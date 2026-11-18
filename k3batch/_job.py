"""Watch one local command independently of the batch coordinator."""

from __future__ import annotations

import contextlib
import ctypes
import json
import os
import resource
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

MIB = 1024**2
PR_SET_PDEATHSIG = 1
PR_SET_CHILD_SUBREAPER = 36


def kernel_value(group: Path, key: str) -> str:
    return (group / key).read_text().strip()


def counters(group: Path, key: str) -> dict[str, int]:
    return {
        name: int(value) for name, value in (row.split() for row in kernel_value(group, key).splitlines())
    }


def scope_controls(group: Path) -> dict[str, Any]:
    quota, period = kernel_value(group, "cpu.max").split()
    memory = kernel_value(group, "memory.max")
    swap = kernel_value(group, "memory.swap.max")
    if "max" in {quota, memory, swap}:
        raise RuntimeError(f"memory, swap and CPU controllers must enforce finite limits in {group}")
    return {
        "memory_bytes": int(memory),
        "swap_bytes": int(swap),
        "cpu_cores": int(quota) / int(period),
    }


def rss_tree(pid: int) -> int:
    """Read one approximate RSS sample for the process and its descendants."""
    pending = [pid]
    seen = set()
    resident = 0
    while pending:
        process = pending.pop()
        if process in seen:
            continue
        seen.add(process)
        info = Path("/proc") / str(process)
        with contextlib.suppress(OSError, ValueError, IndexError):
            resident += int((info / "statm").read_text().split()[1]) * os.sysconf("SC_PAGE_SIZE")
        for children in (info / "task").glob("*/children"):
            with contextlib.suppress(OSError, ValueError):
                pending.extend(int(child) for child in children.read_text().split())
    return resident


def scratch_size(directory: Path, limit: int) -> int:
    """Count scratch entries and allocated blocks without following symlinks."""
    total = 0
    pending = [directory]
    while pending:
        with contextlib.suppress(FileNotFoundError), os.scandir(pending.pop()) as entries:
            for entry in entries:
                with contextlib.suppress(FileNotFoundError):
                    attributes = entry.stat(follow_symlinks=False)
                    total += 4096 + attributes.st_blocks * 512
                    if total > limit:
                        return total
                    if entry.is_dir(follow_symlinks=False):
                        pending.append(Path(entry.path))
    return total


def kill_group(pid: int, group: Path | None) -> None:
    if group is not None:
        with contextlib.suppress(OSError):
            (group / "cgroup.kill").write_text("1")
    with contextlib.suppress(ProcessLookupError):
        os.killpg(pid, signal.SIGKILL)


def reap_children() -> None:
    # When a parent exits, this subreaper adopts ordinary descendants before cleaning up.
    children = Path(f"/proc/self/task/{os.getpid()}/children")
    deadline = time.monotonic() + 1
    while time.monotonic() < deadline:
        for child in children.read_text().split():
            with contextlib.suppress(ProcessLookupError):
                os.kill(int(child), signal.SIGKILL)
        try:
            pid, _ = os.waitpid(-1, os.WNOHANG)
        except ChildProcessError:
            return
        if not pid:
            time.sleep(0.01)


def child_exited(pid: int) -> bool:
    if sys.platform == "linux":
        return os.waitid(os.P_PID, pid, os.WEXITED | os.WNOHANG | os.WNOWAIT) is not None
    raise RuntimeError("the job watchdog requires Linux")


def watch(spec: dict[str, Any], command: list[str]) -> dict[str, Any]:
    libc = ctypes.CDLL(None, use_errno=True)
    cancelled = False

    def cancel(signum: int, frame: object) -> None:
        nonlocal cancelled
        cancelled = True

    signal.signal(signal.SIGTERM, cancel)
    signal.pthread_sigmask(signal.SIG_UNBLOCK, {signal.SIGINT, signal.SIGTERM})
    if libc.prctl(PR_SET_PDEATHSIG, signal.SIGTERM) or libc.prctl(PR_SET_CHILD_SUBREAPER, 1):
        raise OSError(ctypes.get_errno(), "cannot configure the job watchdog")
    if os.getppid() != spec["parent"]:
        return {"returncode": -signal.SIGTERM, "verdict": "cancelled"}

    group = None
    effective = None
    run = None
    initial_run_oom = 0
    if "group" in spec:
        group = Path(spec["group"])
        effective = scope_controls(group)
        run = scope_controls(group.parent)
        if (
            effective["memory_bytes"] > spec["memory_bytes"]
            or effective["swap_bytes"] != 0
            or effective["cpu_cores"] > spec["cpu_cores"]
            or run["memory_bytes"] > spec["run_memory_bytes"]
            or run["swap_bytes"] != 0
            or run["cpu_cores"] > spec.get("run_cpu_cores", spec["cpu_cores"])
        ):
            raise RuntimeError("systemd did not enforce the requested cgroup limits")
        initial_run_oom = counters(group.parent, "memory.events.local").get("oom", 0)

    # Set the cap for this command and all inherited regular-file descriptors.
    file_limit = spec["file_bytes"]
    resource.setrlimit(resource.RLIMIT_FSIZE, (file_limit, file_limit))
    scratch = Path(spec["scratch"])
    env = os.environ | {"TMPDIR": str(scratch), "TMP": str(scratch), "TEMP": str(scratch)}
    deadline = spec["deadline"]
    if time.monotonic() >= deadline:
        return {"returncode": -signal.SIGKILL, "verdict": "timeout", "effective": effective}

    if cancelled:
        return {"returncode": -signal.SIGTERM, "verdict": "cancelled"}
    process = subprocess.Popen(command, stdin=subprocess.DEVNULL, env=env, start_new_session=True)
    verdict = None
    peak_sample = 0
    try:
        while not child_exited(process.pid):
            if group is None:
                peak_sample = max(peak_sample, rss_tree(process.pid))
            if time.monotonic() >= deadline:
                verdict = "timeout"
            elif cancelled:
                verdict = "cancelled"
            elif peak_sample > spec["memory_bytes"]:
                verdict = "memory"
            elif scratch_size(scratch, spec["scratch_bytes"]) > spec["scratch_bytes"]:
                verdict = "scratch"
            if verdict is not None:
                break
            time.sleep(0.02)
    finally:
        # Hold the child PID until after its tree is stopped, then read the leader's resource usage.
        signal.signal(signal.SIGTERM, signal.SIG_IGN)
        kill_group(process.pid, group)
        _, status, usage = os.wait4(process.pid, 0)
        process.returncode = os.waitstatus_to_exitcode(status)
        elapsed = time.monotonic() - spec["started"]
        reap_children()

    events = None
    peak_bytes = None
    if group is not None:
        events = counters(group, "memory.events")
        peak_bytes = int(kernel_value(group, "memory.peak"))
        run_oom = counters(group.parent, "memory.events.local").get("oom", 0) > initial_run_oom
        if verdict is None and (events.get("oom", 0) or run_oom) and events.get("oom_kill", 0):
            verdict = "memory"
    if process.returncode == -signal.SIGXFSZ:
        verdict = "file"

    return {
        "returncode": process.returncode,
        "wall_seconds": elapsed,
        "verdict": verdict,
        "cpu_seconds": usage.ru_utime + usage.ru_stime,
        "peak_rss_mb": usage.ru_maxrss / 1024,
        "peak_sampled_bytes": peak_sample if group is None else None,
        "cgroup_memory_peak_bytes": peak_bytes,
        "cgroup_memory_events": events,
        "effective": effective,
        "effective_run": run,
    }


def main() -> int:
    spec = json.loads(sys.argv[1])
    path = Path(spec["outcome"])
    try:
        result = watch(spec, sys.argv[2:])
        if result.get("verdict") == "timeout":
            result["deadline_scope"] = spec.get("deadline_scope", "job")
    except (OSError, RuntimeError, ValueError) as error:
        result = {"returncode": 125, "launch_error": str(error)}
    if os.getppid() != spec["parent"]:
        # An empty transient slice can otherwise remain loaded after the coordinator dies.
        if spec["run_slice"] is not None:
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                subprocess.run(
                    ["systemctl", "--user", "--no-block", "stop", spec["run_slice"]],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                    timeout=1,
                    check=False,
                )
        if spec.get("workspace"):
            shutil.rmtree(spec["workspace"], ignore_errors=True)
        shutil.rmtree(path.parent, ignore_errors=True)
        return 0
    path.write_text(json.dumps(result), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
