"""Local resource policy for the Linux job backend."""

from __future__ import annotations

import contextlib
import os
import shutil
import subprocess
from pathlib import Path
from uuid import uuid4


class MemoryGuard:
    """How a run and its jobs are held to their limits; the policy the planner and the tasks share.

    This one has nothing enforced from outside: the watchdog of each job samples its memory. A guard
    that does opens a boundary around the run and one inside it for each job, and names them.
    """

    name = "none"

    def open_run(self, tag: str, memory_mb: int, cpus: int) -> str | None:
        """Open the boundary of a run; None when the guard keeps none."""
        return None

    def open_job(self, tag: str, run: str | None, memory_mb: int, cpus: int) -> str | None:
        """Open the boundary of one job inside that of its run; None when the guard keeps none."""
        return None

    def confine(
        self, command: list[str], tag: str, job: str | None, run: str | None, time_seconds: float
    ) -> tuple[list[str], Path | None]:
        """The command that starts inside the job's boundary, and where the kernel accounts for it."""
        return command, None

    def launch_failure(self, error: str | None) -> str | None:
        """Why a job that could not be launched (with the watchdog's reason, if it gave one) stops the run.

        None when the failure is the job's own: it is then recorded like any other outcome.
        """
        return None

    def stop(self, unit: str, *, wait: bool = True) -> None:
        """Close a boundary and end what runs inside it."""

    def release(self, unit: str) -> None:
        """Forget the unit a job ran in."""


class PollingGuard(MemoryGuard):
    """Best-effort memory sampling for installations without a user cgroup manager."""

    name = "poll"


class CgroupGuard(MemoryGuard):
    """Hard memory, swap and CPU limits through transient systemd user units."""

    name = "cgroup"

    @staticmethod
    def available() -> bool:
        if not all(shutil.which(command) for command in ("systemd-run", "systemctl", "busctl")):
            return False
        if not Path("/sys/fs/cgroup/cgroup.controllers").is_file():
            return False
        group = CgroupGuard()
        tag = f"batch-probe-{uuid4().hex}"
        try:
            unit = group.open_slice(tag, 64, 1)
        except (OSError, RuntimeError):
            return False
        try:
            path = group.group_path(unit)
            if (
                (path / "memory.max").read_text().strip() != "67108864"
                or (path / "memory.swap.max").read_text().strip() != "0"
                or (path / "cpu.max").read_text().strip() != "100000 100000"
                or not os.access(path / "cgroup.kill", os.W_OK)
                or not os.access(path / "memory.peak", os.R_OK)
            ):
                return False
            group._systemd(group.wrap(["/bin/true"], tag, unit, 3))
            return True
        except (OSError, RuntimeError):
            return False
        finally:
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                group.stop(unit)

    def open_run(self, tag: str, memory_mb: int, cpus: int) -> str:
        return self.open_slice(tag, memory_mb, cpus)

    def open_job(self, tag: str, run: str | None, memory_mb: int, cpus: int) -> str:
        if run is None:
            raise RuntimeError("no cgroup run boundary is active")
        return self.open_slice(tag, memory_mb, cpus)

    def confine(
        self, command: list[str], tag: str, job: str | None, run: str | None, time_seconds: float
    ) -> tuple[list[str], Path]:
        assert job is not None
        group = self.group_path(job)
        if group.parent.name != run:
            raise RuntimeError("the job slice is outside the configured run boundary")
        return self.wrap(command, tag, job, time_seconds), group

    def launch_failure(self, error: str | None) -> str:
        if error is None:
            return "systemd could not launch the scoped job; see the job log"
        return f"cannot run the job under enforced cgroup limits: {error}"

    def open_slice(self, tag: str, budget_mb: int, cpus: int) -> str:
        unit = f"{tag}.slice"
        self._systemd(
            [
                "busctl", "--user", "call", "org.freedesktop.systemd1", "/org/freedesktop/systemd1",
                "org.freedesktop.systemd1.Manager", "StartTransientUnit", "ssa(sv)a(sa(sv))",
                unit, "fail", "4", "MemoryMax", "t", str(budget_mb * 1024**2),
                "MemorySwapMax", "t", "0", "CPUQuotaPerSecUSec", "t", str(cpus * 1_000_000),
                # Slices need to remain active between jobs. The backend stops the slice on exit.
                "MemoryAccounting", "b", "true", "0",
            ]
        )  # fmt: skip
        return unit

    def group_path(self, unit: str) -> Path:
        group = self._systemd(
            ["systemctl", "--user", "show", unit, "--property=ControlGroup", "--value"]
        ).strip()
        if not group.startswith("/") or Path(group).name != unit:
            raise RuntimeError(f"the cgroup for {unit} is unavailable")
        return Path("/sys/fs/cgroup") / group.lstrip("/")

    def wrap(self, command: list[str], tag: str, slice_name: str, time_seconds: float) -> list[str]:
        # The slice keeps job counters readable after the command exits. A scope runtime limit
        # gives systemd an independent deadline if the watchdog stops responding.
        return [
            "systemd-run", "--user", "--scope", "--quiet", f"--slice={slice_name}", f"--unit={tag}",
            "-p", f"RuntimeMaxSec={time_seconds + 1:.6f}s", "-p", "TimeoutStopSec=1s",
            "-p", "OOMPolicy=continue", "--", *command,
        ]  # fmt: skip

    def stop(self, unit: str, *, wait: bool = True) -> None:
        command = ["systemctl", "--user", "stop", unit]
        if not wait:
            command.insert(2, "--no-block")
        subprocess.run(command, capture_output=True, timeout=5 if wait else 0.2, check=False)

    def release(self, unit: str) -> None:
        # A failed scope can stay loaded. A timed-out manager inquiry must not delay other jobs.
        with subprocess.Popen(
            ["systemctl", "--user", "reset-failed", unit],
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        ) as child:
            try:
                child.wait(timeout=0.2)
            except subprocess.TimeoutExpired:
                child.kill()

    @staticmethod
    def _systemd(command: list[str]) -> str:
        try:
            result = subprocess.run(command, capture_output=True, text=True, timeout=5, check=False)
        except subprocess.TimeoutExpired as problem:
            raise RuntimeError(
                "the systemd user manager did not respond while setting cgroup limits"
            ) from problem
        if result.returncode:
            message = result.stderr.strip() or f"exit status {result.returncode}"
            raise RuntimeError(f"cannot enforce cgroup limits with the systemd user manager: {message}")
        return result.stdout


def available_mb() -> int | None:
    """Memory the kernel estimates can be used without swapping, in mebibytes."""
    try:
        for line in Path("/proc/meminfo").read_text().splitlines():
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) // 1024
    except (OSError, ValueError, IndexError):
        pass
    return None


def choose_guard(name: str) -> MemoryGuard:
    if name == "poll":
        return PollingGuard()
    if name in {"auto", "cgroup"}:
        if CgroupGuard.available():
            return CgroupGuard()
        if name == "auto":
            return PollingGuard()
        raise RuntimeError(
            "enforced limits need delegated cgroup v2 controllers and a systemd user manager; "
            "use --memory-guard poll for sampled enforcement"
        )
    raise ValueError(f"unknown memory guard {name!r}")
