"""Linux job lifecycle shared by batch expansion and task execution."""

from __future__ import annotations

import contextlib
import json
import math
import os
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from uuid import uuid4

from ._job import MIB
from .memory import CgroupGuard, MemoryGuard
from .model import Limits

# Keep coordinator buffering and on-disk files bounded even for an overly verbose runner.
FILE_BYTES = 16 * MIB
SCRATCH_BYTES = 128 * MIB
COORDINATOR_HEADROOM_MB = 64
WATCHDOG_HEADROOM_MB = 16
WATCHDOG = Path(__file__).with_name("_job.py")


@dataclass
class LocalJob:
    process: subprocess.Popen[bytes]
    temporary: tempfile.TemporaryDirectory[str]
    outcome: Path
    scope: str
    slice_name: str | None
    started: float


@dataclass
class JobResult:
    returncode: int
    wall_seconds: float
    data: dict[str, Any]

    @property
    def verdict(self) -> str | None:
        value: str | None = self.data.get("verdict")
        return value


def read_output(path: Path) -> str:
    with path.open("rb") as handle:
        return handle.read(FILE_BYTES).decode("utf-8", errors="replace")


class LocalBackend:
    """Own the per-run cgroup boundary and independent job watchdogs."""

    def __init__(self, guard: MemoryGuard, memory_mb: int, cpu_cores: int) -> None:
        self.guard = guard
        self.memory_mb = memory_mb
        self.cpu_cores = cpu_cores
        self.run_tag = f"k3batch-{uuid4().hex}"
        self.slice_name: str | None = None

    def __enter__(self) -> LocalBackend:
        if isinstance(self.guard, CgroupGuard):
            self.slice_name = self.guard.open_slice(self.run_tag, self.memory_mb, self.cpu_cores)
        return self

    def __exit__(self, *error: object) -> None:
        if self.slice_name is not None and isinstance(self.guard, CgroupGuard):
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                self.guard.stop(self.slice_name)
            self.slice_name = None

    @property
    def coordinator_headroom_mb(self) -> int:
        return COORDINATOR_HEADROOM_MB + self.cpu_cores * WATCHDOG_HEADROOM_MB

    def controls(self) -> dict[str, Any]:
        return {
            "mode": "cgroup-v2" if self.slice_name else "sampled",
            "run_memory_mb": self.memory_mb,
            "run_cpu_cores": self.cpu_cores if self.slice_name else None,
            "coordinator_headroom_mb": self.coordinator_headroom_mb,
            "file_limit_bytes": FILE_BYTES,
            "sampled_scratch_limit_bytes": SCRATCH_BYTES,
            "swap_bytes": 0 if self.slice_name else None,
        }

    def start(
        self,
        command: list[str],
        limits: Limits,
        log: Path,
        *,
        cwd: Path | None = None,
        stderr: Path | None = None,
        scratch_root: Path | None = None,
    ) -> LocalJob:
        """Launch a watchdog and give only its command custody of job resources."""
        if sys.platform != "linux":
            raise RuntimeError("the local execution backend requires Linux")
        if not math.isfinite(limits.time_seconds) or limits.time_seconds <= 0:
            raise RuntimeError("a job deadline requires a finite positive time limit")
        tag = f"{self.run_tag}-{uuid4().hex}"
        scope = f"{tag}.scope"
        job_slice = None
        temporary = tempfile.TemporaryDirectory(prefix="k3batch-job-", dir=scratch_root)
        job_directory = Path(temporary.name)
        scratch = job_directory / "scratch"
        outcome = job_directory / "result.json"
        started = time.monotonic()
        deadline = started + limits.time_seconds
        spec = {
            "parent": os.getpid(),
            "started": started,
            "deadline": deadline,
            "memory_bytes": limits.memory_mb * MIB,
            "run_memory_bytes": self.memory_mb * MIB,
            "cpu_cores": self.cpu_cores,
            "run_slice": self.slice_name,
            "file_bytes": FILE_BYTES,
            "scratch_bytes": SCRATCH_BYTES,
            "scratch": str(scratch),
            "outcome": str(outcome),
        }
        try:
            scratch.mkdir()
            if isinstance(self.guard, CgroupGuard):
                if self.slice_name is None:
                    raise RuntimeError("no cgroup run boundary is active")
                job_slice = self.guard.open_slice(tag, limits.memory_mb, self.cpu_cores)
                group = self.guard.group_path(job_slice)
                if group.parent.name != self.slice_name:
                    raise RuntimeError("the job slice is outside the configured run boundary")
                spec["group"] = str(group)
                command = self.guard.wrap(command, tag, job_slice, limits.time_seconds)
            launch = [sys.executable, str(WATCHDOG), json.dumps(spec), *command]
            with contextlib.ExitStack() as stack:
                output = stack.enter_context(log.open("xb"))
                errors = subprocess.STDOUT if stderr is None else stack.enter_context(stderr.open("xb"))
                process = subprocess.Popen(
                    launch, stdin=subprocess.DEVNULL, stdout=output, stderr=errors,
                    cwd=cwd, start_new_session=True,
                )  # fmt: skip
        except BaseException:
            self._release(scope, job_slice)
            temporary.cleanup()
            raise
        return LocalJob(process, temporary, outcome, scope, job_slice, started)

    def _release(self, scope: str, job_slice: str | None) -> None:
        if job_slice is not None and isinstance(self.guard, CgroupGuard):
            with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                self.guard.stop(job_slice, wait=False)
                self.guard.release(scope)

    def observe(self, job: LocalJob) -> JobResult | None:
        """Collect terminal state without delaying other running commands' limits."""
        status = job.process.poll()
        if status is None:
            return None
        wall = time.monotonic() - job.started
        try:
            if job.outcome.is_file():
                data: dict[str, Any] = json.loads(job.outcome.read_text(encoding="utf-8"))
                if "launch_error" in data and isinstance(self.guard, CgroupGuard):
                    raise RuntimeError(
                        f"cannot run the job under enforced cgroup limits: {data['launch_error']}"
                    )
                return JobResult(int(data["returncode"]), float(data.get("wall_seconds", wall)), data)
            if isinstance(self.guard, CgroupGuard) and status > 0:
                raise RuntimeError("systemd could not launch the scoped job; see the job log")
            # A dead watchdog cannot prove that a cgroup-local limit caused its death.
            return JobResult(status or 125, wall, {})
        finally:
            self._release(job.scope, job.slice_name)
            job.temporary.cleanup()

    def cancel(self, job: LocalJob) -> None:
        """Ask a watchdog to stop its tree, then reap its supervisor."""
        try:
            job.process.terminate()
            job.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            if isinstance(self.guard, CgroupGuard):
                with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                    if job.slice_name is not None:
                        self.guard.stop(job.slice_name)
            job.process.kill()
            job.process.wait()
        finally:
            self._release(job.scope, job.slice_name)
            job.temporary.cleanup()

    def execute(self, command: list[str], timeout: float) -> subprocess.CompletedProcess[str]:
        """Execute an expansion with separate, bounded output and error streams."""
        with tempfile.TemporaryDirectory(prefix="k3batch-plan-") as folder:
            stdout, stderr = (Path(folder) / name for name in ("stdout", "stderr"))
            job = self.start(command, Limits(timeout, self.memory_mb), stdout, stderr=stderr)
            try:
                while (result := self.observe(job)) is None:
                    time.sleep(0.02)
            except BaseException:
                self.cancel(job)
                raise
            if result.verdict == "timeout":
                raise subprocess.TimeoutExpired(command, timeout)
            errors = read_output(stderr)
            if result.verdict:
                errors += f"\nplanner exceeded its {result.verdict} limit"
            if "launch_error" in result.data:
                errors += f"\n{result.data['launch_error']}"
            return subprocess.CompletedProcess(command, result.returncode, read_output(stdout), errors)
