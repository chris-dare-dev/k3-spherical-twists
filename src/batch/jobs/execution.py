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

from ..tasks import Limits, RunDeadlineExpired
from .memory import MemoryGuard
from .scratch import tmpfs_capacity
from .watchdog import MIB, JobSpec

# Keep coordinator buffering and on-disk files bounded even for an overly verbose runner.
FILE_BYTES = 16 * MIB
SCRATCH_BYTES = 128 * MIB
COORDINATOR_HEADROOM_MB = 64
WATCHDOG_HEADROOM_MB = 16
WATCHDOG = Path(__file__).with_name("watchdog.py")


@dataclass
class LocalJob:
    process: subprocess.Popen[bytes]
    temporary: tempfile.TemporaryDirectory[str]
    outcome: Path
    scope: str
    slice_name: str | None
    started: float
    scratch_temporary: tempfile.TemporaryDirectory[str] | None = None

    def cleanup(self) -> None:
        try:
            self.temporary.cleanup()
        finally:
            if self.scratch_temporary is not None:
                self.scratch_temporary.cleanup()


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

    def __init__(
        self,
        guard: MemoryGuard,
        memory_mb: int,
        cpu_cores: int,
        *,
        workers: int | None = None,
        run_time_seconds: float | None = None,
        scratch_root: Path | None = None,
        scratch_budget_mb: int | None = None,
    ) -> None:
        self.guard = guard
        self.memory_mb = memory_mb
        self.cpu_cores = cpu_cores
        self.workers = workers if workers is not None else cpu_cores
        self.run_time_seconds = run_time_seconds
        self.deadline: float | None = None
        self.scratch_root = scratch_root
        self.scratch_budget_mb = scratch_budget_mb
        self.scratch_capacity: int | None = None
        self._workspace: tempfile.TemporaryDirectory[str] | None = None
        self.run_tag = f"batch-{uuid4().hex}"
        self.slice_name: str | None = None

    def __enter__(self) -> LocalBackend:
        if self.run_time_seconds is not None:
            if not math.isfinite(self.run_time_seconds) or self.run_time_seconds <= 0:
                raise ValueError("run deadline must be finite and positive")
            self.deadline = time.monotonic() + self.run_time_seconds
        if (self.scratch_root is None) != (self.scratch_budget_mb is None):
            raise ValueError("scratch root and capacity must be configured together")
        try:
            if self.scratch_root is not None and self.scratch_budget_mb is not None:
                root = self.scratch_root.resolve(strict=True)
                self.scratch_capacity = tmpfs_capacity(root)
                if self.scratch_capacity > self.scratch_budget_mb * MIB:
                    raise ValueError("scratch tmpfs is larger than the requested hard capacity")
                self._workspace = tempfile.TemporaryDirectory(prefix="batch-run-", dir=root)
            self.slice_name = self.guard.open_run(self.run_tag, self.memory_mb, self.cpu_cores)
            self.check_deadline()
        except BaseException:
            self.__exit__()
            raise
        return self

    def __exit__(self, *error: object) -> None:
        try:
            if self.slice_name is not None:
                with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                    self.guard.stop(self.slice_name)
                self.slice_name = None
        finally:
            if self._workspace is not None:
                self._workspace.cleanup()
                self._workspace = None
            self.deadline = None

    @property
    def workspace(self) -> Path | None:
        return Path(self._workspace.name) if self._workspace is not None else None

    def check_deadline(self) -> None:
        if self.deadline is not None and time.monotonic() >= self.deadline:
            raise RunDeadlineExpired("run wall deadline reached")

    @property
    def coordinator_headroom_mb(self) -> int:
        return COORDINATOR_HEADROOM_MB + self.workers * WATCHDOG_HEADROOM_MB

    def controls(self) -> dict[str, Any]:
        return {
            "mode": "cgroup-v2" if self.slice_name else "sampled",
            "run_memory_mb": self.memory_mb,
            "run_cpu_cores": self.cpu_cores if self.slice_name else None,
            "coordinator_headroom_mb": self.coordinator_headroom_mb,
            "file_limit_bytes": FILE_BYTES,
            "sampled_scratch_limit_bytes": SCRATCH_BYTES,
            "swap_bytes": 0 if self.slice_name else None,
            "run_time_seconds": self.run_time_seconds,
            "scratch_capacity_bytes": self.scratch_capacity,
        }

    def start(
        self,
        command: list[str],
        limits: Limits,
        log: Path,
        *,
        cwd: Path | None = None,
        watchdog: Path = WATCHDOG,
        stderr: Path | None = None,
        scratch_root: Path | None = None,
    ) -> LocalJob:
        """Launch a watchdog and give only its command custody of job resources."""
        self.check_deadline()
        if sys.platform != "linux":
            raise RuntimeError("the local execution backend requires Linux")
        if not math.isfinite(limits.time_seconds) or limits.time_seconds <= 0:
            raise RuntimeError("a job deadline requires a finite positive time limit")
        tag = f"{self.run_tag}-{uuid4().hex}"
        scope = f"{tag}.scope"
        job_slice = None
        temporary = tempfile.TemporaryDirectory(prefix="batch-job-", dir=scratch_root)
        job_directory = Path(temporary.name)
        outcome = job_directory / "result.json"
        started = time.monotonic()
        job_deadline = started + limits.time_seconds
        deadline = min(job_deadline, self.deadline) if self.deadline is not None else job_deadline
        job_cores = limits.cpu_cores or self.cpu_cores
        if not 1 <= job_cores <= self.cpu_cores:
            temporary.cleanup()
            raise RuntimeError("job CPU request exceeds the configured run budget")
        scratch_temporary = None
        try:
            if self.workspace is not None:
                scratch_temporary = tempfile.TemporaryDirectory(prefix="attempt-", dir=self.workspace)
        except BaseException:
            temporary.cleanup()
            raise
        scratch = Path(scratch_temporary.name) if scratch_temporary is not None else job_directory / "scratch"
        spec: JobSpec = {
            "parent": os.getpid(),
            "started": started,
            "deadline": deadline,
            "deadline_scope": "run" if deadline < job_deadline else "job",
            "workspace": str(self.workspace) if self.workspace is not None else None,
            "memory_bytes": limits.memory_mb * MIB,
            "run_memory_bytes": self.memory_mb * MIB,
            "cpu_cores": job_cores,
            "run_cpu_cores": self.cpu_cores,
            "run_slice": self.slice_name,
            "file_bytes": FILE_BYTES,
            "scratch_bytes": SCRATCH_BYTES,
            "scratch": str(scratch),
            "outcome": str(outcome),
        }
        try:
            scratch.mkdir(exist_ok=scratch_temporary is not None)
            job_slice = self.guard.open_job(tag, self.slice_name, limits.memory_mb, job_cores)
            command, group = self.guard.confine(command, tag, job_slice, self.slice_name, limits.time_seconds)
            if group is not None:
                spec["group"] = str(group)
            launch = [sys.executable, str(watchdog), json.dumps(spec), *command]
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
            if scratch_temporary is not None:
                scratch_temporary.cleanup()
            raise
        return LocalJob(process, temporary, outcome, scope, job_slice, started, scratch_temporary)

    def _release(self, scope: str, job_slice: str | None) -> None:
        if job_slice is not None:
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
                problem = self.guard.launch_failure(data["launch_error"]) if "launch_error" in data else None
                if problem is not None:
                    raise RuntimeError(problem)
                return JobResult(int(data["returncode"]), float(data.get("wall_seconds", wall)), data)
            problem = self.guard.launch_failure(None) if status > 0 else None
            if problem is not None:
                raise RuntimeError(problem)
            # A dead watchdog cannot prove that a cgroup-local limit caused its death.
            return JobResult(status or 125, wall, {})
        finally:
            self._release(job.scope, job.slice_name)
            job.cleanup()

    def cancel(self, job: LocalJob) -> None:
        """Ask a watchdog to stop its tree, then reap its supervisor."""
        try:
            job.process.terminate()
            job.process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            if job.slice_name is not None:
                with contextlib.suppress(OSError, subprocess.TimeoutExpired):
                    self.guard.stop(job.slice_name)
            job.process.kill()
            job.process.wait()
        finally:
            self._release(job.scope, job.slice_name)
            job.cleanup()

    def execute(
        self, command: list[str], timeout: float, *, cwd: Path | None = None, watchdog: Path = WATCHDOG
    ) -> subprocess.CompletedProcess[str]:
        """Execute an expansion with separate, bounded output and error streams."""
        with tempfile.TemporaryDirectory(prefix="batch-plan-", dir=self.workspace) as folder:
            stdout, stderr = (Path(folder) / name for name in ("stdout", "stderr"))
            job = self.start(
                command, Limits(timeout, self.memory_mb), stdout, cwd=cwd, watchdog=watchdog, stderr=stderr
            )
            try:
                while (result := self.observe(job)) is None:
                    time.sleep(0.02)
            except BaseException:
                self.cancel(job)
                raise
            if result.verdict == "timeout":
                if result.data.get("deadline_scope") == "run":
                    raise RunDeadlineExpired("run wall deadline reached during planning")
                raise subprocess.TimeoutExpired(command, timeout)
            errors = read_output(stderr)
            if result.verdict:
                errors += f"\nplanner exceeded its {result.verdict} limit"
            if "launch_error" in result.data:
                errors += f"\n{result.data['launch_error']}"
            return subprocess.CompletedProcess(command, result.returncode, read_output(stdout), errors)
