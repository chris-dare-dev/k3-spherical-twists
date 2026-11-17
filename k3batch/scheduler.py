"""Runs the tasks of a batch: one process per task, several at a time, within a memory budget.

A task process is never trusted to stop itself.  The scheduler measures its wall time and kills it at
the time limit; the memory guard stops it at the memory limit.  Whatever happens to one process, the
scheduler writes exactly one record for its task and carries on with the others.
"""

from __future__ import annotations

import contextlib
import ctypes
import hashlib
import os
import re
import signal
import subprocess
import time
from collections import Counter
from collections.abc import Callable, Collection, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from uuid import uuid4

from .config import BatchConfig, ConfigError
from .identity import RECORD_SCHEMA, implementation_fingerprint, recheck, task_identities
from .memory import MemoryGuard
from .model import RUNNER_STATUSES, Limits, Status, Task
from .runner import REPOSITORY, RunnerError, RunnerInvocation, error_lines
from .store import ResultStore

_PR_SET_PDEATHSIG = 1
_libc = ctypes.CDLL(None, use_errno=True)


def _die_with_scheduler() -> None:
    # runs in the task process before the command starts: the kernel kills the process if the scheduler
    # goes away, so no computation outlives the program that enforces its limits
    _libc.prctl(_PR_SET_PDEATHSIG, signal.SIGKILL)


@dataclass(frozen=True)
class PlannedTask:
    task: Task
    limits: Limits
    computation_id: str
    check_id: str
    record_id: str
    reused: bool
    check: dict[str, Any]

    def manifest_entry(self) -> dict[str, Any]:
        return self.task.payload | {
            "limits": self.limits.as_dict(),
            "computation_id": self.computation_id,
            "check_id": self.check_id,
            "record_id": self.record_id,
            "check": self.check,
        }


@dataclass
class _Running:
    task: Task
    limits: Limits
    process: subprocess.Popen[bytes]
    tag: str
    log: Path
    invocation: RunnerInvocation
    attempt_id: str
    started: float
    started_at: str
    verdict: Status | None = None  # set when the scheduler kills the process


Progress = Callable[[dict[str, Any], int, int], None]


class Scheduler:
    def __init__(
        self,
        *,
        config: BatchConfig,
        tasks: Sequence[Task],
        store: ResultStore,
        run_dir: Path,
        runner: tuple[str, ...],
        guard: MemoryGuard,
        stamp: dict[str, Any] | None = None,
        retry: Collection[str] = (),
        progress: Progress | None = None,
        tick: float = 0.02,
    ) -> None:
        self.config = config
        self.tasks = list(tasks)
        self.store = store
        self.run_dir = run_dir
        self.runner = runner
        self.guard = guard
        self.stamp = stamp or {}
        self.retry = frozenset(retry)
        self.progress = progress
        self.tick = tick
        self._started = 0
        self._active_plan: dict[str, PlannedTask] = {}

    def plan(self) -> list[PlannedTask]:
        """Select existing attempts and reserve identifiers for work this run will start."""
        implementation = implementation_fingerprint(self.runner, self.stamp.get("runner", {}))
        latest = {
            record["computation_id"]: record
            for record in self.store.records()
            if record.get("schema_version") == RECORD_SCHEMA
            and isinstance(record.get("computation_id"), str)
            and isinstance(record.get("check_id"), str)
            and isinstance(record.get("record_id"), str)
        }
        plan = []
        for task in self.tasks:
            limits = self.config.limits_for(task)
            computation_id, check_id = task_identities(task, implementation)
            previous = latest.get(computation_id)
            check = recheck(task, previous, check_id) if previous is not None else {}
            reused = previous is not None and self._can_reuse(previous, limits, check)
            if not reused and limits.memory_mb > self.config.memory_budget_mb:
                raise ConfigError(
                    f"task {task.id} has a memory limit of {limits.memory_mb} MB, "
                    f"above the budget of {self.config.memory_budget_mb} MB"
                )
            plan.append(
                PlannedTask(
                    task,
                    limits,
                    computation_id,
                    check_id,
                    previous["record_id"] if reused and previous is not None else uuid4().hex,
                    reused,
                    check if reused else {},
                )
            )
        return plan

    def _can_reuse(self, record: dict[str, Any], limits: Limits, check: dict[str, Any]) -> bool:
        status = check.get("status", record["status"])
        if status in self.retry:
            return False
        previous_limits = record.get("limits", {})
        if status == Status.TIMEOUT and limits.time_seconds > previous_limits.get("time_seconds", 0):
            return False
        return not (status == Status.MEMORY and limits.memory_mb > previous_limits.get("memory_mb", 0))

    def pending(self, plan: Sequence[PlannedTask] | None = None) -> list[tuple[Task, Limits]]:
        """Unfulfilled work in cost order, preserving batch order at tied costs."""
        members = self.plan() if plan is None else plan
        todo = [(entry.task, entry.limits) for entry in members if not entry.reused]
        return sorted(todo, key=lambda entry: entry[0].cost)

    def run(self, plan: Sequence[PlannedTask] | None = None) -> Counter[str]:
        """Execute a plan and return how many new attempts ended with each status."""
        members = self.plan() if plan is None else plan
        self._active_plan = {entry.task.id: entry for entry in members}
        pending = self.pending(members)
        total = len(pending)
        outcome: Counter[str] = Counter()
        running: list[_Running] = []
        (self.run_dir / "logs").mkdir(parents=True, exist_ok=True)
        # a terminated scheduler stops its task processes the same way an interrupted one does
        previous = signal.signal(signal.SIGTERM, _raise_interrupt)
        try:
            while pending or running:
                self._admit(pending, running)
                finished = self._collect(running)
                for record in finished:
                    self.store.append(record)
                    outcome[record["status"]] += 1
                    if self.progress is not None:
                        self.progress(record, outcome.total(), total)
                if not finished and running:
                    time.sleep(self.tick)
        finally:
            # an interrupted run leaves no record for the tasks in flight, so a rerun computes them
            for entry in running:
                try:
                    self._kill(entry)
                    self.guard.release(entry.tag)
                finally:
                    entry.invocation.cleanup()
            signal.signal(signal.SIGTERM, previous)
        return outcome

    # starting --------------------------------------------------------------------------------------

    def _admit(self, pending: list[tuple[Task, Limits]], running: list[_Running]) -> None:
        """Starts tasks, cheapest first, while a worker is free and the memory limits fit the budget."""
        while len(running) < self.config.workers:
            committed = sum(entry.limits.memory_mb for entry in running)
            room = self.config.memory_budget_mb - committed
            fits = next((i for i, (_, limits) in enumerate(pending) if limits.memory_mb <= room), None)
            if fits is None:
                return
            running.append(self._start(*pending.pop(fits)))

    def _start(self, task: Task, limits: Limits) -> _Running:
        self._started += 1
        tag = f"k3batch-{os.getpid()}-{self._started}"
        attempt_id = uuid4().hex
        log = self.run_dir / "logs" / f"{_slug(task.id)}-{attempt_id}.log"
        invocation = RunnerInvocation.prepare(self.runner, "run", task.payload, self.run_dir / "requests")
        try:
            command = self.guard.wrap(invocation.command, limits.memory_mb, tag)
            with log.open("xb") as output:
                process = subprocess.Popen(
                    command,
                    stdin=subprocess.DEVNULL,
                    stdout=output,
                    stderr=subprocess.STDOUT,
                    cwd=REPOSITORY,
                    start_new_session=True,
                    preexec_fn=_die_with_scheduler,
                )
        except BaseException:
            invocation.cleanup()
            raise
        return _Running(
            task=task,
            limits=limits,
            process=process,
            tag=tag,
            log=log,
            invocation=invocation,
            attempt_id=attempt_id,
            started=time.monotonic(),
            started_at=datetime.now(UTC).isoformat(timespec="seconds"),
        )

    # ending ----------------------------------------------------------------------------------------

    def _collect(self, running: list[_Running]) -> list[dict[str, Any]]:
        """Records for the processes that ended or had to be stopped; removes them from `running`."""
        records = []
        for entry in list(running):
            pid, status, usage = os.wait4(entry.process.pid, os.WNOHANG)
            if pid == 0:
                if time.monotonic() - entry.started > entry.limits.time_seconds:
                    entry.verdict = Status.TIMEOUT
                elif self.guard.over_limit(entry.process.pid, entry.limits.memory_mb):
                    entry.verdict = Status.MEMORY
                else:
                    continue
                status, usage = self._kill(entry)
            wall = time.monotonic() - entry.started
            entry.process.returncode = os.waitstatus_to_exitcode(status)
            running.remove(entry)
            try:
                records.append(self._record(entry, entry.process.returncode, usage, wall))
            finally:
                entry.invocation.cleanup()
        return records

    @staticmethod
    def _kill(entry: _Running) -> tuple[int, Any]:
        with contextlib.suppress(ProcessLookupError):
            os.killpg(entry.process.pid, signal.SIGKILL)
        _, status, usage = os.wait4(entry.process.pid, 0)
        entry.process.returncode = os.waitstatus_to_exitcode(status)
        return status, usage

    def _record(self, entry: _Running, exit_code: int, usage: Any, wall: float) -> dict[str, Any]:
        output = entry.log.read_text(encoding="utf-8", errors="replace")
        result = None
        error = None
        if entry.verdict is None and exit_code >= 0:
            try:
                result = entry.invocation.task_result(output, exit_code)
            except RunnerError as problem:
                diagnostics = error_lines(output)
                error = f"{problem}\n{diagnostics}" if diagnostics else str(problem)
        if entry.verdict is not None:
            status = entry.verdict
            result = None
        elif result is not None and result.get("status") in RUNNER_STATUSES:
            status = Status(result["status"])
        elif exit_code == -signal.SIGKILL and self.guard.killed_for_memory(entry.tag):
            status = Status.MEMORY
        elif error is not None:
            status = Status.ERROR
        elif exit_code > 0:
            status = Status.ERROR
            error = error_lines(output) or f"exit status {exit_code}"
        else:
            status = Status.CRASHED
            error = (
                f"ended by signal {signal.Signals(-exit_code).name}"
                if exit_code < 0
                else "ended without a result"
            )
        if exit_code != 0:
            self.guard.release(entry.tag)

        result = result or {}
        keep_log = status not in RUNNER_STATUSES
        if not keep_log:
            entry.log.unlink(missing_ok=True)
        record = {
            "task_id": entry.task.id,
            "attempt_id": entry.attempt_id,
            "task": entry.task.payload,
            "status": str(status),
            "value": result.get("value"),
            "predicted": result.get("predicted", entry.task.payload.get("predicted")),
            "agrees": result.get("agrees"),
            "detail": {
                key: value
                for key, value in result.items()
                if key not in {"status", "value", "predicted", "agrees"}
            },
            "error": error,
            "wall_seconds": round(wall, 3),
            "cpu_seconds": round(usage.ru_utime + usage.ru_stime, 3),
            "peak_rss_mb": round(usage.ru_maxrss / 1024, 1),
            "limits": entry.limits.as_dict(),
            "memory_guard": self.guard.name,
            "exit_code": exit_code if exit_code >= 0 else None,
            "exit_signal": signal.Signals(-exit_code).name if exit_code < 0 else None,
            "started_at": entry.started_at,
            "log": str(entry.log.relative_to(self.run_dir)) if keep_log else None,
        }
        planned = self._active_plan[entry.task.id]
        return (
            record
            | self.stamp
            | {
                "schema_version": RECORD_SCHEMA,
                "computation_id": planned.computation_id,
                "check_id": planned.check_id,
                "record_id": planned.record_id,
            }
        )


def _raise_interrupt(signum: int, frame: object) -> None:
    raise KeyboardInterrupt


def _slug(task_id: str) -> str:
    """A file name for a task id: readable, and unique through a hash of the id."""
    readable = re.sub(r"[^A-Za-z0-9._-]+", "_", task_id).strip("_")[:80]
    return f"{readable}-{hashlib.sha1(task_id.encode()).hexdigest()[:8]}"
