"""Runs the tasks of a batch: one process per task, several at a time, within a memory budget.

The execution backend owns each job tree. The scheduler handles admission, identities and results.
"""

from __future__ import annotations

import hashlib
import re
import signal
import time
from collections import Counter
from collections.abc import Callable, Collection, Sequence
from dataclasses import dataclass
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from uuid import uuid4

from .artifacts import ArtifactError, ArtifactStore, model_digest
from .config import BatchConfig, ConfigError
from .execution import WATCHDOG, JobResult, LocalBackend, LocalJob, read_output
from .graph import Graph
from .identity import implementation_fingerprint
from .memory import MemoryGuard
from .model import RUNNER_STATUSES, Limits, Status, Task
from .planning import PlannedTask, Planner
from .record import Record
from .record import build as build_record
from .runner import REPOSITORY, RunnerError, RunnerInvocation, error_lines
from .source import SourceSnapshot
from .store import RunHistory


@dataclass
class _Running:
    task: Task
    limits: Limits
    job: LocalJob
    invocation: RunnerInvocation
    log: Path
    attempt_id: str
    started_at: str
    inputs: dict[str, Any]
    trial_id: str


Progress = Callable[[Record, int, int], None]


class Scheduler:
    def __init__(
        self,
        *,
        config: BatchConfig,
        tasks: Sequence[Task],
        store: RunHistory,
        run_dir: Path,
        runner: tuple[str, ...],
        guard: MemoryGuard,
        backend: LocalBackend | None = None,
        source: SourceSnapshot | None = None,
        stamp: dict[str, Any] | None = None,
        retry: Collection[str] = (),
        progress: Progress | None = None,
        tick: float = 0.02,
    ) -> None:
        self.config = config
        self.tasks = list(tasks)
        self.store = store
        self.graph = Graph.build(self.tasks, config.graph)
        if self.graph.nodes and not store.supports_graphs:
            raise ConfigError("a dependency graph requires a SQLite result store")
        self.artifacts = (
            ArtifactStore(store.path.with_suffix(store.path.suffix + ".artifacts"))
            if self.graph.nodes
            else None
        )
        self.run_dir = run_dir
        self.runner = runner
        self.source = source
        self.guard = guard
        self.backend = backend or LocalBackend(
            guard,
            config.memory_budget_mb,
            config.run_cores,
            workers=config.workers,
            run_time_seconds=config.run_time_seconds,
            scratch_root=config.scratch_root,
            scratch_budget_mb=config.scratch_budget_mb,
        )
        self._own_backend = backend is None
        self.stamp = stamp or {}
        self.retry = frozenset(retry)
        self.progress = progress
        self.tick = tick
        self.planner = Planner(
            config=config,
            graph=self.graph,
            history=store,
            guard=guard.name,
            cpu_cores=self.backend.cpu_cores,
            retry=self.retry,
            usable=self._valid_outputs,
        )
        self._active_plan: dict[str, PlannedTask] = {}

    def plan(self) -> list[PlannedTask]:
        """Select existing attempts and reserve identifiers for work this run will start."""
        implementation = implementation_fingerprint(
            self.runner, self.stamp.get("runner", {}), files=self.source.files if self.source else None
        )
        return self.planner.plan(self.tasks, implementation)

    def _valid_outputs(self, task_id: str, record: Record) -> bool:
        node = self.graph.nodes.get(task_id)
        if node is None or not node.outputs:
            return True
        try:
            for name, kind in node.outputs.items():
                self._read_output(record, name, kind)
        except (ArtifactError, OSError):
            return False
        return True

    def _read_output(self, record: Record, name: str, kind: str) -> dict[str, Any]:
        assert self.artifacts is not None
        reference = record.get("detail", {}).get("artifact_outputs", {}).get(name)
        return self.artifacts.output(reference, name, kind)

    def pending(self, plan: Sequence[PlannedTask] | None = None) -> list[tuple[Task, Limits]]:
        """Unfulfilled work in cost order, preserving batch order at tied costs."""
        members = self.plan() if plan is None else plan
        todo = [(entry.task, entry.limits) for entry in members if not entry.reused]
        return sorted(todo, key=lambda entry: entry[0].cost)

    def run(self, plan: Sequence[PlannedTask] | None = None) -> Counter[str]:
        """Execute a plan and return how many new attempts ended with each status."""
        if self._own_backend:
            with self.backend:
                return self._run(plan)
        return self._run(plan)

    def _run(self, plan: Sequence[PlannedTask] | None) -> Counter[str]:
        members = self.plan() if plan is None else plan
        self._active_plan = {entry.task.id: entry for entry in members}
        pending = self.pending(members)
        self.planner.begin()
        total = len(pending)
        outcome: Counter[str] = Counter()
        wanted = [entry for entry in members if entry.reused]
        settled: dict[str, Record] = {}
        if self.graph.nodes:
            records = self.store.by_record_id([entry.record_id for entry in wanted])
            settled = {entry.task.id: records[entry.record_id] for entry in wanted}
        running: list[_Running] = []
        (self.run_dir / "logs").mkdir(parents=True, exist_ok=True)
        # a terminated scheduler stops its task processes the same way an interrupted one does
        previous = signal.signal(signal.SIGTERM, _raise_interrupt)
        try:
            while pending or running:
                self.backend.check_deadline()
                blocked = self._admit(pending, running, settled)
                finished = blocked + self._collect(running)
                for record in finished:
                    if record.get("deadline_scope") == "run":
                        continue
                    larger = self.planner.settle(record)
                    if larger is not None:
                        pending.append((self._active_plan[record["task_id"]].task, larger))
                        pending.sort(key=lambda item: item[0].cost)
                        continue
                    self.store.append(record)
                    if record["task_id"] in self.graph.nodes:
                        settled[record["task_id"]] = record
                    outcome[record["status"]] += 1
                    if self.progress is not None:
                        self.progress(record, outcome.total(), total)
                if not finished and running:
                    time.sleep(self.tick)
                self.backend.check_deadline()
                if pending and not running and not finished:
                    raise RuntimeError("pending tasks have no ready prerequisite")
        finally:
            # an interrupted run leaves no record for the tasks in flight, so a rerun computes them
            for entry in running:
                try:
                    self.backend.cancel(entry.job)
                finally:
                    entry.invocation.cleanup()
            signal.signal(signal.SIGTERM, previous)
        return outcome

    # starting --------------------------------------------------------------------------------------

    def _admit(
        self,
        pending: list[tuple[Task, Limits]],
        running: list[_Running],
        settled: dict[str, Record],
    ) -> list[Record]:
        """Start ready tasks in cost order and record unusable prerequisites."""
        blocked = []
        while len(running) < self.config.workers:
            room = self.config.memory_budget_mb - sum(entry.limits.memory_mb for entry in running)
            cores = self.backend.cpu_cores - sum((entry.limits.cpu_cores or 1) for entry in running)
            fits = next(
                (
                    i
                    for i, (task, limits) in enumerate(pending)
                    if limits.memory_mb <= room
                    and (limits.cpu_cores is None or limits.cpu_cores <= cores)
                    and self._dependencies_settled(task, settled)
                ),
                None,
            )
            if fits is None:
                break
            self.backend.check_deadline()
            task, limits = pending.pop(fits)
            try:
                inputs = self._resolve_inputs(task, settled)
            except ArtifactError as problem:
                blocked.append(self._block(task, limits, str(problem)))
                continue
            # Register the child before handling interruptions. The watchdog unblocks signals.
            signals = signal.pthread_sigmask(signal.SIG_BLOCK, {signal.SIGINT, signal.SIGTERM})
            try:
                running.append(self._start(task, limits, inputs))
            finally:
                signal.pthread_sigmask(signal.SIG_SETMASK, signals)
        return blocked

    def _dependencies_settled(self, task: Task, settled: dict[str, Record]) -> bool:
        node = self.graph.nodes.get(task.id)
        return node is None or all(source.producer in settled for source in node.inputs.values())

    def _resolve_inputs(self, task: Task, settled: dict[str, Record]) -> dict[str, Any]:
        inputs: dict[str, Any] = {}
        node = self.graph.nodes.get(task.id)
        if node is None:
            return inputs
        for name, source in node.inputs.items():
            record = settled[source.producer]
            if record["status"] != Status.OK:
                why = f": {record['error']}" if record.get("error") else ""
                raise ArtifactError(f"prerequisite {source.producer} ended {record['status']}{why}")
            try:
                inputs[name] = self._read_output(record, source.output, source.kind) | {
                    "producer": source.producer,
                    "record_id": record["record_id"],
                    "attempt_id": record["attempt_id"],
                }
            except (ArtifactError, OSError) as problem:
                raise ArtifactError(f"prerequisite {source.producer}: {problem}") from problem
        for name, source in node.inputs.items():
            if source.model_input is not None:
                expected = inputs[source.model_input]["digest"]
                if model_digest(inputs[name]["data"]) != expected:
                    raise ArtifactError(
                        f"prerequisite {source.producer}/{source.output} has an incompatible model"
                    )
        return inputs

    def _claim(
        self, task: Task, attempt_id: str, started_at: str, log: Path | None, inputs: dict[str, Any]
    ) -> None:
        self.store.start_attempt(
            self.stamp.get("run_id", ""),
            self._active_plan[task.id].manifest_entry(),
            attempt_id,
            started_at,
            str(log.relative_to(self.run_dir)) if log else None,
            prerequisites=[ref["record_id"] for ref in inputs.values()],
        )

    def _block(self, task: Task, limits: Limits, error: str) -> Record:
        earlier = self.planner.attempt_of(task.id)
        attempt_id = earlier or uuid4().hex
        started_at = datetime.now(UTC).isoformat(timespec="seconds")
        if earlier is None:
            self._claim(task, attempt_id, started_at, None, {})
        return self._result_record(
            task,
            limits,
            attempt_id,
            started_at,
            None,
            {},
            JobResult(0, 0, {}),
            Status.BLOCKED,
            error,
        )

    def _start(self, task: Task, limits: Limits, inputs: dict[str, Any]) -> _Running:
        trial_id = uuid4().hex
        earlier = self.planner.attempt_of(task.id)
        attempt_id = earlier or trial_id
        log = self.run_dir / "logs" / f"{_slug(task.id)}-{trial_id}.log"
        started_at = datetime.now(UTC).isoformat(timespec="seconds")
        if earlier is None:
            self._claim(task, attempt_id, started_at, log, inputs)
        payload = task.payload | ({"inputs": inputs} if inputs else {})
        request_root = self.backend.workspace or self.run_dir
        repository = self.source.root if self.source else REPOSITORY
        command = self.source.command if self.source else self.runner
        watchdog = self.source.watchdog if self.source else WATCHDOG
        invocation = RunnerInvocation.prepare(
            command, "run", payload, request_root / "requests", repository=repository
        )
        try:
            job = self.backend.start(invocation.command, limits, log, cwd=repository, watchdog=watchdog)
        except BaseException:
            invocation.cleanup()
            raise
        return _Running(task, limits, job, invocation, log, attempt_id, started_at, inputs, trial_id)

    # ending ----------------------------------------------------------------------------------------

    def _collect(self, running: list[_Running]) -> list[Record]:
        """Records for the processes that ended or had to be stopped; removes them from `running`."""
        records = []
        for entry in list(running):
            try:
                outcome = self.backend.observe(entry.job)
            except RuntimeError:
                running.remove(entry)
                entry.invocation.cleanup()
                raise
            if outcome is None:
                continue
            running.remove(entry)
            try:
                records.append(self._record(entry, outcome))
            finally:
                entry.invocation.cleanup()
        return records

    def _record(self, entry: _Running, outcome: JobResult) -> Record:
        output = read_output(entry.log)
        exit_code = outcome.returncode
        result = None
        error = None
        if exit_code >= 0 and outcome.verdict is None:
            try:
                result = entry.invocation.task_result(output, exit_code)
            except RunnerError as problem:
                diagnostics = error_lines(output)
                error = f"{problem}\n{diagnostics}" if diagnostics else str(problem)
        if outcome.verdict in {"timeout", "memory"}:
            status = Status(outcome.verdict)
        elif outcome.verdict is not None:
            status = Status.ERROR
            error = (
                "job watchdog was cancelled"
                if outcome.verdict == "cancelled"
                else f"job exceeded its {outcome.verdict} limit"
            )
        elif result is not None and result.get("status") in RUNNER_STATUSES:
            status = Status(result["status"])
        elif error is not None:
            status = Status.ERROR
        elif exit_code > 0:
            status = Status.ERROR
            error = outcome.data.get("launch_error") or error_lines(output) or f"exit status {exit_code}"
        else:
            status = Status.CRASHED
            error = (
                f"ended by signal {signal.Signals(-exit_code).name}"
                if exit_code < 0
                else "ended without a result"
            )

        result = result or {}
        staged = result.pop("artifacts", {})
        result.pop("artifact_outputs", None)
        result.pop("artifact_inputs", None)
        node = self.graph.nodes.get(entry.task.id)
        if status == Status.OK and (staged or (node is not None and node.outputs)):
            try:
                result["artifact_outputs"] = self._publish_outputs(entry, staged)
            except (ArtifactError, OSError, ValueError) as problem:
                status = Status.ERROR
                error = f"invalid artifact output: {problem}"
        if entry.inputs:
            result["artifact_inputs"] = {
                name: {key: value for key, value in ref.items() if key != "data"}
                for name, ref in entry.inputs.items()
            }
        keep_log = status not in RUNNER_STATUSES
        if not keep_log:
            entry.log.unlink(missing_ok=True)
        record = self._result_record(
            entry.task,
            entry.limits,
            entry.attempt_id,
            entry.started_at,
            entry.log if keep_log else None,
            result,
            outcome,
            status,
            error,
        )
        resources = self._active_plan[entry.task.id].resources
        if outcome.data.get("deadline_scope") == "run":
            record["deadline_scope"] = "run"
        if resources is not None:
            record["resource_estimate"] = resources
            record["resource_context"] = resources["fingerprint_context"]
            record["trial_id"] = entry.trial_id
        return record

    def _publish_outputs(self, entry: _Running, staged: Any) -> dict[str, Any]:
        node = self.graph.nodes.get(entry.task.id)
        if node is None or self.artifacts is None:
            raise ArtifactError("returned artifact names must match the graph declaration")
        return self.artifacts.publish_outputs(staged, node.outputs, entry.attempt_id)

    def _result_record(
        self,
        task: Task,
        limits: Limits,
        attempt_id: str,
        started_at: str,
        log: Path | None,
        result: dict[str, Any],
        outcome: JobResult,
        status: Status,
        error: str | None,
    ) -> Record:
        planned = self._active_plan[task.id]
        return build_record(
            task,
            limits,
            status=status,
            result=result,
            error=error,
            attempt_id=attempt_id,
            started_at=started_at,
            log=str(log.relative_to(self.run_dir)) if log else None,
            exit_code=outcome.returncode,
            wall_seconds=outcome.wall_seconds,
            measured=outcome.data,
            resource_controls=self.backend.controls(),
            memory_guard=self.guard.name,
            stamp=self.stamp,
            computation_id=planned.computation_id,
            check_id=planned.check_id,
            record_id=planned.record_id,
        )


def _raise_interrupt(signum: int, frame: object) -> None:
    raise KeyboardInterrupt


def _slug(task_id: str) -> str:
    """A file name for a task id: readable, and unique through a hash of the id."""
    readable = re.sub(r"[^A-Za-z0-9._-]+", "_", task_id).strip("_")[:80]
    return f"{readable}-{hashlib.sha1(task_id.encode()).hexdigest()[:8]}"
