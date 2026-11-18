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

from .artifacts import ArtifactError, ArtifactStore, read_artifact_json
from .config import BatchConfig, ConfigError
from .execution import JobResult, LocalBackend, LocalJob, read_output
from .graph import Graph
from .identity import RECORD_SCHEMA, fingerprint, implementation_fingerprint, recheck, task_identities
from .memory import MemoryGuard
from .model import RUNNER_STATUSES, Limits, Status, Task
from .resources import HISTORY_WINDOW, estimate, grow_limits, resource_context
from .runner import REPOSITORY, RunnerError, RunnerInvocation, error_lines
from .sqlite_store import SQLiteStore
from .store import ResultStore


@dataclass(frozen=True)
class PlannedTask:
    task: Task
    limits: Limits
    computation_id: str
    check_id: str
    record_id: str
    reused: bool
    check: dict[str, Any]
    graph: dict[str, Any] | None = None
    resources: dict[str, Any] | None = None

    def manifest_entry(self) -> dict[str, Any]:
        return self.task.payload | {
            "limits": self.limits.as_dict(),
            "computation_id": self.computation_id,
            "check_id": self.check_id,
            "record_id": self.record_id,
            "check": self.check,
            **({"graph": self.graph} if self.graph is not None else {}),
            **({"resource_estimate": self.resources} if self.resources is not None else {}),
        }


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


Progress = Callable[[dict[str, Any], int, int], None]


class Scheduler:
    def __init__(
        self,
        *,
        config: BatchConfig,
        tasks: Sequence[Task],
        store: ResultStore | SQLiteStore,
        run_dir: Path,
        runner: tuple[str, ...],
        guard: MemoryGuard,
        backend: LocalBackend | None = None,
        stamp: dict[str, Any] | None = None,
        retry: Collection[str] = (),
        progress: Progress | None = None,
        tick: float = 0.02,
    ) -> None:
        self.config = config
        self.tasks = list(tasks)
        self.store = store
        self.graph = Graph.build(self.tasks, config.graph)
        if self.graph.nodes and not isinstance(store, SQLiteStore):
            raise ConfigError("a dependency graph requires a SQLite result store")
        self.artifacts = (
            ArtifactStore(store.path.with_suffix(store.path.suffix + ".artifacts"))
            if isinstance(store, SQLiteStore) and self.graph.nodes
            else None
        )
        self.run_dir = run_dir
        self.runner = runner
        self.guard = guard
        self.backend = backend or LocalBackend(guard, config.memory_budget_mb, config.workers)
        self._own_backend = backend is None
        self.stamp = stamp or {}
        self.retry = frozenset(retry)
        self.progress = progress
        self.tick = tick
        self._active_plan: dict[str, PlannedTask] = {}
        self._resource_trials: dict[str, list[dict[str, Any]]] = {}

    def plan(self) -> list[PlannedTask]:
        """Select existing attempts and reserve identifiers for work this run will start."""
        implementation = implementation_fingerprint(self.runner, self.stamp.get("runner", {}))
        tasks = {task.id: task for task in self.tasks}
        policy = self.config.resources
        window = HISTORY_WINDOW if policy else 1
        jsonl_history: dict[str, list[dict[str, Any]]] = {}
        if isinstance(self.store, ResultStore):
            for record in self.store.records():
                identity = record.get("computation_id")
                if (
                    record.get("schema_version") == RECORD_SCHEMA
                    and isinstance(identity, str)
                    and all(isinstance(record.get(key), str) for key in ("check_id", "record_id"))
                ):
                    history = jsonl_history.setdefault(identity, [])
                    history.insert(0, record)
                    del history[window:]
        plan: dict[str, PlannedTask] = {}
        records: dict[str, str] = {}
        for level in self.graph.levels:
            identified = []
            for task_id in level:
                node = self.graph.nodes.get(task_id)
                contract = node.identity(records) if node else None
                task = tasks[task_id]
                identified.append((task, contract, *task_identities(task, implementation, contract)))
            history_by_id = (
                self.store.recent_by_computation([identity for _, _, identity, _ in identified], window)
                if isinstance(self.store, SQLiteStore)
                else jsonl_history
            )
            for task, contract, computation_id, check_id in identified:
                limits = self.config.limits_for(task)
                resource_estimate = None
                history = history_by_id.get(computation_id, [])
                if policy:
                    caps = policy.caps(self.config.memory_budget_mb, self.backend.cpu_cores)
                    context = resource_context(task, computation_id, self.guard.name, self.backend.cpu_cores)
                    limits, resource_estimate = estimate(limits, caps, policy, context, history)
                    resource_estimate["fingerprint"] = fingerprint(context)
                previous = history[0] if history else None
                check = recheck(task, previous, check_id) if previous is not None else {}
                reused = previous is not None and self._can_reuse(previous, limits, check)
                if reused and previous is not None and previous["status"] == Status.OK:
                    reused = self._valid_outputs(task.id, previous)
                if not reused and limits.memory_mb > self.config.memory_budget_mb:
                    raise ConfigError(
                        f"task {task.id} has a memory limit of {limits.memory_mb} MB, "
                        f"above the budget of {self.config.memory_budget_mb} MB"
                    )
                record_id = previous["record_id"] if reused and previous is not None else uuid4().hex
                records[task.id] = record_id
                plan[task.id] = PlannedTask(
                    task,
                    limits,
                    computation_id,
                    check_id,
                    record_id,
                    reused,
                    check if reused else {},
                    contract,
                    resource_estimate,
                )
        return [plan[task.id] for task in self.tasks]

    def _valid_outputs(self, task_id: str, record: dict[str, Any]) -> bool:
        node = self.graph.nodes.get(task_id)
        if node is None or not node.outputs:
            return True
        try:
            for name, kind in node.outputs.items():
                self._read_output(record, name, kind)
        except (ArtifactError, OSError):
            return False
        return True

    def _read_output(self, record: dict[str, Any], name: str, kind: str) -> dict[str, Any]:
        assert self.artifacts is not None
        reference = record.get("detail", {}).get("artifact_outputs", {}).get(name)
        if not isinstance(reference, dict) or reference.get("kind") != kind:
            raise ArtifactError(f"missing {kind} artifact {name}")
        digest = reference.get("digest")
        if not isinstance(digest, str):
            raise ArtifactError(f"missing digest for artifact {name}")
        data = read_artifact_json(self.artifacts.read(digest))
        if data["kind"] != kind:
            raise ArtifactError(f"artifact {name} has kind {data['kind']}, expected {kind}")
        return {"digest": digest, "data": data}

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
        if self._own_backend:
            with self.backend:
                return self._run(plan)
        return self._run(plan)

    def _run(self, plan: Sequence[PlannedTask] | None) -> Counter[str]:
        members = self.plan() if plan is None else plan
        self._active_plan = {entry.task.id: entry for entry in members}
        pending = self.pending(members)
        self._resource_trials.clear()
        total = len(pending)
        outcome: Counter[str] = Counter()
        wanted = [entry for entry in members if entry.reused]
        settled: dict[str, dict[str, Any]] = {}
        if self.graph.nodes and isinstance(self.store, SQLiteStore):
            records = self.store.by_record_id([entry.record_id for entry in wanted])
            settled = {entry.task.id: records[entry.record_id] for entry in wanted}
        running: list[_Running] = []
        (self.run_dir / "logs").mkdir(parents=True, exist_ok=True)
        # a terminated scheduler stops its task processes the same way an interrupted one does
        previous = signal.signal(signal.SIGTERM, _raise_interrupt)
        try:
            while pending or running:
                blocked = self._admit(pending, running, settled)
                finished = blocked + self._collect(running)
                for record in finished:
                    if self._resource_retry(record, pending):
                        continue
                    self.store.append(record)
                    if record["task_id"] in self.graph.nodes:
                        settled[record["task_id"]] = record
                    outcome[record["status"]] += 1
                    if self.progress is not None:
                        self.progress(record, outcome.total(), total)
                if not finished and running:
                    time.sleep(self.tick)
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

    def _resource_retry(self, record: dict[str, Any], pending: list[tuple[Task, Limits]]) -> bool:
        policy = self.config.resources
        if policy is None:
            return False
        task_id = record["task_id"]
        if record["status"] == Status.BLOCKED:
            previous = self._resource_trials.pop(task_id, [])
            if previous:
                record["resource_attempts"] = previous
            return False
        trials = self._resource_trials.setdefault(task_id, [])
        limits = Limits(**record["limits"])
        caps = policy.caps(self.config.memory_budget_mb, self.backend.cpu_cores)
        expanded = grow_limits(limits, caps, record["status"])
        retrying = expanded is not None and len(trials) < policy.retry_attempts
        if retrying:
            decision = "retry with larger reservation"
        elif record["status"] in {Status.MEMORY, Status.TIMEOUT}:
            decision = "ceiling reached" if expanded is None else "retry allowance exhausted"
        else:
            decision = "finished"
        trial = {
            key: record[key]
            for key in (
                "attempt_id",
                "trial_id",
                "status",
                "limits",
                "started_at",
                "log",
                "wall_seconds",
                "cpu_seconds",
                "peak_sampled_bytes",
                "peak_rss_mb",
                "cgroup_memory_peak_bytes",
                "cgroup_memory_events",
                "resource_controls",
            )
        }
        trials.append(trial | {"decision": decision})
        if retrying and expanded is not None:
            pending.append((self._active_plan[task_id].task, expanded))
            pending.sort(key=lambda item: item[0].cost)
            return True
        record["resource_attempts"] = self._resource_trials.pop(task_id)
        return False

    # starting --------------------------------------------------------------------------------------

    def _admit(
        self,
        pending: list[tuple[Task, Limits]],
        running: list[_Running],
        settled: dict[str, dict[str, Any]],
    ) -> list[dict[str, Any]]:
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

    def _dependencies_settled(self, task: Task, settled: dict[str, dict[str, Any]]) -> bool:
        node = self.graph.nodes.get(task.id)
        return node is None or all(source.producer in settled for source in node.inputs.values())

    def _resolve_inputs(self, task: Task, settled: dict[str, dict[str, Any]]) -> dict[str, Any]:
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
                if inputs[name]["data"]["payload"]["model_digest"] != expected:
                    raise ArtifactError(
                        f"prerequisite {source.producer}/{source.output} has an incompatible model"
                    )
        return inputs

    def _claim(
        self, task: Task, attempt_id: str, started_at: str, log: Path | None, inputs: dict[str, Any]
    ) -> None:
        if isinstance(self.store, SQLiteStore):
            self.store.start_attempt(
                self.stamp["run_id"],
                self._active_plan[task.id].manifest_entry(),
                attempt_id,
                started_at,
                str(log.relative_to(self.run_dir)) if log else None,
                prerequisites=[ref["record_id"] for ref in inputs.values()],
            )

    def _block(self, task: Task, limits: Limits, error: str) -> dict[str, Any]:
        previous = self._resource_trials.get(task.id)
        attempt_id = previous[0]["attempt_id"] if previous else uuid4().hex
        started_at = datetime.now(UTC).isoformat(timespec="seconds")
        if not previous:
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
        previous = self._resource_trials.get(task.id)
        attempt_id = previous[0]["attempt_id"] if previous else trial_id
        log = self.run_dir / "logs" / f"{_slug(task.id)}-{trial_id}.log"
        started_at = datetime.now(UTC).isoformat(timespec="seconds")
        if not previous:
            self._claim(task, attempt_id, started_at, log, inputs)
        payload = task.payload | ({"inputs": inputs} if inputs else {})
        invocation = RunnerInvocation.prepare(self.runner, "run", payload, self.run_dir / "requests")
        try:
            job = self.backend.start(invocation.command, limits, log, cwd=REPOSITORY)
        except BaseException:
            invocation.cleanup()
            raise
        return _Running(task, limits, job, invocation, log, attempt_id, started_at, inputs, trial_id)

    # ending ----------------------------------------------------------------------------------------

    def _collect(self, running: list[_Running]) -> list[dict[str, Any]]:
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

    def _record(self, entry: _Running, outcome: JobResult) -> dict[str, Any]:
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
        if resources is not None:
            record["resource_estimate"] = resources
            record["resource_context"] = resources["fingerprint_context"]
            record["trial_id"] = entry.trial_id
        return record

    def _publish_outputs(self, entry: _Running, staged: Any) -> dict[str, Any]:
        node = self.graph.nodes.get(entry.task.id)
        if (
            node is None
            or self.artifacts is None
            or not isinstance(staged, dict)
            or staged.keys() != node.outputs.keys()
        ):
            raise ArtifactError("returned artifact names must match the graph declaration")
        for name, kind in node.outputs.items():
            data = staged[name]
            if not isinstance(data, dict) or data.get("kind") != kind:
                raise ArtifactError(f"output {name} must be a {kind} artifact")
        return {
            name: {"kind": kind, "digest": self.artifacts.publish(staged[name], entry.attempt_id)}
            for name, kind in node.outputs.items()
        }

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
    ) -> dict[str, Any]:
        exit_code = outcome.returncode
        record = {
            "task_id": task.id,
            "attempt_id": attempt_id,
            "task": task.payload,
            "status": str(status),
            "value": result.get("value"),
            "predicted": result.get("predicted", task.payload.get("predicted")),
            "agrees": result.get("agrees"),
            "detail": {
                key: value
                for key, value in result.items()
                if key not in {"status", "value", "predicted", "agrees"}
            },
            "error": error,
            "wall_seconds": round(outcome.wall_seconds, 3),
            "cpu_seconds": round(outcome.data.get("cpu_seconds", 0), 3),
            "peak_rss_mb": round(outcome.data.get("peak_rss_mb", 0), 1),
            "peak_sampled_bytes": outcome.data.get("peak_sampled_bytes"),
            "cgroup_memory_peak_bytes": outcome.data.get("cgroup_memory_peak_bytes"),
            "cgroup_memory_events": outcome.data.get("cgroup_memory_events"),
            "resource_controls": self.backend.controls()
            | {
                "effective_job": outcome.data.get("effective"),
                "effective_run": outcome.data.get("effective_run"),
            },
            "limits": limits.as_dict(),
            "memory_guard": self.guard.name,
            "exit_code": exit_code if exit_code >= 0 and status != Status.BLOCKED else None,
            "exit_signal": signal.Signals(-exit_code).name if exit_code < 0 else None,
            "started_at": started_at,
            "log": str(log.relative_to(self.run_dir)) if log else None,
        }
        planned = self._active_plan[task.id]
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
