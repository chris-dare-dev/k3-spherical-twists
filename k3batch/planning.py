"""What a run computes: which earlier results stand, what runs under which limits, what is refused.

The planner reads the history of earlier runs and decides; the scheduler carries the decisions out.
"""

from __future__ import annotations

from collections.abc import Callable, Collection, Mapping, Sequence
from dataclasses import dataclass
from typing import Any
from uuid import uuid4

from .config import BatchConfig, ConfigError
from .graph import Graph
from .identity import fingerprint, recheck, task_identities
from .model import Limits, Status, Task
from .record import Record
from .resources import HISTORY_WINDOW, estimate, grow_limits, resource_context
from .store import RunHistory

# what a trial keeps of the record of an attempt that ended at a limit and was tried again
TRIAL_FIELDS = (
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


@dataclass(frozen=True)
class PlannedTask:
    """One task of a run: the record that answers it, and whether that record already exists."""

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


class Planner:
    """Decides from the history what a run reuses, what it computes, and what it tries again.

    `plan` answers before anything runs: each task is reused or computed, and a task that cannot fit
    the budgets of the run is refused. `settle` answers after each attempt: its record stands, or the
    task is tried again with larger limits.
    """

    def __init__(
        self,
        *,
        config: BatchConfig,
        graph: Graph,
        history: RunHistory,
        guard: str,
        cpu_cores: int,
        retry: Collection[str] = (),
        usable: Callable[[str, Record], bool] = lambda task_id, record: True,
    ) -> None:
        self.config = config
        self.graph = graph
        self.history = history
        self.guard = guard
        self.cpu_cores = cpu_cores
        self.retry = frozenset(retry)
        # whether what a successful record of a task left behind can still be read
        self.usable = usable
        self._trials: dict[str, list[dict[str, Any]]] = {}

    # before the run -----------------------------------------------------------------------------------

    def plan(self, tasks: Sequence[Task], implementation: str) -> list[PlannedTask]:
        """Select existing records and reserve identifiers for the work this run will start."""
        by_id = {task.id: task for task in tasks}
        policy = self.config.resources
        window = HISTORY_WINDOW if policy else 1
        plan: dict[str, PlannedTask] = {}
        records: dict[str, str] = {}
        for level in self.graph.levels:
            identified = []
            for task_id in level:
                node = self.graph.nodes.get(task_id)
                contract = node.identity(records) if node else None
                task = by_id[task_id]
                identified.append((task, contract, *task_identities(task, implementation, contract)))
            history_by_id = self.history.recent_by_computation(
                [identity for _, _, identity, _ in identified], window
            )
            for task, contract, computation_id, check_id in identified:
                limits = self.config.limits_for(task)
                resource_estimate = None
                history = history_by_id.get(computation_id, [])
                if policy:
                    caps = policy.caps(self.config.memory_budget_mb, self.cpu_cores)
                    context = resource_context(task, computation_id, self.guard, self.cpu_cores)
                    if self.config.weighted_cpu and limits.cpu_cores is not None:
                        caps = Limits(
                            caps.time_seconds, caps.memory_mb, min(caps.cpu_cores or 1, limits.cpu_cores)
                        )
                    limits, resource_estimate = estimate(limits, caps, policy, context, history)
                    resource_estimate["fingerprint"] = fingerprint(context)
                previous = history[0] if history else None
                check = recheck(task, previous, check_id) if previous is not None else {}
                reused = previous is not None and self._stands(previous, limits, check)
                if reused and previous is not None and previous["status"] == Status.OK:
                    reused = self.usable(task.id, previous)
                if not reused and limits.memory_mb > self.config.memory_budget_mb:
                    raise ConfigError(
                        f"task {task.id} has a memory limit of {limits.memory_mb} MB, "
                        f"above the budget of {self.config.memory_budget_mb} MB"
                    )
                if not reused and limits.cpu_cores is not None and limits.cpu_cores > self.cpu_cores:
                    raise ConfigError(f"task {task.id} exceeds the run CPU budget")
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
        return [plan[task.id] for task in tasks]

    def _stands(self, record: Record, limits: Limits, check: dict[str, Any]) -> bool:
        """Whether the latest record of a computation answers the task, checked as it now is."""
        status = check.get("status", record["status"])
        if status in self.retry:
            return False
        previous_limits = record.get("limits", {})
        if status == Status.TIMEOUT and limits.time_seconds > previous_limits.get("time_seconds", 0):
            return False
        return not (status == Status.MEMORY and limits.memory_mb > previous_limits.get("memory_mb", 0))

    # during the run -----------------------------------------------------------------------------------

    def begin(self) -> None:
        """Forget the trials of an earlier run."""
        self._trials.clear()

    def attempt_of(self, task_id: str) -> str | None:
        """The attempt the earlier trials of a task belong to; None before its first trial."""
        trials = self._trials.get(task_id)
        return trials[0]["attempt_id"] if trials else None

    def settle(self, record: Record) -> Limits | None:
        """Decide what follows an attempt that ended, from its record.

        Returns the larger limits to try the task again with, when the resource policy allows another
        trial. Otherwise the record stands and None is returned, after the trials that led to it were
        added to it as `resource_attempts`.
        """
        policy = self.config.resources
        if policy is None:
            return None
        task_id = record["task_id"]
        if record["status"] == Status.BLOCKED:
            previous = self._trials.pop(task_id, [])
            if previous:
                record["resource_attempts"] = previous
            return None
        trials = self._trials.setdefault(task_id, [])
        caps = policy.caps(self.config.memory_budget_mb, self.cpu_cores)
        expanded = grow_limits(Limits(**record["limits"]), caps, record["status"])
        retrying = expanded is not None and len(trials) < policy.retry_attempts
        if retrying:
            decision = "retry with larger reservation"
        elif record["status"] in {Status.MEMORY, Status.TIMEOUT}:
            decision = "ceiling reached" if expanded is None else "retry allowance exhausted"
        else:
            decision = "finished"
        ended: Mapping[str, Any] = record
        trials.append({key: ended[key] for key in TRIAL_FIELDS} | {"decision": decision})
        if retrying:
            return expanded
        record["resource_attempts"] = self._trials.pop(task_id)
        return None
