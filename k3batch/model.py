"""Tasks, limits and outcomes."""

from __future__ import annotations

from dataclasses import dataclass
from enum import StrEnum
from typing import Any


class Status(StrEnum):
    """How an attempt ended. Reuse and retry policies are applied separately."""

    OK = "ok"  # a value was computed; it agrees with the predicted value, or there is none
    MISMATCH = "mismatch"  # a value was computed and differs from the predicted value
    UNSUPPORTED = "unsupported"  # the runner has no method for this task
    TIMEOUT = "timeout"  # stopped at the time limit
    MEMORY = "memory"  # stopped at the memory limit
    BLOCKED = "blocked"  # a prerequisite could not produce the required artifact
    ERROR = "error"  # the runner reported an error
    CRASHED = "crashed"  # the process ended without a result for another reason


# Statuses the runner itself may report; the others are decided by the scheduler.
RUNNER_STATUSES = frozenset({Status.OK, Status.MISMATCH, Status.UNSUPPORTED})

# Statuses that count as the task having been carried out as intended.
COMPLETED_STATUSES = frozenset({Status.OK, Status.UNSUPPORTED})

# Statuses that make a run fail; the remaining ones are stops at a limit.
FAILED_STATUSES = frozenset({Status.MISMATCH, Status.ERROR, Status.CRASHED, Status.BLOCKED})


@dataclass(frozen=True)
class Limits:
    """The resources one task may use."""

    time_seconds: float
    memory_mb: int
    cpu_cores: int | None = None

    def as_dict(self) -> dict[str, Any]:
        result = {"time_seconds": self.time_seconds, "memory_mb": self.memory_mb}
        return result | ({"cpu_cores": self.cpu_cores} if self.cpu_cores is not None else {})


class TaskError(ValueError):
    """A task of an expansion lacks a field the scheduler reads, or has one of the wrong type."""


@dataclass(frozen=True)
class Task:
    """One unit of work, as produced by the runner's expansion of a batch.

    The scheduler reads `id`, `cost`, `set` and `group`; the rest of `payload` is the runner's business
    and is handed back to it unchanged.
    """

    id: str
    kind: str
    cost: float
    set: int
    group: str
    payload: dict[str, Any]

    @classmethod
    def from_payload(cls, payload: Any, *, complete: bool = False) -> Task:
        """Read one task of an expansion: the only place that decides what a task must look like.

        The file protocol sends `complete` tasks: every field the scheduler reads, the version of the
        kind and the names of its requirements. A runner that prints marker lines may leave out `set`,
        `cost` and `group`; a field it does give follows the same rules.
        """
        if not isinstance(payload, dict):
            raise TaskError("task must be an object")
        fields: dict[str, Any] = (
            payload if complete else {"set": 0, "cost": 0, "group": payload.get("kind")} | payload
        )
        for key in ("id", "kind", "group"):
            if not isinstance(fields.get(key), str) or not fields[key]:
                raise TaskError(f"{key} must be a nonempty string")
        for key, minimum in (("set", 0), ("kind_version", 1))[: 2 if complete else 1]:
            if type(fields.get(key)) is not int or fields[key] < minimum:
                raise TaskError(f"{key} must be an integer >= {minimum}")
        cost = fields.get("cost")
        if not isinstance(cost, (int, float)) or isinstance(cost, bool) or not cost >= 0:
            raise TaskError("cost must be a nonnegative number")
        requirements = fields.get("requirements")
        if complete and (
            not isinstance(requirements, list) or any(not isinstance(item, str) for item in requirements)
        ):
            raise TaskError("requirements must be a list of strings")
        try:
            return cls(fields["id"], fields["kind"], float(cost), fields["set"], fields["group"], payload)
        except OverflowError:
            raise TaskError("cost is too large") from None
