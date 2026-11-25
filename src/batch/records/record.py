"""The record of one attempt: the object a store keeps, a report reads and a later run reuses.

This is the one place that says which fields a record has. The scheduler writes records with `build`;
the stores keep them as JSON objects without looking inside, except for the fields named here.
"""

from __future__ import annotations

import signal
from datetime import UTC, datetime
from pathlib import Path
from typing import Any, Required, TypedDict

from ..tasks import Limits, Status, Task

RECORD_SCHEMA = 1


class Record(TypedDict, total=False):
    """One attempt that ended. Records from before versioned runs have the first three groups only."""

    # which attempt of which task
    task_id: Required[str]
    attempt_id: str
    task: dict[str, Any]  # as the runner expanded it; in a report, the member of the selected run
    started_at: str

    # how it ended
    status: Required[str]  # a value of model.Status
    value: Any
    predicted: Any
    agrees: bool | None
    detail: dict[str, Any]  # the rest of the runner's result: method, timings, artifacts, evidence
    error: str | None
    exit_code: int | None
    exit_signal: str | None
    log: str | None  # kept when the runner gave no result; relative to the run directory

    # what it used and what it was allowed
    wall_seconds: float
    cpu_seconds: float
    peak_rss_mb: float
    peak_sampled_bytes: int | None
    cgroup_memory_peak_bytes: int | None
    cgroup_memory_events: dict[str, int] | None
    resource_controls: dict[str, Any]
    limits: dict[str, Any]
    memory_guard: str

    # the stamp of the run that computed it
    run_id: str
    runner: dict[str, Any]
    code: dict[str, Any]  # commit, dirty

    # what makes it reusable: versioned identities (identity.py)
    schema_version: int
    computation_id: str
    check_id: str
    record_id: str

    # under a resource policy (resources.py, planning.py)
    resource_estimate: dict[str, Any]
    resource_context: dict[str, Any]
    trial_id: str
    resource_attempts: list[dict[str, Any]]
    deadline_scope: str  # "run" on an attempt the deadline of the run stopped; such a record is not kept

    # added when a store hands a record out
    log_directory: str  # the run directory of the attempt, when it is not the one reported on
    selected_run_id: str


def build(
    task: Task,
    limits: Limits,
    *,
    status: Status,
    result: dict[str, Any],
    error: str | None,
    attempt_id: str,
    started_at: str,
    log: str | None,
    exit_code: int,
    wall_seconds: float,
    measured: dict[str, Any],
    resource_controls: dict[str, Any],
    memory_guard: str,
    stamp: dict[str, Any],
    computation_id: str,
    check_id: str,
    record_id: str,
) -> Record:
    """The record of an attempt, from the runner's result and what the backend measured of the job."""
    record: Record = {
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
        "wall_seconds": round(wall_seconds, 3),
        "cpu_seconds": round(measured.get("cpu_seconds", 0), 3),
        "peak_rss_mb": round(measured.get("peak_rss_mb", 0), 1),
        "peak_sampled_bytes": measured.get("peak_sampled_bytes"),
        "cgroup_memory_peak_bytes": measured.get("cgroup_memory_peak_bytes"),
        "cgroup_memory_events": measured.get("cgroup_memory_events"),
        "resource_controls": resource_controls
        | {"effective_job": measured.get("effective"), "effective_run": measured.get("effective_run")},
        "limits": limits.as_dict(),
        "memory_guard": memory_guard,
        "exit_code": exit_code if exit_code >= 0 and status != Status.BLOCKED else None,
        "exit_signal": signal.Signals(-exit_code).name if exit_code < 0 else None,
        "started_at": started_at,
        "log": log,
    }
    record.update(stamp)  # type: ignore[typeddict-item]
    record.update(
        {
            "schema_version": RECORD_SCHEMA,
            "computation_id": computation_id,
            "check_id": check_id,
            "record_id": record_id,
        }
    )
    return record


def _utc_start(value: object) -> str:
    if not isinstance(value, str):
        return ""
    try:
        start = datetime.fromisoformat(value)
        if start.tzinfo is None:
            start = start.replace(tzinfo=UTC)
        return start.astimezone(UTC).isoformat(timespec="microseconds")
    except (ValueError, OverflowError):
        return ""


def attempt_started_at(record: Record) -> str:
    """A sortable UTC timestamp for the first trial, or an empty string if unavailable."""
    # The top-level timestamp is the terminal trial's start on a retried attempt.
    trials = record.get("resource_attempts")
    if isinstance(trials, list) and trials and isinstance(trials[0], dict):
        first_start = _utc_start(trials[0].get("started_at"))
        if first_start:
            return first_start
    return _utc_start(record.get("started_at"))


def surface(record: Record) -> Any:
    """The surface a task computed on, if its task names one."""
    task = record.get("task")
    return task.get("surface") if isinstance(task, dict) else None


def method(record: Record) -> str | None:
    """The method the runner says it used."""
    detail = record.get("detail")
    value = detail.get("method") if isinstance(detail, dict) else None
    return value if isinstance(value, str) and value else None


def commit(record: Record) -> str | None:
    """The commit of the code that computed the record."""
    code = record.get("code")
    value = code.get("commit") if isinstance(code, dict) else None
    return value if isinstance(value, str) and value else None


def log_path(record: Record) -> str | None:
    """Where the kept log of an attempt is, from the run directory it was written under."""
    log = record.get("log")
    directory = record.get("log_directory")
    if log and isinstance(directory, str):
        return str(Path(directory) / log)
    return log
