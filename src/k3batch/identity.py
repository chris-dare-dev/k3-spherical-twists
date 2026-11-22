"""Versioned identities for measurements and their checks."""

from __future__ import annotations

import hashlib
import json
import platform
import shutil
import sys
from collections.abc import Mapping
from pathlib import Path
from typing import Any

from .model import RUNNER_STATUSES, Status, Task
from .runner import REPOSITORY, RunnerError

IDENTITY_VERSION = 1
RECORD_SCHEMA = 1

# These fields describe the placement of a task within a batch.
TASK_LABELS = {"id", "set", "group", "cost"}
COMPARISONS = {"equals", "fields"}


def fingerprint(value: Any) -> str:
    """Digest the canonical JSON encoding, preserving types and array order."""
    try:
        data = json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)
    except (TypeError, ValueError) as exc:
        raise RunnerError(f"cannot fingerprint non-JSON runner data: {exc}") from exc
    return hashlib.sha256(data.encode("utf-8")).hexdigest()


def implementation_files(
    runner: tuple[str, ...], repository: Path
) -> tuple[Path, dict[str, dict[str, Path]]]:
    """Find the local source and runner files. Keys describe their original locations."""
    sources = [
        repository / "src" / "K3Twists.m2",
        *(repository / "src" / "K3Twists").rglob("*.m2"),
        *(repository / "src" / "runners").rglob("*.m2"),
        *(repository / "src" / "k3batch").rglob("*.py"),
    ]
    if not runner:
        raise RunnerError("the runner command is empty")
    executable = shutil.which(runner[0])
    if executable is None:
        raise RunnerError(f"cannot start the runner: {runner[0]} not found")
    launcher = Path(executable).absolute()
    resolved = launcher.resolve()
    runtime_files = {str(resolved): launcher}
    # The installed M2 command can be a launcher for the adjacent M2-binary executable.
    companion = resolved.with_name(f"{resolved.name}-binary")
    if companion.is_file():
        runtime_files[str(companion)] = companion
    for arg in runner[1:]:
        path = repository / arg
        if path.suffix in {".m2", ".py", ".sh"} and path.is_file():
            runtime_files[str(path)] = path
    return launcher, {
        "sources": {path.relative_to(repository).as_posix(): path for path in sources},
        "runner_files": runtime_files,
    }


def file_digest(path: Path) -> str:
    try:
        with path.open("rb") as handle:
            return hashlib.file_digest(handle, "sha256").hexdigest()
    except OSError as exc:
        raise RunnerError(f"cannot fingerprint implementation file {path}: {exc}") from exc


def implementation_fingerprint(
    runner: tuple[str, ...],
    versions: dict[str, Any],
    repository: Path = REPOSITORY,
    *,
    files: dict[str, dict[str, Path]] | None = None,
) -> str:
    """Fingerprint the local implementations used to expand and execute tasks."""
    if files is None:
        _, files = implementation_files(runner, repository)
    return fingerprint(
        {
            "version": IDENTITY_VERSION,
            **{
                kind: {key: file_digest(path) for key, path in paths.items()} for kind, paths in files.items()
            },
            "runner": runner,
            "versions": versions,
            "python": sys.version,
            "system": [platform.system(), platform.machine()],
        }
    )


def task_identities(task: Task, implementation: str, graph: dict[str, Any] | None = None) -> tuple[str, str]:
    """Fingerprint the operation and the independently comparable prediction, if declared."""
    operation = {key: value for key, value in task.payload.items() if key not in TASK_LABELS}
    operation["kind"] = task.kind
    if graph is not None:
        operation["graph"] = graph
    comparison = operation.get("comparison")
    prediction = operation.pop("prediction", None) if comparison is not None else None
    if comparison is not None:
        if not isinstance(comparison, str) or comparison not in COMPARISONS:
            raise RunnerError(f"task {task.id} declares an unknown comparison: {comparison!r}")
        predicted = operation.get("predicted")
        if comparison == "fields" and predicted is not None and not isinstance(predicted, dict):
            raise RunnerError(f"task {task.id} requires named fields for comparison")
        del operation["comparison"]
        operation.pop("predicted", None)

    computation_id = fingerprint(
        {
            "version": IDENTITY_VERSION,
            "implementation": implementation,
            "operation": operation,
            "independent_prediction": comparison is not None,
        }
    )
    check_id = fingerprint(
        {
            "version": IDENTITY_VERSION,
            "computation_id": computation_id,
            "comparison": comparison,
            "predicted": task.payload.get("predicted"),
            **({"prediction": prediction} if prediction is not None else {}),
        }
    )
    return computation_id, check_id


def recheck(task: Task, record: Mapping[str, Any], check_id: str) -> dict[str, Any]:
    """Record a new check against the original observation when its prediction changed."""
    if record["check_id"] == check_id:
        return {}
    predicted = task.payload.get("predicted")
    comparison = task.payload.get("comparison")
    status = record["status"]
    agrees = None
    if status in RUNNER_STATUSES - {Status.UNSUPPORTED}:
        measured = record["value"]
        if predicted is not None:
            if comparison == "fields":
                if not isinstance(predicted, dict) or not isinstance(measured, dict):
                    raise RunnerError(f"task {task.id} requires named fields for comparison")
                if not predicted.keys() <= measured.keys():
                    raise RunnerError(f"observation for {task.id} is missing predicted fields")
                measured = {key: measured[key] for key in predicted}
            agrees = fingerprint(measured) == fingerprint(predicted)
        status = Status.MISMATCH if agrees is False else Status.OK
    return {"status": str(status), "predicted": predicted, "agrees": agrees}
