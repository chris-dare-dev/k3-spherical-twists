"""Tables from the records of a batch: computed against predicted, mismatches, timeouts, kills."""

from __future__ import annotations

import json
import re
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

from .identity import RECORD_SCHEMA
from .model import Status
from .sqlite_store import SQLiteStore
from .store import ResultStore

NOT_RUN = "not run"
COLUMNS = [str(status) for status in Status] + [NOT_RUN]


def _cell(value: Any) -> str:
    """A value as it appears in a table cell."""
    if value is None:
        return ""
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, dict):
        return ", ".join(f"{key} {_cell(item)}" for key, item in value.items())
    if isinstance(value, list):
        return "(" + ", ".join(_cell(item) for item in value) + ")"
    if isinstance(value, float):
        return f"{value:g}"
    return str(value).replace("|", "\\|")


def _table(header: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    lines += ["| " + " | ".join(_cell(item) for item in row) + " |" for row in rows]
    return [*lines, ""]


def _name(record: dict[str, Any]) -> str:
    return f"`{record['task_id']}`"


def load_manifest(run_dir: Path, run_id: str | None = None) -> dict[str, Any]:
    """Read the latest manifest or a specific run's immutable manifest."""
    if run_id is None:
        path = run_dir / "manifest.json"
        if not path.exists():
            return {}
    else:
        if not re.fullmatch(r"[0-9a-f]{32}", run_id):
            raise RuntimeError(f"invalid run ID: {run_id!r}")
        path = run_dir / "runs" / f"{run_id}.json"
        if not path.exists():
            raise RuntimeError(f"run {run_id} is not in {run_dir}")
    manifest: dict[str, Any] = json.loads(path.read_text(encoding="utf-8"))
    return manifest


def selected_results(store: ResultStore | SQLiteStore, manifest: dict[str, Any]) -> dict[str, dict[str, Any]]:
    """Resolve the attempts pinned by a manifest, with label lookup for legacy reports."""
    if "schema_version" not in manifest:
        if isinstance(store, SQLiteStore):
            raise RuntimeError("a versioned manifest is required for a pinned run")
        return store.latest()
    if manifest["schema_version"] != RECORD_SCHEMA:
        raise RuntimeError(f"unsupported manifest schema version: {manifest['schema_version']}")

    if isinstance(store, SQLiteStore):
        attempts = store.by_record_id([task["record_id"] for task in manifest["tasks"]])
    else:
        attempts = {
            record["record_id"]: record
            for record in store.records()
            if record.get("schema_version") == RECORD_SCHEMA and isinstance(record.get("record_id"), str)
        }
    selected = {}
    for task in manifest["tasks"]:
        attempt = attempts.get(task["record_id"])
        if attempt is None or attempt.get("computation_id") != task["computation_id"]:
            continue
        selected[task["id"]] = (
            attempt
            | task["check"]
            | {
                "task": task,
                "task_id": task["id"],
                "check_id": task["check_id"],
            }
        )
    return selected


def render(
    run_dir: Path,
    *,
    full: bool = False,
    run_id: str | None = None,
    legacy: bool = False,
    store: ResultStore | SQLiteStore | None = None,
) -> str:
    """The report for a selected run, as Markdown."""
    store = store or ResultStore(run_dir / "results.jsonl")
    if isinstance(store, SQLiteStore):
        manifest = store.manifest(run_dir, run_id, legacy=legacy)
        if "schema_version" in manifest:
            selected = selected_results(store, manifest)
        else:
            selected = {
                record["task_id"]: record
                for record in store.query(run_dir=run_dir)
                if not legacy or "schema_version" not in record
            }
    elif legacy:
        manifest = load_manifest(run_dir)
        if "schema_version" in manifest:
            manifest = {}
        selected = {record["task_id"]: record for record in store.records() if "schema_version" not in record}
    else:
        manifest = load_manifest(run_dir, run_id)
        selected = selected_results(store, manifest)
    groups: dict[str, Counter[str]] = defaultdict(Counter)
    known = set()
    for task in manifest.get("tasks", []):
        known.add(task["id"])
        record = selected.get(task["id"])
        groups[task.get("group", task["kind"])][record["status"] if record else NOT_RUN] += 1
    for task_id, record in selected.items():
        if task_id not in known:
            groups[record["task"].get("group", record["task"].get("kind", "?"))][record["status"]] += 1
    records = sorted(selected.values(), key=lambda r: (r["task"].get("group", ""), r["task_id"]))

    lines = [f"# Results in {run_dir.name}", ""]
    if legacy:
        lines.append("- selection: unversioned historical records")
    if "run_id" in manifest:
        lines.append(f"- run: `{manifest['run_id']}`")
    if "run_state" in manifest:
        lines.append(f"- run state: {manifest['run_state']}")
    lines += _provenance(records, store.unreadable_lines)

    lines += ["## Summary", ""]
    used = [column for column in COLUMNS if any(counts[column] for counts in groups.values())]
    lines += _table(
        ["group", "tasks", *used],
        [
            [group, counts.total(), *(counts[column] for column in used)]
            for group, counts in sorted(groups.items())
        ],
    )

    def section(title: str, statuses: set[str], header: list[str], row: Any) -> None:
        chosen = [record for record in records if record["status"] in statuses]
        if chosen:
            lines.extend([f"## {title}", ""])
            lines.extend(_table(header, [row(record) for record in chosen]))

    section(
        "Computed values that differ from the predicted ones",
        {Status.MISMATCH},
        ["task", "computed", "predicted"],
        lambda r: [_name(r), r["value"], r["predicted"]],
    )
    section(
        "Stopped at a limit",
        {Status.TIMEOUT, Status.MEMORY},
        ["task", "status", "cost", "time limit (s)", "memory limit (MB)", "wall (s)", "peak (MB)"],
        lambda r: [
            _name(r),
            r["status"],
            r["task"].get("cost"),
            r["limits"]["time_seconds"],
            r["limits"]["memory_mb"],
            r["wall_seconds"],
            r["peak_rss_mb"],
        ],
    )
    section(
        "Errors and crashes",
        {Status.ERROR, Status.CRASHED, Status.BLOCKED},
        ["task", "status", "message", "log"],
        lambda r: [_name(r), r["status"], (r["error"] or "").replace("\n", "; "), _log_path(r)],
    )
    section(
        "No method",
        {Status.UNSUPPORTED},
        ["task", "predicted"],
        lambda r: [_name(r), r["predicted"]],
    )
    if full:
        section(
            "Computed against predicted",
            {Status.OK, Status.MISMATCH},
            ["task", "computed", "predicted", "agrees", "method", "wall (s)", "peak (MB)"],
            lambda r: [
                _name(r),
                r["value"],
                r["predicted"],
                r["agrees"],
                r["detail"].get("method"),
                r["wall_seconds"],
                r["peak_rss_mb"],
            ],
        )
    else:
        slowest = sorted(
            (r for r in records if r["status"] in {Status.OK, Status.MISMATCH}),
            key=lambda r: -r["wall_seconds"],
        )[:10]
        if slowest:
            lines += ["## Slowest computed tasks", ""]
            lines += _table(
                ["task", "cost", "wall (s)", "peak (MB)"],
                [[_name(r), r["task"].get("cost"), r["wall_seconds"], r["peak_rss_mb"]] for r in slowest],
            )
    if full:
        artifacts = []
        for record in records:
            detail = record.get("detail", {})
            for field in ("artifact_inputs", "artifact_outputs"):
                for name, ref in sorted(detail.get(field, {}).items()):
                    producer = ref.get("producer", record["task_id"])
                    attempt = ref.get("attempt_id", record.get("attempt_id"))
                    artifacts.append(
                        [
                            _name(record),
                            field.removeprefix("artifact_"),
                            name,
                            ref["digest"],
                            producer,
                            attempt,
                            record.get("resource_controls", {}).get("mode"),
                        ]
                    )
        if artifacts:
            lines += ["## Artifacts", ""]
            lines += _table(
                ["task", "use", "name", "digest", "producer", "source attempt", "memory control"], artifacts
            )
        evidence = [
            [_name(record), record["detail"]["evidence"], record["task"].get("prediction")]
            for record in records
            if record.get("detail", {}).get("evidence")
        ]
        if evidence:
            lines += ["## Mathematical evidence", ""]
            lines += _table(["task", "evidence", "prediction"], evidence)
    resources = []
    for record in records:
        estimate = record.get("resource_estimate")
        if estimate:
            for trial in record.get("resource_attempts", []):
                effective = trial["resource_controls"].get("effective_job")
                resources.append(
                    [
                        _name(record),
                        trial["trial_id"],
                        trial["status"],
                        estimate["basis"],
                        trial["limits"],
                        effective or trial["resource_controls"]["mode"],
                        trial["decision"],
                    ]
                )
    if resources:
        lines += ["## Resource estimates and retries", ""]
        lines += _table(["task", "trial", "status", "basis", "requested", "effective", "decision"], resources)
    return "\n".join(lines).rstrip() + "\n"


def _log_path(record: dict[str, Any]) -> str | None:
    log: str | None = record.get("log")
    directory = record.get("log_directory")
    if log and isinstance(directory, str):
        return str(Path(directory) / log)
    return log


def _provenance(records: list[dict[str, Any]], unreadable: int) -> list[str]:
    def distinct(pick: Any) -> str:
        values = sorted({str(value) for value in map(pick, records) if value is not None})
        return ", ".join(values) if values else "unknown"

    lines = [
        f"- records: {len(records)}",
        f"- code: {distinct(lambda r: r.get('code', {}).get('commit'))}",
        f"- runner: {distinct(lambda r: _cell(r.get('runner')) or None)}",
        f"- wall time of all tasks: {sum(r['wall_seconds'] for r in records):.0f} s",
    ]
    if any(r.get("code", {}).get("dirty") for r in records):
        lines.append("- some records come from a working tree with uncommitted changes")
    if unreadable:
        lines.append(f"- {unreadable} unreadable line(s) in results.jsonl were ignored")
    return [*lines, ""]
