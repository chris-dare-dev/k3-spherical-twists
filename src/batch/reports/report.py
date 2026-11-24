"""Tables from the records of a batch: computed against predicted, mismatches, timeouts, kills.

`select` asks a store for the records of a run; `tables` writes the report from them and reads nothing.
"""

from __future__ import annotations

from collections import Counter, defaultdict
from collections.abc import Callable, Collection
from pathlib import Path
from typing import Any

from ..records import RECORD_SCHEMA, Record, ResultStore, RunHistory, commit, log_path
from ..tasks import Status

NOT_RUN = "not run"
Row = Callable[[Record], list[Any]]
COLUMNS = [str(status) for status in Status] + [NOT_RUN]


def cell(value: Any) -> str:
    """A value as it appears in a table cell."""
    if value is None:
        return ""
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, dict):
        return ", ".join(f"{key} {cell(item)}" for key, item in value.items())
    if isinstance(value, list):
        return "(" + ", ".join(cell(item) for item in value) + ")"
    if isinstance(value, float):
        return f"{value:g}"
    return str(value).replace("|", "\\|")


def _table(header: list[str], rows: list[list[Any]]) -> list[str]:
    lines = ["| " + " | ".join(header) + " |", "|" + "---|" * len(header)]
    lines += ["| " + " | ".join(cell(item) for item in row) + " |" for row in rows]
    return [*lines, ""]


def _name(record: Record) -> str:
    return f"`{record['task_id']}`"


def selected_results(store: RunHistory, manifest: dict[str, Any]) -> dict[str, Record]:
    """Resolve the attempts pinned by the manifest of a versioned run."""
    if "schema_version" not in manifest:
        raise RuntimeError("a versioned manifest is required for a pinned run")
    if manifest["schema_version"] != RECORD_SCHEMA:
        raise RuntimeError(f"unsupported manifest schema version: {manifest['schema_version']}")

    attempts = store.by_record_id([task["record_id"] for task in manifest["tasks"]])
    selected: dict[str, Record] = {}
    for task in manifest["tasks"]:
        attempt = attempts.get(task["record_id"])
        if attempt is None or attempt.get("computation_id") != task["computation_id"]:
            continue
        # the record as this run reads it: under the run's own check, and as a member of the run
        chosen: Any = {
            **attempt,
            **task["check"],
            "task": task,
            "task_id": task["id"],
            "check_id": task["check_id"],
        }
        selected[task["id"]] = chosen
    return selected


def select(
    store: RunHistory, run_dir: Path, *, run_id: str | None = None, legacy: bool = False
) -> tuple[dict[str, Any], dict[str, Record]]:
    """The manifest of the selected run of a directory, and the record that answers each of its tasks."""
    manifest = store.manifest(run_dir, run_id, legacy=legacy)
    if "schema_version" in manifest:
        return manifest, selected_results(store, manifest)
    # records from before versioned runs are found by the label of their task
    return manifest, store.unpinned(run_dir, legacy=legacy)


def summary(manifest: dict[str, Any], selected: dict[str, Record]) -> dict[str, Counter[str]]:
    """How the tasks of each group ended; a task of the manifest without a record counts as not run."""
    groups: dict[str, Counter[str]] = defaultdict(Counter)
    known = set()
    for task in manifest.get("tasks", []):
        known.add(task["id"])
        record = selected.get(task["id"])
        groups[task.get("group", task["kind"])][record["status"] if record else NOT_RUN] += 1
    for task_id, record in selected.items():
        if task_id not in known:
            groups[record["task"].get("group", record["task"].get("kind", "?"))][record["status"]] += 1
    return dict(groups)


def render(
    run_dir: Path,
    *,
    full: bool = False,
    run_id: str | None = None,
    legacy: bool = False,
    store: RunHistory | None = None,
) -> str:
    """The report for a selected run, as Markdown."""
    store = store or ResultStore(run_dir / "results.jsonl")
    manifest, selected = select(store, run_dir, run_id=run_id, legacy=legacy)
    return tables(
        run_dir.name, manifest, selected, full=full, legacy=legacy, unreadable=store.unreadable_lines
    )


def tables(
    title: str,
    manifest: dict[str, Any],
    selected: dict[str, Record],
    *,
    full: bool = False,
    legacy: bool = False,
    unreadable: int = 0,
) -> str:
    """The report of a run from its manifest and the records selected for it."""
    groups = summary(manifest, selected)
    records = sorted(selected.values(), key=lambda r: (r["task"].get("group", ""), r["task_id"]))

    lines = [f"# Results in {title}", ""]
    if legacy:
        lines.append("- selection: unversioned historical records")
    if "run_id" in manifest:
        lines.append(f"- run: `{manifest['run_id']}`")
    if "run_state" in manifest:
        lines.append(f"- run state: {manifest['run_state']}")
    lines += _provenance(records, unreadable)

    lines += ["## Summary", ""]
    used = [column for column in COLUMNS if any(counts[column] for counts in groups.values())]
    lines += _table(
        ["group", "tasks", *used],
        [
            [group, counts.total(), *(counts[column] for column in used)]
            for group, counts in sorted(groups.items())
        ],
    )

    def section(heading: str, statuses: Collection[str], header: list[str], row: Row) -> None:
        chosen = [record for record in records if record["status"] in statuses]
        if chosen:
            lines.extend([f"## {heading}", ""])
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
        lambda r: [_name(r), r["status"], (r["error"] or "").replace("\n", "; "), log_path(r)],
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


def _provenance(records: list[Record], unreadable: int) -> list[str]:
    def distinct(pick: Callable[[Record], Any]) -> str:
        values = sorted({str(value) for value in map(pick, records) if value is not None})
        return ", ".join(values) if values else "unknown"

    lines = [
        f"- records: {len(records)}",
        f"- code: {distinct(commit)}",
        f"- runner: {distinct(lambda r: cell(r.get('runner')) or None)}",
        f"- wall time of all tasks: {sum(r['wall_seconds'] for r in records):.0f} s",
    ]
    if any(r.get("code", {}).get("dirty") for r in records):
        lines.append("- some records come from a working tree with uncommitted changes")
    if unreadable:
        lines.append(f"- {unreadable} unreadable line(s) in results.jsonl were ignored")
    return [*lines, ""]
