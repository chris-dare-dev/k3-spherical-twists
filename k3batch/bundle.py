"""Export and verify a pinned run and its mathematical artifacts."""

from __future__ import annotations

import json
import tempfile
from collections.abc import Iterable
from hashlib import sha256
from pathlib import Path
from typing import Any, cast

from . import report
from .artifacts import (
    ArtifactError,
    ArtifactReference,
    ArtifactStore,
    artifact_digest,
    artifact_references,
    check_artifact_references,
    model_digest,
    read_artifact_json,
)
from .identity import RECORD_SCHEMA
from .record import Record
from .sqlite_store import SQLiteStore
from .wire import unique_object

BUNDLE_VERSION = 1
RUN_FILES = ("manifest.json", "results.jsonl")


class BundleError(ValueError):
    """A portable run has incomplete or inconsistent contents."""


def _references(record: Record, field: str) -> dict[str, dict[str, Any]]:
    detail = record.get("detail", {})
    refs = detail.get(field, {}) if isinstance(detail, dict) else None
    if not isinstance(refs, dict) or not all(isinstance(ref, dict) for ref in refs.values()):
        raise BundleError(f"invalid {field} for {record['task_id']}")
    return refs


def _copy_artifacts(records: Iterable[Record], store: ArtifactStore, objects: Path) -> None:
    pending = [
        artifact_digest(ref.get("digest"))
        for record in records
        for field in ("artifact_inputs", "artifact_outputs")
        for ref in _references(record, field).values()
    ]
    if pending and not store.database.is_file():
        raise ArtifactError(f"no artifact registry at {store.database}")
    copied: set[str] = set()
    while pending:
        digest = pending.pop()
        if digest in copied:
            continue
        body = store.read(digest)
        data = read_artifact_json(body)
        (objects / f"{digest}.json").write_bytes(body)
        copied.add(digest)
        pending.extend(ref for _, ref, _, _ in artifact_references(data))


def export_run(store: SQLiteStore, run_dir: Path, destination: Path, *, run_id: str | None = None) -> None:
    """Publish a directory containing exactly the selected run and its referenced artifact closure."""
    if destination.exists() or destination.is_symlink():
        raise FileExistsError(f"bundle destination already exists: {destination}")
    manifest, records = report.select(store, run_dir, run_id=run_id)
    if manifest.get("schema_version") != RECORD_SCHEMA:
        raise ValueError("a pinned run with a versioned manifest is required")
    artifacts = ArtifactStore(store.path.with_suffix(store.path.suffix + ".artifacts"))
    destination.parent.mkdir(parents=True, exist_ok=True)

    def encode(value: object) -> bytes:
        return (json.dumps(value, ensure_ascii=False, allow_nan=False) + "\n").encode("utf-8")

    with tempfile.TemporaryDirectory(prefix=".k3batch-export-", dir=destination.parent) as scratch:
        staged = Path(scratch) / "bundle"
        objects = staged / "objects"
        objects.mkdir(parents=True)
        _copy_artifacts(records.values(), artifacts, objects)
        files = {
            "manifest.json": encode(manifest),
            "results.jsonl": b"".join(encode(record) for record in records.values()),
        }
        for name, content in files.items():
            (staged / name).write_bytes(content)
        (staged / "bundle.json").write_bytes(
            encode(
                {
                    "version": BUNDLE_VERSION,
                    "title": run_dir.name,
                    "unreadable_lines": store.unreadable_lines,
                    "files": {name: sha256(content).hexdigest() for name, content in files.items()},
                }
            )
        )
        staged.rename(destination)


def _checked_bytes(path: Path, digest: object) -> bytes:
    expected = artifact_digest(digest)
    try:
        content = path.read_bytes()
    except FileNotFoundError:
        raise BundleError(f"missing bundle file {path.name}") from None
    if sha256(content).hexdigest() != expected:
        raise BundleError(f"bundle file {path.name} failed digest verification")
    return content


def _object(text: bytes, label: str) -> dict[str, Any]:
    data = json.loads(text, object_pairs_hook=unique_object)
    if not isinstance(data, dict):
        raise BundleError(f"expected a JSON object in {label}")
    return data


def _selected_records(manifest: dict[str, Any], body: bytes) -> dict[str, Record]:
    tasks = manifest.get("tasks")
    if (
        type(manifest.get("schema_version")) is not int
        or manifest["schema_version"] != RECORD_SCHEMA
        or not isinstance(manifest.get("run_id"), str)
        or not isinstance(tasks, list)
    ):
        raise BundleError("invalid pinned manifest")
    members = {}
    for task in tasks:
        if not isinstance(task, dict) or not all(
            isinstance(task.get(key), str) and task[key]
            for key in ("id", "kind", "record_id", "computation_id", "check_id")
        ):
            raise BundleError("invalid member in pinned manifest")
        if task["id"] in members or not isinstance(task.get("check"), dict):
            raise BundleError(f"invalid or duplicate manifest member {task['id']}")
        members[task["id"]] = task

    selected: dict[str, Record] = {}
    for line in body.split(b"\n"):
        if not line.strip():
            continue
        record = _object(line, "results.jsonl")
        task_id = record.get("task_id")
        if not isinstance(task_id, str):
            raise BundleError("pinned result has no task ID")
        member = members.get(task_id)
        if (
            member is None
            or task_id in selected
            or record.get("task") != member
            or any(record.get(key) != member[key] for key in ("record_id", "computation_id", "check_id"))
            or any(key not in record or record[key] != value for key, value in member["check"].items())
        ):
            raise BundleError(f"result {task_id!r} does not match a unique pinned manifest member")
        selected[task_id] = cast(Record, record)
    if manifest.get("run_state") == "completed" and selected.keys() != members.keys():
        raise BundleError("completed run has missing pinned results")
    return selected


def _check_artifacts(directory: Path, records: dict[str, Record]) -> None:
    identities: dict[str, tuple[str, str | None]] = {}
    pending: list[tuple[ArtifactReference, ...]] = []

    def identify(digest: str) -> tuple[str, str | None]:
        if digest not in identities:
            content = _checked_bytes(directory / "objects" / f"{digest}.json", digest)
            data = read_artifact_json(content)
            identities[digest] = (data["kind"], model_digest(data))
            pending.append(tuple(artifact_references(data)))
        return identities[digest]

    outputs = {task_id: _references(record, "artifact_outputs") for task_id, record in records.items()}
    for task_id, record in records.items():
        graph = record["task"].get("graph", {})
        for name, ref in outputs[task_id].items():
            kind, _ = identify(artifact_digest(ref.get("digest")))
            if ref.get("kind") != kind or (graph and graph["outputs"].get(name) != kind):
                raise BundleError(f"{task_id} output {name} has an inconsistent artifact kind")
        inputs = _references(record, "artifact_inputs")
        for name, ref in inputs.items():
            kind, model = identify(artifact_digest(ref.get("digest")))
            contract = graph.get("inputs", {}).get(name, {})
            producer_id = contract.get("producer")
            producer = records.get(producer_id)
            source = outputs.get(producer_id, {}).get(contract.get("output"), {})
            if (
                producer is None
                or producer_id != ref.get("producer")
                or producer.get("record_id") != ref.get("record_id")
                or not isinstance(ref.get("attempt_id"), str)
                or producer.get("attempt_id") != ref["attempt_id"]
                or contract.get("record_id") != ref.get("record_id")
                or contract.get("kind") != kind
                or source.get("digest") != ref.get("digest")
                or source.get("kind") != kind
            ):
                raise BundleError(f"{task_id} input {name} disagrees with its pinned producer")
            parent = contract.get("model_input")
            if parent is not None and (parent not in inputs or model != inputs[parent].get("digest")):
                raise BundleError(f"{task_id} input {name} has an inconsistent model reference")
    while pending:
        check_artifact_references(pending.pop(), identify)


def verify_run(directory: Path, *, full: bool = False) -> str:
    """Verify a portable run offline and render its report."""
    index = _object((directory / "bundle.json").read_bytes(), "bundle.json")
    files = index.get("files")
    unreadable = index.get("unreadable_lines")
    title = index.get("title")
    if (
        type(index.get("version")) is not int
        or index["version"] != BUNDLE_VERSION
        or not isinstance(files, dict)
        or files.keys() != set(RUN_FILES)
        or not isinstance(title, str)
        or type(unreadable) is not int
        or unreadable < 0
    ):
        raise BundleError("invalid or unsupported bundle index")
    manifest_bytes, records_bytes = (_checked_bytes(directory / name, files[name]) for name in RUN_FILES)
    manifest = _object(manifest_bytes, "manifest.json")
    records = _selected_records(manifest, records_bytes)
    try:
        _check_artifacts(directory, records)
        return report.tables(title, manifest, records, full=full, unreadable=unreadable)
    except (AttributeError, KeyError, TypeError) as problem:
        raise BundleError(f"invalid pinned result data: {problem}") from problem
