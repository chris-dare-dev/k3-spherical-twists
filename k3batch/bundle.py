"""Export a pinned run and the mathematical artifacts needed to inspect it."""

from __future__ import annotations

import json
import tempfile
from collections.abc import Iterable
from hashlib import sha256
from pathlib import Path

from . import report
from .artifacts import CHAIN_MAP, ENDPOINTS, ArtifactError, ArtifactStore, model_digest, read_artifact_json
from .identity import RECORD_SCHEMA
from .record import Record
from .sqlite_store import SQLiteStore


def _copy_artifacts(records: Iterable[Record], store: ArtifactStore, objects: Path) -> None:
    pending = [
        ref["digest"]
        for record in records
        for field in ("artifact_inputs", "artifact_outputs")
        for ref in record.get("detail", {}).get(field, {}).values()
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
        parent = model_digest(data)
        if parent is not None:
            pending.append(parent)
        if data["kind"] == CHAIN_MAP:
            pending.extend(data["payload"][endpoint] for endpoint in ENDPOINTS)


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
                    "version": 1,
                    "title": run_dir.name,
                    "unreadable_lines": store.unreadable_lines,
                    "files": {name: sha256(content).hexdigest() for name, content in files.items()},
                }
            )
        )
        staged.rename(destination)
