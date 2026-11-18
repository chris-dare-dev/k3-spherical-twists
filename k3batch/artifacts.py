"""Immutable mathematical artifacts and their registered producers."""

from __future__ import annotations

import json
import os
import re
import sqlite3
import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from hashlib import sha256
from pathlib import Path
from typing import Any

from .wire import _unique_object

VERSION = 1
MODEL = "k3-model"
PAYLOAD_FIELDS = {
    MODEL: {"parameters", "coordinates", "grading", "equations", "markings"},
    "graded-presentation": {"model_digest", "source", "target", "matrix"},
    "graded-complex": {"model_digest", "base", "terms", "differentials"},
}


class ArtifactError(ValueError):
    """Invalid, unavailable, or damaged artifact."""


def _digest(value: object) -> str:
    if not isinstance(value, str) or not re.fullmatch("[0-9a-f]{64}", value):
        raise ArtifactError("expected a lowercase SHA-256 digest")
    return value


def _describe(data: Any) -> tuple[str, str | None]:
    if not isinstance(data, dict) or set(data) != {"version", "kind", "payload"}:
        raise ArtifactError("invalid artifact envelope")
    if type(data["version"]) is not int or data["version"] != VERSION:
        raise ArtifactError("unknown artifact version")
    kind = data["kind"]
    if not isinstance(kind, str) or kind not in PAYLOAD_FIELDS:
        raise ArtifactError("unknown artifact kind")
    payload = data["payload"]
    if not isinstance(payload, dict) or set(payload) != PAYLOAD_FIELDS[kind]:
        raise ArtifactError(f"invalid {kind} payload fields")
    return kind, None if kind == MODEL else _digest(payload["model_digest"])


def read_artifact_json(body: bytes) -> dict[str, Any]:
    data = json.loads(body.decode("utf-8"), object_pairs_hook=_unique_object)
    _describe(data)
    assert isinstance(data, dict)
    return data


def _canonical(data: dict[str, Any]) -> bytes:
    return (json.dumps(data, sort_keys=True, separators=(",", ":"), allow_nan=False) + "\n").encode("utf-8")


class ArtifactStore:
    """A blob becomes available only after its file and registry row are durable."""

    def __init__(self, root: Path) -> None:
        self.objects = root / "objects"
        self.database = root / "artifacts.sqlite3"

    @contextmanager
    def _connect(self) -> Iterator[sqlite3.Connection]:
        self.objects.mkdir(parents=True, exist_ok=True)
        connection = sqlite3.connect(self.database, timeout=30)
        try:
            with connection:
                connection.execute("PRAGMA foreign_keys = ON")
                connection.execute("PRAGMA synchronous = FULL")
                connection.execute("""
                    CREATE TABLE IF NOT EXISTS artifact (
                        digest TEXT PRIMARY KEY,
                        size INTEGER NOT NULL,
                        version INTEGER NOT NULL,
                        kind TEXT NOT NULL,
                        model_digest TEXT REFERENCES artifact(digest)
                    )
                """)
                connection.execute("""
                    CREATE TABLE IF NOT EXISTS producer (
                        digest TEXT NOT NULL REFERENCES artifact(digest),
                        attempt TEXT NOT NULL,
                        PRIMARY KEY (digest, attempt)
                    )
                """)
                yield connection
        finally:
            connection.close()

    def publish(self, data: dict[str, Any], producer: str) -> str:
        if not isinstance(producer, str) or not producer.strip():
            raise ArtifactError("producer must identify a nonempty run or attempt")
        kind, model = _describe(data)
        body = _canonical(data)
        digest = sha256(body).hexdigest()
        with self._connect() as connection:
            if model is not None:
                self._require_model(connection, model)
            self._publish_file(digest, body)
            connection.execute(
                "INSERT INTO artifact VALUES (?, ?, ?, ?, ?) ON CONFLICT(digest) DO NOTHING",
                (digest, len(body), VERSION, kind, model),
            )
            connection.execute(
                "INSERT INTO producer VALUES (?, ?) ON CONFLICT(digest, attempt) DO NOTHING",
                (digest, producer),
            )
        return digest

    def _publish_file(self, digest: str, body: bytes) -> None:
        destination = self.objects / f"{digest}.json"
        with tempfile.NamedTemporaryFile(dir=self.objects, prefix=".part-", delete=False) as handle:
            stage = Path(handle.name)
            try:
                handle.write(body)
                handle.flush()
                os.fsync(handle.fileno())
                if sha256(stage.read_bytes()).hexdigest() != digest:
                    raise ArtifactError("staged artifact failed digest verification")
                try:
                    os.link(stage, destination)
                except FileExistsError:
                    if destination.read_bytes() != body:
                        raise ArtifactError(
                            f"existing artifact {digest} failed digest verification"
                        ) from None
            finally:
                stage.unlink(missing_ok=True)
        directory = os.open(self.objects, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)

    def _read(self, connection: sqlite3.Connection, digest: str) -> tuple[bytes, str, str | None]:
        row = connection.execute(
            "SELECT size, version, kind, model_digest FROM artifact WHERE digest = ?", (digest,)
        ).fetchone()
        if row is None:
            raise ArtifactError(f"artifact {digest} is not registered")
        try:
            body = (self.objects / f"{digest}.json").read_bytes()
        except FileNotFoundError:
            raise ArtifactError(f"registered artifact {digest} has no file") from None
        if len(body) != row[0] or sha256(body).hexdigest() != digest:
            raise ArtifactError(f"artifact {digest} failed digest verification")
        kind, model = _describe(read_artifact_json(body))
        if row[1:] != (VERSION, kind, model):
            raise ArtifactError(f"artifact {digest} disagrees with its registry metadata")
        return body, kind, model

    def _require_model(self, connection: sqlite3.Connection, digest: str) -> None:
        _, kind, _ = self._read(connection, digest)
        if kind != MODEL:
            raise ArtifactError(f"artifact {digest} is not a K3 model")

    def read(self, digest: str) -> bytes:
        """Verify the registered artifact and its model before returning canonical JSON."""
        with self._connect() as connection:
            body, _, model = self._read(connection, _digest(digest))
            if model is not None:
                self._require_model(connection, model)
        return body
