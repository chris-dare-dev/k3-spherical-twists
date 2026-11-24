"""Immutable mathematical artifacts and their registered producers."""

from __future__ import annotations

import json
import os
import re
import sqlite3
import tempfile
from collections.abc import Callable, Iterable, Iterator
from contextlib import contextmanager
from hashlib import sha256
from pathlib import Path
from typing import Any

from ..runner import unique_object

MODEL = "k3-model"
COMPLEX = "graded-complex"
CHAIN_MAP = "graded-chain-map"
ENDPOINTS = ("source_digest", "target_digest")
ArtifactReference = tuple[str, str, str, str | None]
PAYLOAD_FIELDS = {
    MODEL: {"parameters", "coordinates", "grading", "equations", "markings"},
    "graded-presentation": {"model_digest", "source", "target", "matrix"},
    COMPLEX: {"model_digest", "base", "terms", "differentials"},
    CHAIN_MAP: {"model_digest", *ENDPOINTS, "components"},
}


class ArtifactError(ValueError):
    """Invalid, unavailable, or damaged artifact."""


def artifact_digest(value: object) -> str:
    """Validate a content digest before using it as an object name."""
    if not isinstance(value, str) or not re.fullmatch("[0-9a-f]{64}", value):
        raise ArtifactError("expected a lowercase SHA-256 digest")
    return value


def _describe(data: Any) -> tuple[int, str, str | None]:
    if not isinstance(data, dict) or set(data) != {"version", "kind", "payload"}:
        raise ArtifactError("invalid artifact envelope")
    kind = data["kind"]
    if not isinstance(kind, str) or kind not in PAYLOAD_FIELDS:
        raise ArtifactError("unknown artifact kind")
    version = data["version"]
    if type(version) is not int or version not in ((1, 2) if kind == COMPLEX else (1,)):
        raise ArtifactError("unknown artifact version")
    payload = data["payload"]
    if not isinstance(payload, dict) or set(payload) != PAYLOAD_FIELDS[kind]:
        raise ArtifactError(f"invalid {kind} payload fields")
    if kind == CHAIN_MAP:
        for endpoint in ENDPOINTS:
            artifact_digest(payload[endpoint])
    return version, kind, None if kind == MODEL else artifact_digest(payload["model_digest"])


def read_artifact_json(body: bytes) -> dict[str, Any]:
    data = json.loads(body.decode("utf-8"), object_pairs_hook=unique_object)
    _describe(data)
    assert isinstance(data, dict)
    return data


def model_digest(data: dict[str, Any]) -> str | None:
    """The model an artifact is bound to; None for a model, which is bound to nothing."""
    return _describe(data)[2]


def artifact_references(data: dict[str, Any]) -> Iterator[ArtifactReference]:
    """Yield the field, digest, kind, and model required for each direct reference."""
    model = model_digest(data)
    if model is not None:
        yield "model_digest", model, MODEL, None
    if data["kind"] == CHAIN_MAP:
        for key in ENDPOINTS:
            yield key, data["payload"][key], COMPLEX, model


def check_artifact_references(
    references: Iterable[ArtifactReference],
    identify: Callable[[str], tuple[str, str | None]],
) -> None:
    """Check reference kinds and model binding against a registry or an offline reader."""
    for field, digest, kind, model in references:
        if identify(digest) != (kind, model):
            if field == "model_digest":
                raise ArtifactError(f"artifact {digest} is not a K3 model")
            raise ArtifactError(f"chain map {field} must name a graded complex over its model")


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
        version, kind, model = _describe(data)
        body = _canonical(data)
        digest = sha256(body).hexdigest()
        with self._connect() as connection:
            self._require_references(connection, data)
            self._publish_file(digest, body)
            connection.execute(
                "INSERT INTO artifact VALUES (?, ?, ?, ?, ?) ON CONFLICT(digest) DO NOTHING",
                (digest, len(body), version, kind, model),
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

    def _read(self, connection: sqlite3.Connection, digest: str) -> tuple[bytes, dict[str, Any], str | None]:
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
        data = read_artifact_json(body)
        version, kind, model = _describe(data)
        if row[1:] != (version, kind, model):
            raise ArtifactError(f"artifact {digest} disagrees with its registry metadata")
        return body, data, model

    def _require_references(self, connection: sqlite3.Connection, data: dict[str, Any]) -> None:
        def identify(digest: str) -> tuple[str, str | None]:
            _, referenced, model = self._read(connection, digest)
            return referenced["kind"], model

        check_artifact_references(artifact_references(data), identify)

    def publish_outputs(
        self, staged: Any, declared: dict[str, str], producer: str
    ) -> dict[str, dict[str, str]]:
        """Publish what a task returned, under the names and kinds declared for it.

        Returns the reference to each artifact that the record of the task keeps.
        """
        if not isinstance(staged, dict) or staged.keys() != declared.keys():
            raise ArtifactError("returned artifact names must match the graph declaration")
        for name, kind in declared.items():
            data = staged[name]
            if not isinstance(data, dict) or data.get("kind") != kind:
                raise ArtifactError(f"output {name} must be a {kind} artifact")
        prepared = dict(staged)
        for name, kind in declared.items():
            if kind == CHAIN_MAP:
                prepared[name] = self._bind_map_outputs(staged[name], staged, declared)
        # The map's referenced complexes must be durable before the map is registered.
        ordered = sorted(declared, key=lambda name: declared[name] == CHAIN_MAP)
        return {
            name: {"kind": declared[name], "digest": self.publish(prepared[name], producer)}
            for name in ordered
        }

    @staticmethod
    def _bind_map_outputs(
        data: dict[str, Any], staged: dict[str, Any], declared: dict[str, str]
    ) -> dict[str, Any]:
        payload = data.get("payload")
        names = ("source_output", "target_output")
        if not isinstance(payload, dict) or not any(name in payload for name in names):
            return data
        if set(payload) != {"model_digest", "components", *names}:
            raise ArtifactError("staged chain maps require both endpoint output names")
        payload = dict(payload)
        for name, digest_key in zip(names, ENDPOINTS, strict=True):
            endpoint = payload.pop(name)
            if not isinstance(endpoint, str) or declared.get(endpoint) != COMPLEX:
                raise ArtifactError(f"chain map {name} must name a graded-complex sibling output")
            payload[digest_key] = sha256(_canonical(staged[endpoint])).hexdigest()
        return data | {"payload": payload}

    def output(self, reference: Any, name: str, kind: str) -> dict[str, Any]:
        """Read the artifact a record refers to as its output `name`, of the kind its reader declared."""
        if not isinstance(reference, dict) or reference.get("kind") != kind:
            raise ArtifactError(f"missing {kind} artifact {name}")
        digest = reference.get("digest")
        if not isinstance(digest, str):
            raise ArtifactError(f"missing digest for artifact {name}")
        data = read_artifact_json(self.read(digest))
        if data["kind"] != kind:
            raise ArtifactError(f"artifact {name} has kind {data['kind']}, expected {kind}")
        return {"digest": digest, "data": data}

    def read(self, digest: str) -> bytes:
        """Verify the registered artifact and its references before returning canonical JSON."""
        with self._connect() as connection:
            body, data, _ = self._read(connection, artifact_digest(digest))
            self._require_references(connection, data)
        return body
