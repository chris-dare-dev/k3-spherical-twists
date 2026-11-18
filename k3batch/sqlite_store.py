"""A transactional run ledger backed by a local SQLite database."""

from __future__ import annotations

import hashlib
import json
import os
import sqlite3
from collections import Counter
from collections.abc import Iterator, Sequence
from contextlib import contextmanager
from datetime import UTC, datetime
from pathlib import Path
from typing import Any

from .identity import RECORD_SCHEMA
from .store import ResultStore, lock_writer

_APPLICATION_ID = 0x4B334254  # K3BT
_VERSION = 1
_SCHEMA = """
CREATE TABLE runs (
    seq INTEGER PRIMARY KEY,
    run_id TEXT NOT NULL UNIQUE,
    directory TEXT NOT NULL,
    manifest TEXT,
    metadata TEXT,
    state TEXT NOT NULL CHECK (state IN ('running', 'completed', 'interrupted', 'failed', 'imported')),
    started_at TEXT,
    ended_at TEXT
);
CREATE INDEX runs_directory ON runs(directory, started_at DESC, seq DESC);
CREATE TABLE members (
    run_id TEXT NOT NULL REFERENCES runs(run_id),
    position INTEGER NOT NULL,
    task_id TEXT NOT NULL,
    record_id TEXT,
    member TEXT NOT NULL,
    PRIMARY KEY (run_id, position),
    UNIQUE (run_id, task_id)
);
CREATE TABLE attempts (
    seq INTEGER PRIMARY KEY,
    attempt_id TEXT UNIQUE,
    record_id TEXT UNIQUE,
    computation_id TEXT,
    check_id TEXT,
    run_id TEXT,
    task_id TEXT NOT NULL,
    state TEXT NOT NULL CHECK (state IN ('running', 'finished', 'interrupted')),
    started_at TEXT,
    ended_at TEXT,
    log TEXT,
    directory TEXT NOT NULL,
    log_directory TEXT NOT NULL,
    surface TEXT,
    method TEXT,
    code_commit TEXT,
    result TEXT,
    import_key TEXT UNIQUE
);
CREATE INDEX attempts_computation ON attempts(computation_id, started_at DESC, seq DESC)
    WHERE result IS NOT NULL;
CREATE INDEX attempts_run ON attempts(run_id);
CREATE INDEX attempts_directory ON attempts(directory);
CREATE INDEX attempts_surface ON attempts(surface);
CREATE INDEX attempts_method ON attempts(method);
CREATE INDEX attempts_commit ON attempts(code_commit);
CREATE TABLE imports (
    directory TEXT PRIMARY KEY,
    manifest TEXT NOT NULL,
    unreadable INTEGER NOT NULL
);
"""


def _json(value: Any) -> str:
    # Store large exact integers as JSON text, independent of SQLite's 64-bit integer storage.
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def _object(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def _decode(value: str | None) -> dict[str, Any]:
    return _object(json.loads(value)) if value is not None else {}


def _string(value: Any) -> str | None:
    return value if isinstance(value, str) and value else None


def _now() -> str:
    return datetime.now(UTC).isoformat(timespec="seconds")


def _placeholders(count: int) -> str:
    return ",".join("?" for _ in range(count))


def _chunks(values: Sequence[str]) -> Iterator[Sequence[str]]:
    for index in range(0, len(values), 500):
        yield values[index : index + 500]


def _record_identity(record: dict[str, Any]) -> tuple[str | None, str | None, str | None]:
    if record.get("schema_version") != RECORD_SCHEMA:
        return None, None, None
    return (
        _string(record.get("record_id")),
        _string(record.get("computation_id")),
        _string(record.get("check_id")),
    )


def _indexes(record: dict[str, Any]) -> tuple[str | None, str | None, str | None]:
    surface = _object(record.get("task")).get("surface")
    return (
        _json(surface) if surface is not None else None,
        _string(_object(record.get("detail")).get("method")),
        _string(_object(record.get("code")).get("commit")),
    )


def _result(row: sqlite3.Row) -> dict[str, Any]:
    value = _decode(row["result"])
    # The run selected for reporting can differ from the attempt that produced the log.
    value.setdefault("log_directory", row["log_directory"])
    return value


def _check_schema(db: sqlite3.Connection) -> None:
    app_id = db.execute("PRAGMA application_id").fetchone()[0]
    version = db.execute("PRAGMA user_version").fetchone()[0]
    if app_id != _APPLICATION_ID or version != _VERSION:
        raise RuntimeError(f"unsupported k3batch database format (application {app_id}, schema {version})")


class SQLiteStore:
    """Own one writing coordinator, with transactional updates and concurrent read snapshots."""

    def __init__(self, path: Path) -> None:
        self.path = path.resolve()
        self.unreadable_lines = 0
        self._db: sqlite3.Connection | None = None
        self._lock_fd: int | None = None

    def __enter__(self) -> SQLiteStore:
        if self._lock_fd is not None:
            raise RuntimeError("the results database is already open for writing")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock_fd = lock_writer(self.path)
        try:
            self._db = sqlite3.connect(self.path, isolation_level=None)
            self._db.row_factory = sqlite3.Row
            self._db.execute("PRAGMA foreign_keys = ON")
            if (
                self._db.execute("PRAGMA application_id").fetchone()[0] == 0
                and self._db.execute("PRAGMA user_version").fetchone()[0] == 0
                and not self._db.execute("SELECT name FROM sqlite_master LIMIT 1").fetchone()
            ):
                self._db.executescript(
                    f"BEGIN IMMEDIATE;\n{_SCHEMA}\nPRAGMA application_id = {_APPLICATION_ID};\n"
                    f"PRAGMA user_version = {_VERSION};\nCOMMIT;"
                )
            _check_schema(self._db)
            if self._db.execute("PRAGMA journal_mode = WAL").fetchone()[0] != "wal":
                raise RuntimeError("the results database needs SQLite WAL support on local storage")
            self._db.execute("PRAGMA synchronous = FULL")
            with self._write() as db:
                # Acquiring the writer lock proves there is no active coordinator in this database.
                ended_at = _now()
                db.execute(
                    "UPDATE runs SET state = 'interrupted', ended_at = ? WHERE state = 'running'", (ended_at,)
                )
                db.execute(
                    "UPDATE attempts SET state = 'interrupted', ended_at = ? WHERE state = 'running'",
                    (ended_at,),
                )
            return self
        except BaseException:
            self.__exit__()
            raise

    def __exit__(self, *exc: object) -> None:
        try:
            if self._db is not None:
                self._db.close()
                self._db = None
        finally:
            if self._lock_fd is not None:
                os.close(self._lock_fd)
                self._lock_fd = None

    @contextmanager
    def _write(self) -> Iterator[sqlite3.Connection]:
        if self._db is None:
            raise RuntimeError("the results database is not open for writing")
        with self._db:
            self._db.execute("BEGIN IMMEDIATE")
            yield self._db

    @contextmanager
    def _read(self) -> Iterator[sqlite3.Connection | None]:
        if self._db is not None:
            yield self._db
        elif not self.path.exists():
            yield None
        else:
            db = sqlite3.connect(f"{self.path.as_uri()}?mode=ro", uri=True)
            db.row_factory = sqlite3.Row
            try:
                _check_schema(db)
                db.execute("BEGIN")
                yield db
            finally:
                db.close()

    @staticmethod
    def _insert_run(
        db: sqlite3.Connection,
        run_id: str,
        directory: str,
        manifest: dict[str, Any],
        metadata: dict[str, Any],
        state: str,
    ) -> None:
        header = {key: value for key, value in manifest.items() if key != "tasks"}
        db.execute(
            "INSERT INTO runs(run_id, directory, manifest, metadata, state, started_at)"
            " VALUES (?, ?, ?, ?, ?, ?)",
            (run_id, directory, _json(header), _json(metadata), state, _string(metadata.get("started_at"))),
        )
        db.executemany(
            "INSERT INTO members(run_id, position, task_id, record_id, member) VALUES (?, ?, ?, ?, ?)",
            (
                (run_id, index, task["id"], _string(task.get("record_id")), _json(task))
                for index, task in enumerate(manifest.get("tasks", []))
            ),
        )

    @contextmanager
    def run(self, run_dir: Path, manifest: dict[str, Any], metadata: dict[str, Any]) -> Iterator[None]:
        """Publish the immutable membership, then track the coordinator's terminal state."""
        run_id = manifest["run_id"]
        with self._write() as db:
            self._insert_run(db, run_id, str(run_dir.resolve()), manifest, metadata, "running")
        state = "failed"
        try:
            yield
            # A run can complete with scientific or resource failures. Each member still needs an outcome.
            with self._read() as db:
                assert db is not None
                missing = db.execute(
                    "SELECT 1 FROM members m LEFT JOIN attempts a ON a.record_id = m.record_id"
                    " WHERE m.run_id = ? AND a.result IS NULL LIMIT 1",
                    (run_id,),
                ).fetchone()
            if missing is not None:
                raise RuntimeError("cannot complete a run with missing outcomes")
            state = "completed"
        except KeyboardInterrupt:
            state = "interrupted"
            raise
        finally:
            ended_at = _now()
            with self._write() as db:
                db.execute(
                    "UPDATE runs SET state = ?, ended_at = ? WHERE run_id = ?", (state, ended_at, run_id)
                )
                db.execute(
                    "UPDATE attempts SET state = 'interrupted', ended_at = ? "
                    "WHERE run_id = ? AND state = 'running'",
                    (ended_at, run_id),
                )

    def start_attempt(
        self, run_id: str, member: dict[str, Any], attempt_id: str, started_at: str, log: str
    ) -> None:
        with self._write() as db:
            active = db.execute(
                "SELECT members.member, runs.directory FROM members JOIN runs USING (run_id) "
                "WHERE runs.state = 'running' AND run_id = ? AND task_id = ? AND record_id = ?",
                (run_id, member["id"], member["record_id"]),
            ).fetchone()
            if active is None:
                raise RuntimeError("attempt must belong to a task in an active run")
            if _decode(active["member"]) != member:
                raise RuntimeError("attempt does not match the pinned task definition")
            db.execute(
                "INSERT INTO attempts (attempt_id, record_id, computation_id, check_id, run_id, task_id,"
                " state, started_at, log, directory, log_directory)"
                " VALUES (?, ?, ?, ?, ?, ?, 'running', ?, ?, ?, ?)",
                (
                    attempt_id,
                    member["record_id"],
                    member["computation_id"],
                    member["check_id"],
                    run_id,
                    member["id"],
                    started_at,
                    log,
                    active["directory"],
                    active["directory"],
                ),
            )

    def append(self, record: dict[str, Any]) -> None:
        """Complete the attempt and record its observation, check and any output references atomically."""
        with self._write() as db:
            completed = db.execute(
                "UPDATE attempts SET state = 'finished', ended_at = ?, log = ?, surface = ?,"
                " method = ?, code_commit = ?, result = ?"
                " WHERE attempt_id = ? AND record_id = ? AND computation_id = ? AND check_id = ?"
                " AND task_id = ? AND run_id = ? AND state = 'running'",
                (
                    _now(),
                    record.get("log"),
                    *_indexes(record),
                    _json(record),
                    record["attempt_id"],
                    *_record_identity(record),
                    record["task_id"],
                    record["run_id"],
                ),
            )
            if completed.rowcount != 1:
                raise RuntimeError("result does not match a running attempt")

    def latest_by_computation(self, identities: Sequence[str]) -> dict[str, dict[str, Any]]:
        """Find the latest eligible result for each requested computation through the index."""
        with self._read() as db:
            if db is None:
                return {}
            return {
                row["computation_id"]: _result(row)
                for chunk in _chunks(tuple(dict.fromkeys(identities)))
                for row in db.execute(
                    "SELECT computation_id, result, log_directory FROM ("
                    " SELECT computation_id, result, log_directory,"
                    " ROW_NUMBER() OVER (PARTITION BY computation_id ORDER BY started_at DESC, seq DESC) rank"
                    " FROM attempts WHERE result IS NOT NULL AND record_id IS NOT NULL"
                    f" AND check_id IS NOT NULL AND computation_id IN ({_placeholders(len(chunk))})"
                    ") WHERE rank = 1",
                    chunk,
                )
            }

    def by_record_id(self, identities: Sequence[str]) -> dict[str, dict[str, Any]]:
        """Find the exact records reserved by run members."""
        with self._read() as db:
            if db is None:
                return {}
            return {
                row["record_id"]: _result(row)
                for chunk in _chunks(tuple(dict.fromkeys(identities)))
                for row in db.execute(
                    "SELECT record_id, result, log_directory FROM attempts"
                    f" WHERE result IS NOT NULL AND record_id IN ({_placeholders(len(chunk))})",
                    chunk,
                )
            }

    def manifest(
        self, run_dir: Path | None = None, run_id: str | None = None, *, legacy: bool = False
    ) -> dict[str, Any]:
        directory = str(run_dir.resolve()) if run_dir is not None else None
        with self._read() as db:
            if db is None:
                raise RuntimeError(f"no results database at {self.path}")
            if run_id is not None:
                run = db.execute(
                    "SELECT * FROM runs WHERE run_id = ? AND manifest IS NOT NULL", (run_id,)
                ).fetchone()
                if run is None:
                    raise RuntimeError(f"run {run_id} is not in {self.path}")
            elif not legacy:
                run = db.execute(
                    "SELECT * FROM runs WHERE directory = ? AND manifest IS NOT NULL"
                    " ORDER BY started_at DESC, seq DESC LIMIT 1",
                    (directory,),
                ).fetchone()
            else:
                run = None
            if run is None:
                imported = db.execute("SELECT * FROM imports WHERE directory = ?", (directory,)).fetchone()
                if imported is not None:
                    self.unreadable_lines = imported["unreadable"]
                    return _decode(imported["manifest"])
                if legacy:
                    return {}
                raise RuntimeError(f"no runs for {directory} in {self.path}")
            imported = db.execute(
                "SELECT unreadable FROM imports WHERE directory = ?", (run["directory"],)
            ).fetchone()
            self.unreadable_lines = imported["unreadable"] if imported is not None else 0
            return _decode(run["manifest"]) | {
                "run_state": run["state"],
                "tasks": [
                    _decode(row["member"])
                    for row in db.execute(
                        "SELECT member FROM members WHERE run_id = ? ORDER BY position", (run["run_id"],)
                    )
                ],
            }

    def query(
        self,
        *,
        run_id: str | None = None,
        run_dir: Path | None = None,
        surface: dict[str, Any] | None = None,
        method: str | None = None,
        observation: str | None = None,
        commit: str | None = None,
    ) -> list[dict[str, Any]]:
        """Return observations filtered by indexed provenance or the run that pinned them."""
        columns = {
            "a.surface": _json(surface) if surface is not None else None,
            "a.method": method,
            "a.record_id": observation,
            "a.code_commit": commit,
            "a.directory": str(run_dir.resolve()) if run_dir is not None else None,
        }
        predicates = ["a.result IS NOT NULL"]
        params = []
        if run_id is not None:
            predicates.append("m.run_id = ?")
            params.append(run_id)
            select = (
                "SELECT a.result, a.log_directory, m.member FROM members m"
                " JOIN attempts a ON a.record_id = m.record_id"
            )
            order = "m.position"
        else:
            select = "SELECT a.result, a.log_directory FROM attempts a"
            order = "a.seq"
        for column, value in columns.items():
            if value is not None:
                predicates.append(f"{column} = ?")
                params.append(value)
        with self._read() as db:
            if db is None:
                raise RuntimeError(f"no results database at {self.path}")
            if (
                run_id is not None
                and not db.execute("SELECT 1 FROM runs WHERE run_id = ?", (run_id,)).fetchone()
            ):
                raise RuntimeError(f"run {run_id} is not in {self.path}")
            rows = db.execute(f"{select} WHERE {' AND '.join(predicates)} ORDER BY {order}", params)
            if run_id is None:
                return [_result(row) for row in rows]
            results = []
            for row in rows:
                record = _result(row)
                member = _decode(row["member"])
                if record.get("computation_id") == member.get("computation_id"):
                    results.append(
                        record
                        | member.get("check", {})
                        | {
                            "task_id": member["id"],
                            "task": member,
                            "check_id": member["check_id"],
                            "selected_run_id": run_id,
                        }
                    )
            return results

    def import_jsonl(self, run_dir: Path) -> int:
        """Migrate result rows and run manifests in one transaction, retaining source files."""
        legacy = ResultStore(run_dir / "results.jsonl")
        records = legacy.records()
        directory = str(run_dir.resolve())
        manifests: dict[str, dict[str, Any]] = {}
        latest = (
            _decode((run_dir / "manifest.json").read_text()) if (run_dir / "manifest.json").exists() else {}
        )
        manifest_paths = sorted((run_dir / "runs").glob("*.json"))
        for source_manifest in [_decode(path.read_text(encoding="utf-8")) for path in manifest_paths] + [
            latest
        ]:
            if (run_id := _string(source_manifest.get("run_id"))) is not None:
                if run_id in manifests and manifests[run_id] != source_manifest:
                    raise RuntimeError(f"conflicting manifests for run {run_id}")
                manifests[run_id] = source_manifest

        run_metadata = {}
        run_log = run_dir / "runs.jsonl"
        if run_log.exists():
            with run_log.open("rb") as handle:
                for line in handle:
                    try:
                        data = _object(json.loads(line))
                    except (json.JSONDecodeError, UnicodeDecodeError):
                        legacy.unreadable_lines += 1
                        continue
                    if (run_id := _string(data.get("run_id"))) is not None:
                        run_metadata[run_id] = data
        # Old versioned manifests are immutable. The replaceable latest manifest is exported last.
        if (latest_id := _string(latest.get("run_id"))) is not None:
            manifests[latest_id] = manifests.pop(latest_id)

        with self._write() as db:
            db.execute(
                "INSERT INTO imports VALUES (?, ?, ?) ON CONFLICT (directory)"
                " DO UPDATE SET manifest = excluded.manifest, unreadable = excluded.unreadable",
                (directory, _json(latest if latest_id is None else {}), legacy.unreadable_lines),
            )
            for run_id in dict.fromkeys((*run_metadata, *manifests)):
                manifest = manifests.get(run_id)
                existing = db.execute("SELECT * FROM runs WHERE run_id = ?", (run_id,)).fetchone()
                if existing is None:
                    if manifest is None:
                        metadata = run_metadata[run_id]
                        db.execute(
                            "INSERT INTO runs(run_id, directory, metadata, state, started_at)"
                            " VALUES (?, ?, ?, 'imported', ?)",
                            (run_id, directory, _json(metadata), _string(metadata.get("started_at"))),
                        )
                    else:
                        self._insert_run(
                            db, run_id, directory, manifest, run_metadata.get(run_id, {}), "imported"
                        )
                elif manifest is not None:
                    header = {key: value for key, value in manifest.items() if key != "tasks"}
                    members = [
                        row["member"]
                        for row in db.execute(
                            "SELECT member FROM members WHERE run_id = ? ORDER BY position", (run_id,)
                        )
                    ]
                    if existing["manifest"] != _json(header) or members != [
                        _json(task) for task in manifest.get("tasks", [])
                    ]:
                        raise RuntimeError(f"conflicting manifests for run {run_id}")
            occurrences: Counter[str] = Counter()
            return sum(self._import_record(db, directory, record, occurrences) for record in records)

    @staticmethod
    def _import_record(
        db: sqlite3.Connection, directory: str, record: dict[str, Any], occurrences: Counter[str]
    ) -> int:
        record_id, computation_id, check_id = _record_identity(record)
        attempt_id = _string(record.get("attempt_id"))
        source = _string(record.get("log_directory")) or directory
        payload = _json(
            {
                key: value
                for key, value in record.items()
                if key != "log_directory" or not isinstance(value, str)
            }
        )
        digest = hashlib.sha256(payload.encode()).hexdigest()
        occurrences[digest] += 1
        key = _json((source, digest, occurrences[digest]))
        for row in db.execute(
            "SELECT result FROM attempts WHERE attempt_id = ? OR record_id = ? OR import_key = ?",
            (attempt_id, record_id, key),
        ):
            if row["result"] != payload:
                raise RuntimeError(f"conflicting imported attempt {attempt_id or record_id}")
            return 0
        db.execute(
            "INSERT INTO attempts (attempt_id, record_id, computation_id, check_id, run_id, task_id,"
            " state, started_at, log, directory, log_directory,"
            " surface, method, code_commit, result, import_key)"
            " VALUES (?, ?, ?, ?, ?, ?, 'finished', ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (
                attempt_id,
                record_id,
                computation_id,
                check_id,
                _string(record.get("run_id")),
                record["task_id"],
                _string(record.get("started_at")),
                _string(record.get("log")),
                directory,
                source,
                *_indexes(record),
                payload,
                key,
            ),
        )
        return 1
