"""The results of earlier runs: what every store of them offers, and the store that is a file of lines."""

from __future__ import annotations

import errno
import fcntl
import json
import os
import re
from abc import ABC, abstractmethod
from collections.abc import Collection, Iterator, Sequence
from contextlib import AbstractContextManager, contextmanager
from heapq import nlargest
from pathlib import Path
from typing import Any, ClassVar, cast

from .record import RECORD_SCHEMA, Record, attempt_started_at


class StoreLocked(RuntimeError):
    """Another scheduler is writing to the same results."""


def lock_writer(path: Path) -> int:
    fd = os.open(path.with_name(path.name + ".lock"), os.O_RDWR | os.O_CREAT, 0o644)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        raise StoreLocked(f"another run is writing to {path}") from None
    except BaseException:
        os.close(fd)
        raise
    return fd


class RunHistory(ABC):
    """What the scheduler, the reports and the command line ask of the results of earlier runs.

    A record is the JSON object of one attempt that ended. Computation history sorts by attempt
    start time (the first trial's start for a retried attempt), newest first. Ties sort by descending
    record ID. Unknown start times sort after known times. `ResultStore` keeps the records of one run
    directory in a file of lines; `SQLiteStore` keeps those of many in one database.
    """

    # Whether a run with a dependency graph can be kept: its attempts are claimed with their
    # prerequisites before they start, and looked up by record afterwards.
    supports_graphs: ClassVar[bool]
    path: Path
    unreadable_lines: int

    @property
    @abstractmethod
    def location(self) -> Path:
        """Where a run is told its results are."""

    @abstractmethod
    def __enter__(self) -> RunHistory:
        """Become the one writer of the store."""

    @abstractmethod
    def __exit__(self, *exc: object) -> None: ...

    @abstractmethod
    def run(
        self, run_dir: Path, manifest: dict[str, Any], metadata: dict[str, Any]
    ) -> AbstractContextManager[None]:
        """Record the members of a run before its work starts, and how it ended."""

    @abstractmethod
    def start_attempt(
        self,
        run_id: str,
        member: dict[str, Any],
        attempt_id: str,
        started_at: str,
        log: str | None,
        *,
        prerequisites: Sequence[str] = (),
    ) -> None:
        """Claim an attempt of a member of the active run, before its process starts."""

    @abstractmethod
    def append(self, record: Record) -> None:
        """Keep the record of an attempt that ended."""

    @abstractmethod
    def recent_by_computation(self, identities: Sequence[str], limit: int) -> dict[str, list[Record]]:
        """The history of each computation that has one: its last `limit` reusable records."""

    def latest_by_computation(self, identities: Sequence[str]) -> dict[str, Record]:
        """The latest reusable record of each computation that has one."""
        return {identity: rows[0] for identity, rows in self.recent_by_computation(identities, 1).items()}

    @abstractmethod
    def by_record_id(self, identities: Sequence[str]) -> dict[str, Record]:
        """The records that run members reserved, by their record ID."""

    @abstractmethod
    def manifest(
        self, run_dir: Path | None = None, run_id: str | None = None, *, legacy: bool = False
    ) -> dict[str, Any]:
        """The members of the latest run of a directory or of the run with the given ID.

        With `legacy`, the manifest from before versioned runs if there is one, and otherwise none.
        """

    @abstractmethod
    def unpinned(self, run_dir: Path, *, legacy: bool) -> dict[str, Record]:
        """The latest record of each task of a directory whose manifest pins no records.

        With `legacy`, only the records from before versioned runs count.
        """


class ResultStore(RunHistory):
    """An append-only file of records, written by one scheduler at a time.

    Each append writes and syncs a complete record before returning. An interrupted write can leave
    an incomplete last line. Readers skip and count invalid lines, and the next writer closes off
    the tail at a newline before appending.

    The members of each run are files next to it: `manifest.json` (the latest run), `runs/<id>.json`
    and a line of `runs.jsonl`. An attempt leaves no trace before it ends, so there is nothing to claim.
    """

    supports_graphs = False

    def __init__(self, path: Path) -> None:
        self.path = path
        self.unreadable_lines = 0
        self._fd: int | None = None
        self._lock_fd: int | None = None
        self._write_failed = False

    # reading ---------------------------------------------------------------------------------------

    def records(self) -> list[Record]:
        """Every record in the file, oldest first."""
        self.unreadable_lines = 0
        try:
            handle = self.path.open("rb")
        except FileNotFoundError:
            return []
        records: list[Record] = []
        with handle:
            for line in handle:
                try:
                    decoded = line.decode("utf-8")
                    if not decoded.strip():
                        continue
                    record = json.loads(decoded)
                except (UnicodeDecodeError, json.JSONDecodeError):
                    self.unreadable_lines += 1
                    continue
                if (
                    isinstance(record, dict)
                    and isinstance(record.get("task_id"), str)
                    and isinstance(record.get("status"), str)
                ):
                    records.append(cast(Record, record))
                else:
                    self.unreadable_lines += 1
        return records

    def latest(self) -> dict[str, Record]:
        """The most recent record of each task."""
        return {record["task_id"]: record for record in self.records()}

    def finished(self, retry: Collection[str] = ()) -> set[str]:
        """Ids of the tasks a run must not compute again: those whose latest status is not in `retry`."""
        return {task_id for task_id, record in self.latest().items() if record["status"] not in retry}

    @property
    def location(self) -> Path:
        return self.path.parent

    def recent_by_computation(self, identities: Sequence[str], limit: int) -> dict[str, list[Record]]:
        if limit <= 0:
            return {}
        wanted = set(identities)
        history: dict[str, list[Record]] = {}
        for record in self.records():
            identity = record.get("computation_id")
            if (
                record.get("schema_version") == RECORD_SCHEMA
                and isinstance(identity, str)
                and identity in wanted
                and all(isinstance(record.get(key), str) for key in ("check_id", "record_id"))
            ):
                history.setdefault(identity, []).append(record)
        return {
            identity: nlargest(
                limit, rows, key=lambda record: (attempt_started_at(record), record["record_id"])
            )
            for identity, rows in history.items()
        }

    def by_record_id(self, identities: Sequence[str]) -> dict[str, Record]:
        wanted = set(identities)
        return {
            record["record_id"]: record
            for record in self.records()
            if record.get("schema_version") == RECORD_SCHEMA
            and isinstance(record.get("record_id"), str)
            and record["record_id"] in wanted
        }

    def manifest(
        self, run_dir: Path | None = None, run_id: str | None = None, *, legacy: bool = False
    ) -> dict[str, Any]:
        directory = run_dir or self.path.parent
        if legacy:
            latest = _read_manifest(directory, None)
            return {} if "schema_version" in latest else latest
        return _read_manifest(directory, run_id)

    def unpinned(self, run_dir: Path, *, legacy: bool) -> dict[str, Record]:
        return {
            record["task_id"]: record
            for record in self.records()
            if not legacy or "schema_version" not in record
        }

    # writing ---------------------------------------------------------------------------------------

    def open(self) -> None:
        """Takes the lock and opens the file for appending."""
        if self._lock_fd is not None:
            raise RuntimeError("the store is already open for writing")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock_fd = lock_writer(self.path)
        try:
            self._fd = os.open(self.path, os.O_RDWR | os.O_APPEND | os.O_CREAT, 0o644)
            size = os.fstat(self._fd).st_size
            if size and os.pread(self._fd, 1, size - 1) != b"\n":
                _write_synced(self._fd, b"\n")
        except BaseException:
            self.close()
            raise
        self._write_failed = False

    @contextmanager
    def run(self, run_dir: Path, manifest: dict[str, Any], metadata: dict[str, Any]) -> Iterator[None]:
        _write_json(run_dir / "runs" / f"{manifest['run_id']}.json", manifest)
        _write_json(run_dir / "manifest.json", manifest)
        with (run_dir / "runs.jsonl").open("a", encoding="utf-8") as handle:
            handle.write(json.dumps(metadata, sort_keys=True) + "\n")
        yield

    def start_attempt(
        self,
        run_id: str,
        member: dict[str, Any],
        attempt_id: str,
        started_at: str,
        log: str | None,
        *,
        prerequisites: Sequence[str] = (),
    ) -> None:
        pass

    def append(self, record: Record) -> None:
        if self._fd is None:
            raise RuntimeError("the store is not open for writing")
        if self._write_failed:
            raise RuntimeError("reopen the result store before appending after an I/O failure")
        line = json.dumps(record, sort_keys=True, ensure_ascii=False, allow_nan=False) + "\n"
        try:
            _write_synced(self._fd, line.encode("utf-8"))
        except BaseException:
            # A partial line needs recovery under the writer lock before appending another.
            self._write_failed = True
            raise

    def close(self) -> None:
        for fd in (self._fd, self._lock_fd):
            if fd is not None:
                os.close(fd)
        self._fd = None
        self._lock_fd = None

    def __enter__(self) -> ResultStore:
        self.open()
        return self

    def __exit__(self, *exc: object) -> None:
        self.close()


def _write_synced(fd: int, data: bytes) -> None:
    remaining = memoryview(data)
    while remaining:
        written = os.write(fd, remaining)
        if written == 0:
            raise OSError(errno.EIO, "writing the result store made no progress")
        remaining = remaining[written:]
    os.fsync(fd)


def _write_json(path: Path, content: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".part")
    temporary.write_text(json.dumps(content, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    temporary.replace(path)


def _read_manifest(run_dir: Path, run_id: str | None) -> dict[str, Any]:
    """The latest manifest of a run directory, or the immutable one of a run."""
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
