"""The results of a batch: one JSON object per line, one line per task that ended."""

from __future__ import annotations

import errno
import fcntl
import json
import os
from collections.abc import Collection
from pathlib import Path
from typing import Any


class StoreLocked(RuntimeError):
    """Another scheduler is writing to the same results."""


class ResultStore:
    """An append-only file of records, written by one scheduler at a time.

    Each append writes and syncs a complete record before returning. An interrupted write can leave
    an incomplete last line. Readers skip and count invalid lines, and the next writer closes off
    the tail at a newline before appending.
    """

    def __init__(self, path: Path) -> None:
        self.path = path
        self.unreadable_lines = 0
        self._fd: int | None = None
        self._lock_fd: int | None = None
        self._write_failed = False

    # reading ---------------------------------------------------------------------------------------

    def records(self) -> list[dict[str, Any]]:
        """Every record in the file, oldest first."""
        self.unreadable_lines = 0
        try:
            handle = self.path.open("rb")
        except FileNotFoundError:
            return []
        records = []
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
                    records.append(record)
                else:
                    self.unreadable_lines += 1
        return records

    def latest(self) -> dict[str, dict[str, Any]]:
        """The most recent record of each task."""
        return {record["task_id"]: record for record in self.records()}

    def finished(self, retry: Collection[str] = ()) -> set[str]:
        """Ids of the tasks a run must not compute again: those whose latest status is not in `retry`."""
        return {task_id for task_id, record in self.latest().items() if record["status"] not in retry}

    # writing ---------------------------------------------------------------------------------------

    def open(self) -> None:
        """Takes the lock and opens the file for appending."""
        if self._lock_fd is not None:
            raise RuntimeError("the store is already open for writing")
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self._lock_fd = os.open(self.path.with_name(self.path.name + ".lock"), os.O_RDWR | os.O_CREAT, 0o644)
        try:
            try:
                fcntl.flock(self._lock_fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise StoreLocked(f"another run is writing to {self.path}") from None
            self._fd = os.open(self.path, os.O_RDWR | os.O_APPEND | os.O_CREAT, 0o644)
            size = os.fstat(self._fd).st_size
            if size and os.pread(self._fd, 1, size - 1) != b"\n":
                _write_synced(self._fd, b"\n")
        except BaseException:
            self.close()
            raise
        self._write_failed = False

    def append(self, record: dict[str, Any]) -> None:
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
