"""The result file: whole records only, one writer at a time."""

from __future__ import annotations

import errno
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from k3batch.store import ResultStore, StoreLocked


def record(task_id: str, status: str = "ok") -> dict[str, str]:
    return {"task_id": task_id, "status": status}


class Store(unittest.TestCase):
    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.path = Path(scratch.name) / "run" / "results.jsonl"

    def test_records_come_back_in_the_order_written(self) -> None:
        with ResultStore(self.path) as store:
            store.append(record("a"))
            store.append(record("b", "timeout"))
            store.append(record("a", "error"))
        store = ResultStore(self.path)
        self.assertEqual([r["task_id"] for r in store.records()], ["a", "b", "a"])
        self.assertEqual(store.latest()["a"]["status"], "error")
        self.assertEqual(store.finished(), {"a", "b"})
        self.assertEqual(store.finished(retry={"timeout"}), {"a"})
        self.assertEqual(len(self.path.read_text().splitlines()), 3)

    def test_an_empty_or_missing_file_has_no_records(self) -> None:
        self.assertEqual(ResultStore(self.path).records(), [])
        self.assertEqual(ResultStore(self.path).finished(), set())

    def test_an_incomplete_utf8_last_line_is_ignored_and_closed_off(self) -> None:
        with ResultStore(self.path) as store:
            store.append(record("a"))
        with self.path.open("ab") as handle:
            handle.write(b'{"task_id": "\xe2\x82')  # partial UTF-8 character in an interrupted record

        store = ResultStore(self.path)
        self.assertEqual(store.finished(), {"a"})
        self.assertEqual(store.unreadable_lines, 1)

        with store:
            store.append(record("c"))
        self.assertEqual(store.finished(), {"a", "c"})
        self.assertEqual(store.unreadable_lines, 1)

    def test_an_append_completes_short_writes_before_syncing(self) -> None:
        write = os.write
        saved = record("a€")

        def check_complete_record(_fd: int) -> None:
            self.assertTrue(self.path.read_bytes().endswith(b"\n"))
            self.assertEqual(store.records(), [saved])

        with (
            ResultStore(self.path) as store,
            patch("k3batch.store.os.write", side_effect=lambda fd, data: write(fd, data[:5])) as partial,
            patch("k3batch.store.os.fsync", side_effect=check_complete_record) as sync,
        ):
            store.append(saved)
            self.assertGreater(partial.call_count, 1)
            sync.assert_called_once()

    def test_a_failed_append_surfaces_the_error_and_can_recover_after_reopening(self) -> None:
        write = os.write
        store = ResultStore(self.path)
        with store:
            store.append(record("kept"))

            def partial_then_fail(fd: int, data: memoryview) -> int:
                if bytes(data).startswith(b"{"):
                    return write(fd, data[:8])
                raise OSError(errno.ENOSPC, "no space for result")

            with patch("k3batch.store.os.write", side_effect=partial_then_fail):
                with self.assertRaises(OSError) as error:
                    store.append(record("interrupted"))
                self.assertEqual(error.exception.errno, errno.ENOSPC)
            with self.assertRaisesRegex(RuntimeError, "reopen"):
                store.append(record("too early"))

        with store:
            store.append(record("interrupted"))
        self.assertEqual(store.records(), [record("kept"), record("interrupted")])
        self.assertEqual(store.unreadable_lines, 1)

    def test_failed_tail_repair_releases_the_writer_lock(self) -> None:
        self.path.parent.mkdir(parents=True)
        self.path.write_bytes(b'{"unfinished":')
        with patch("k3batch.store.os.write", return_value=0):
            with self.assertRaises(OSError) as error:
                ResultStore(self.path).open()
            self.assertEqual(error.exception.errno, errno.EIO)

        with ResultStore(self.path) as store:
            store.append(record("a"))
        self.assertEqual(store.records(), [record("a")])
        self.assertEqual(store.unreadable_lines, 1)

    def test_lines_that_are_not_records_are_counted_not_used(self) -> None:
        self.path.parent.mkdir(parents=True)
        self.path.write_bytes(
            b'{"task_id": "a", "status": "ok"}\n[1, 2]\n\xff\n'
            b'{"status": "ok"}\n{"task_id": [], "status": "ok"}\n\n{"task_id": "b", "status": "ok"}\n'
        )
        store = ResultStore(self.path)
        self.assertEqual(store.finished(), {"a", "b"})
        self.assertEqual(store.unreadable_lines, 4)

    def test_a_second_writer_is_refused(self) -> None:
        with ResultStore(self.path), self.assertRaises(StoreLocked):
            ResultStore(self.path).open()
        with ResultStore(self.path) as store:
            store.append(record("a"))

    def test_writing_needs_an_open_store(self) -> None:
        with self.assertRaises(RuntimeError):
            ResultStore(self.path).append(record("a"))


if __name__ == "__main__":
    unittest.main()
