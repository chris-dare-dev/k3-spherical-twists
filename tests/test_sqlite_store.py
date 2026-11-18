"""Transactional result and run membership tests using temporary SQLite databases."""

from __future__ import annotations

import json
import sqlite3
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from k3batch.report import selected_results
from k3batch.runner import REPOSITORY
from k3batch.sqlite_store import SQLiteStore
from k3batch.store import StoreLocked

MEMBER = {
    "id": "pair",
    "kind": "ext_pair",
    "computation_id": "operation",
    "check_id": "original-check",
    "record_id": "observation",
    "check": {},
}
MANIFEST = {"run_id": "initial", "schema_version": 1, "tasks": [MEMBER]}
RESULT = {
    "task_id": "pair",
    "task": {"surface": {"d": 2}},
    "value": 2**90,
    "predicted": 2**90,
    "status": "ok",
    "detail": {
        "method": "Hom",
        "outputs": [{"name": "artifact", "media_type": "application/json", "digest": "sha256:123"}],
    },
    "code": {"commit": "commit", "external_metadata": ["keep"]},
    "log": "logs/attempt.log",
    "schema_version": 1,
    "record_id": "observation",
    "computation_id": "operation",
    "check_id": "original-check",
    "attempt_id": "attempt",
    "run_id": "initial",
}


class TransactionalStore(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.store = SQLiteStore(self.root / "results.sqlite")

    def test_observation_finish_is_atomic_and_checked_against_the_active_attempt(self) -> None:
        with self.store, self.store.run(self.run_dir, MANIFEST, {}):
            self.store.start_attempt("initial", MEMBER, "attempt", "start", "logs/attempt.log")
            with self.assertRaises(ValueError):
                self.store.append(RESULT | {"value": float("nan")})
            with self.assertRaisesRegex(RuntimeError, "running attempt"):
                self.store.append(RESULT | {"check_id": "different"})
            self.assertEqual(self.store.query(), [])
            self.store.append(RESULT)
            with self.assertRaisesRegex(RuntimeError, "running attempt"):
                self.store.append(RESULT)
        raw = self.store.query()
        self.assertEqual(raw, [RESULT | {"log_directory": str(self.run_dir.resolve())}])
        self.assertEqual(self.store.manifest(self.run_dir)["run_state"], "completed")
        self.assertEqual(self.store.query(surface={"d": 2}, method="Hom", commit="commit"), raw)
        self.assertEqual(self.store.query(observation="observation"), raw)
        self.assertEqual(self.store.query(method="wrong"), [])
        self.assertEqual(self.store.latest_by_computation(["operation"]), {"operation": raw[0]})

    def test_existing_membership_and_checks_remain_selectable_after_a_later_attempt(self) -> None:
        newer = MEMBER | {
            "record_id": "later-observation",
            "check_id": "later-check",
        }
        later = MANIFEST | {"run_id": "later", "tasks": [newer]}
        reused = MEMBER | {"check_id": "check-revision", "check": {"predicted": 1, "status": "mismatch"}}
        revised = MANIFEST | {"run_id": "recheck", "tasks": [reused]}
        with self.store:
            with self.store.run(self.run_dir, MANIFEST, {}):
                self.store.start_attempt("initial", MEMBER, "attempt", "start", "log")
                self.store.append(RESULT)
            with self.store.run(self.root / "another", revised, {}):
                pass
            with self.store.run(self.run_dir, later, {}):
                self.store.start_attempt("later", newer, "retry", "start", "log")
                self.store.append(
                    RESULT
                    | {
                        "run_id": "later",
                        "attempt_id": "retry",
                        "record_id": "later-observation",
                        "check_id": "later-check",
                        "value": 2,
                    }
                )
        self.assertEqual(self.store.latest_by_computation(["operation"])["operation"]["value"], 2)
        self.assertEqual(self.store.manifest(self.run_dir)["run_id"], "later")
        pinned = self.store.manifest(run_id="initial")
        self.assertEqual(selected_results(self.store, pinned)["pair"]["value"], 2**90)
        (selection,) = self.store.query(run_id="recheck")
        self.assertEqual(selection["run_id"], "initial")
        self.assertEqual(selection["selected_run_id"], "recheck")
        self.assertEqual(selection["check_id"], "check-revision")
        self.assertEqual(selection["predicted"], 1)
        self.assertEqual(selection["log_directory"], str(self.run_dir.resolve()))

    def test_coordinators_exclude_concurrent_writers_and_allow_reads(self) -> None:
        with self.store, self.store.run(self.run_dir, MANIFEST | {"tasks": []}, {}):
            with self.assertRaises(StoreLocked), SQLiteStore(self.store.path):
                self.fail("a second coordinator acquired the writer lock")
            self.assertEqual(SQLiteStore(self.store.path).manifest(self.run_dir)["run_state"], "running")

    def test_writer_reopen_recovers_a_dead_coordinators_attempt(self) -> None:
        program = """
import json
import os
import sys
from pathlib import Path
from k3batch.sqlite_store import SQLiteStore
store = SQLiteStore(Path(sys.argv[1]))
directory = Path(sys.argv[2])
manifest = json.loads(sys.argv[3])
with store, store.run(directory, manifest, {}):
    store.start_attempt(manifest["run_id"], manifest["tasks"][0], "attempt", "start", "log")
    os._exit(9)
"""
        process = subprocess.run(
            [sys.executable, "-c", program, str(self.store.path), str(self.run_dir), json.dumps(MANIFEST)],
            cwd=REPOSITORY,
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(process.returncode, 9, process.stderr)
        self.assertEqual(self.store.manifest(self.run_dir)["run_state"], "running")
        with self.store:
            self.assertEqual(self.store.manifest(self.run_dir)["run_state"], "interrupted")
        with sqlite3.connect(self.store.path) as db:
            state, ended, log = db.execute("SELECT state, ended_at, log FROM attempts").fetchone()
        self.assertEqual(state, "interrupted")
        self.assertIsNotNone(ended)
        self.assertEqual(log, "log")
        self.assertEqual(self.store.latest_by_computation(["operation"]), {})

    def test_legacy_migration_is_repeatable_and_preserves_source_files(self) -> None:
        legacy = {"task_id": "unknown", "status": "ok", "unknown": {"integer": 2**90}}
        source = {
            "results.jsonl": (chr(10).join(map(json.dumps, (legacy, legacy, RESULT))) + chr(10)).encode()
            + b'{"x',
            "manifest.json": json.dumps(MANIFEST).encode(),
            "runs.jsonl": json.dumps({"run_id": "initial", "provenance": {"region": "test"}}).encode(),
        }
        for name, content in source.items():
            (self.run_dir / name).write_bytes(content)
        with self.store:
            self.assertEqual(self.store.import_jsonl(self.run_dir), 3)
            self.assertEqual(self.store.import_jsonl(self.run_dir), 0)
        for name, content in source.items():
            self.assertEqual((self.run_dir / name).read_bytes(), content)
        pinned = self.store.manifest(self.run_dir)
        self.assertEqual(pinned["tasks"], MANIFEST["tasks"])
        self.assertEqual(self.store.unreadable_lines, 1)
        self.assertEqual(self.store.query(run_id="initial")[0]["value"], 2**90)
        self.assertEqual([row["unknown"] for row in self.store.query()[:2]], [legacy["unknown"]] * 2)
        with sqlite3.connect(self.store.path) as db:
            metadata = json.loads(db.execute("SELECT metadata FROM runs").fetchone()[0])
        self.assertEqual(metadata["provenance"], {"region": "test"})

    def test_conflicting_import_rolls_back_rows_and_run_membership(self) -> None:
        (self.run_dir / "results.jsonl").write_text(
            json.dumps(RESULT) + "\n" + json.dumps(RESULT | {"value": 0}) + "\n"
        )
        (self.run_dir / "manifest.json").write_text(json.dumps(MANIFEST))
        with self.store:
            with self.assertRaisesRegex(RuntimeError, "conflicting imported attempt"):
                self.store.import_jsonl(self.run_dir)
            self.assertEqual(self.store.query(), [])
            with self.assertRaisesRegex(RuntimeError, "no runs"):
                self.store.manifest(self.run_dir)

    def test_import_command_refuses_to_use_an_empty_source_as_the_database(self) -> None:
        source = self.run_dir / "results.jsonl"
        source.touch()
        base = [sys.executable, "-m", "k3batch", "import-jsonl", str(self.run_dir), "--store"]
        refused = subprocess.run(
            [*base, str(source)], cwd=REPOSITORY, check=False, capture_output=True, text=True, timeout=10
        )
        self.assertEqual(refused.returncode, 2, refused.stderr)
        self.assertEqual(source.read_bytes(), b"")
        imported = subprocess.run(
            [*base, str(self.store.path)],
            cwd=REPOSITORY,
            check=False,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(imported.returncode, 0, imported.stderr)
        self.assertEqual(self.store.query(), [])

    def test_missing_database_reads_do_not_create_it_and_unknown_versions_are_rejected(self) -> None:
        self.assertEqual(self.store.latest_by_computation(["operation"]), {})
        self.assertFalse(self.store.path.exists())
        with self.store:
            pass
        with sqlite3.connect(self.store.path) as db:
            db.execute("PRAGMA user_version = 2")
        with self.assertRaisesRegex(RuntimeError, "unsupported k3batch database format"):
            self.store.query()
        with self.assertRaisesRegex(RuntimeError, "unsupported k3batch database format"), self.store:
            self.fail("writer accepted a newer schema")
