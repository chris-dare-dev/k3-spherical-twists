"""What every store of results offers, asked of the file of lines and of the database alike."""

from __future__ import annotations

import json
import tempfile
import unittest
from dataclasses import replace
from pathlib import Path
from typing import Any
from uuid import uuid4

from batch.jobs import PollingGuard
from batch.records import ResultStore, RunHistory, SQLiteStore, StoreLocked
from batch.reports import render, selected_results
from batch.scheduler import Scheduler
from batch.tasks import ConfigError, Task

from ..helpers import fake_config, fake_runner


def member(record_id: str, check_id: str = "check") -> dict[str, Any]:
    return {
        "id": "pair",
        "kind": "ext_pair",
        "group": "pairs",
        "computation_id": "operation",
        "check_id": check_id,
        "record_id": record_id,
        "check": {},
    }


def result(run_id: str, entry: dict[str, Any], started_at: str, value: int) -> dict[str, Any]:
    return {
        "task_id": entry["id"],
        "task": {"id": entry["id"], "kind": "ext_pair", "group": "pairs"},
        "status": "ok",
        "value": value,
        "predicted": value,
        "agrees": True,
        "detail": {"method": "Hom"},
        "error": None,
        "wall_seconds": 1.5,
        "peak_rss_mb": 120.0,
        "limits": {"time_seconds": 60, "memory_mb": 500},
        "log": None,
        "started_at": started_at,
        "schema_version": 1,
        "computation_id": entry["computation_id"],
        "check_id": entry["check_id"],
        "record_id": entry["record_id"],
        "attempt_id": f"attempt-{entry['record_id']}",
        "run_id": run_id,
    }


class Contract:
    """The tests of one store; a subclass says which, and how unversioned records get into it."""

    store: RunHistory
    root: Path
    run_dir: Path

    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)  # type: ignore[attr-defined]
        self.root = Path(scratch.name)
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.store = self.make()

    def make(self) -> RunHistory:
        raise NotImplementedError

    def seed_unversioned(self, records: list[dict[str, Any]]) -> None:
        raise NotImplementedError

    def record_run(self, record_id: str, started_at: str, value: int, check_id: str = "check") -> str:
        """A run of one task that computes `value`; returns the ID of the run."""
        run_id = uuid4().hex
        entry = member(record_id, check_id)
        manifest = {"run_id": run_id, "schema_version": 1, "batch": "contract", "tasks": [entry]}
        with self.store, self.store.run(self.run_dir, manifest, {"run_id": run_id, "started_at": started_at}):
            self.store.start_attempt(run_id, entry, f"attempt-{record_id}", started_at, None)
            self.store.append(result(run_id, entry, started_at, value))
        return run_id

    def test_a_run_pins_its_members_and_their_records(self: Any) -> None:
        first = self.record_run("first", "2026-01-01T00:00:01+00:00", 1)
        second = self.record_run("second", "2026-01-01T00:00:02+00:00", 2)

        latest = self.store.manifest(self.run_dir)
        self.assertEqual((latest["run_id"], latest["schema_version"]), (second, 1))
        self.assertEqual(latest["tasks"], [member("second")])
        self.assertEqual(selected_results(self.store, latest)["pair"]["value"], 2)

        earlier = self.store.manifest(self.run_dir, first)
        self.assertEqual(earlier["tasks"], [member("first")])
        pinned = selected_results(self.store, earlier)["pair"]
        self.assertEqual((pinned["value"], pinned["record_id"], pinned["check_id"]), (1, "first", "check"))
        self.assertEqual(pinned["task"], member("first"))

        self.assertEqual(set(self.store.by_record_id(["first", "second", "absent"])), {"first", "second"})
        self.assertEqual(self.store.by_record_id([]), {})
        with self.assertRaisesRegex(RuntimeError, "is not in"):
            self.store.manifest(self.run_dir, uuid4().hex)
        with self.assertRaisesRegex(RuntimeError, "versioned manifest"):
            selected_results(self.store, {"tasks": []})

        report = render(self.run_dir, store=self.store)
        self.assertIn(f"- run: `{second}`", report)
        self.assertIn("| pairs | 1 | 1 |", report)
        self.assertIn(f"- run: `{first}`", render(self.run_dir, run_id=first, store=self.store))

    def test_a_history_is_newest_first_and_as_long_as_asked(self: Any) -> None:
        self.assertEqual(self.store.recent_by_computation(["operation"], 3), {})
        for index, name in enumerate(("first", "second", "third"), start=1):
            self.record_run(name, f"2026-01-01T00:00:0{index}+00:00", index)

        def values(limit: int) -> dict[str, list[int]]:
            history = self.store.recent_by_computation(["operation", "unknown"], limit)
            return {identity: [row["value"] for row in rows] for identity, rows in history.items()}

        self.assertEqual(values(2), {"operation": [3, 2]})
        self.assertEqual(values(5), {"operation": [3, 2, 1]})
        self.assertEqual(self.store.latest_by_computation(["operation"])["operation"]["record_id"], "third")
        self.assertEqual(self.store.latest_by_computation(["unknown"]), {})

    def test_overlapping_attempts_sort_by_first_start_and_break_ties_by_record_id(self: Any) -> None:
        run_id = uuid4().hex
        older, high, low = [member(name) | {"id": name} for name in ("older", "z", "a")]
        manifest = {"run_id": run_id, "schema_version": 1, "batch": "contract", "tasks": [older, high, low]}
        older_start = "2026-01-01T00:00:01+00:00"
        tied_start = "2026-01-01T00:00:02+00:00"
        same_instant = "2026-01-01T01:00:02+01:00"
        retry_start = "2026-01-01T00:00:05+00:00"
        with self.store, self.store.run(self.run_dir, manifest, {"started_at": older_start}):
            self.store.start_attempt(run_id, older, "attempt-older", older_start, None)
            self.store.start_attempt(run_id, high, "attempt-z", tied_start, None)
            self.store.start_attempt(run_id, low, "attempt-a", same_instant, None)
            self.store.append(result(run_id, high, tied_start, 2))
            self.store.append(result(run_id, low, same_instant, 3))
            self.store.append(
                result(run_id, older, retry_start, 1)
                | {"resource_attempts": [{"started_at": older_start}, {"started_at": retry_start}]}
            )

        rows = self.store.recent_by_computation(["operation"], 3)["operation"]
        self.assertEqual([row["record_id"] for row in rows], ["z", "a", "older"])
        self.assertEqual(self.store.latest_by_computation(["operation"])["operation"]["record_id"], "z")
        self.assertEqual(self.store.recent_by_computation(["operation"], 0), {})

    def test_records_from_before_versioned_runs_are_found_by_their_task(self: Any) -> None:
        old = [
            {"task_id": "pair", "task": {"group": "pairs"}, "status": "error", "value": None},
            {"task_id": "pair", "task": {"group": "pairs"}, "status": "ok", "value": 7},
            {"task_id": "other", "task": {"group": "pairs"}, "status": "ok", "value": 8},
        ]
        self.seed_unversioned(old)
        self.assertEqual(self.store.manifest(self.run_dir), {})
        self.assertEqual(self.store.recent_by_computation(["operation"], 3), {})
        for legacy in (False, True):
            found = self.store.unpinned(self.run_dir, legacy=legacy)
            self.assertEqual({name: row["value"] for name, row in found.items()}, {"pair": 7, "other": 8})

        self.record_run("first", "2026-01-01T00:00:01+00:00", 1)
        self.assertEqual(self.store.manifest(self.run_dir, legacy=True), {})
        kept = self.store.unpinned(self.run_dir, legacy=True)
        self.assertEqual({name: row["value"] for name, row in kept.items()}, {"pair": 7, "other": 8})
        self.assertEqual(self.store.unpinned(self.run_dir, legacy=False)["pair"]["value"], 1)

    def test_a_manifest_without_a_version_pins_nothing_and_is_reported_by_task(self: Any) -> None:
        self.seed_unversioned(
            [
                {"task_id": "pair", "task": {"group": "pairs"}, "status": "ok", "value": 7}
                | {"wall_seconds": 1, "peak_rss_mb": 50}
            ]
        )
        for unversioned in ({}, {"tasks": [{"id": "pair", "kind": "ext_pair"}]}):
            with self.assertRaisesRegex(RuntimeError, "versioned manifest"):
                selected_results(self.store, unversioned)
        self.assertEqual(self.store.manifest(self.run_dir), {})
        self.assertIn("| pairs | 1 | 1 |", render(self.run_dir, store=self.store))

    def test_one_writer_at_a_time(self: Any) -> None:
        with self.store, self.assertRaises(StoreLocked), self.make():
            self.fail("a second writer opened the store")
        with self.make():
            pass

    def test_a_dependency_graph_asks_the_store_whether_it_can_keep_one(self: Any) -> None:
        config = replace(
            fake_config([{"name": "a"}]),
            graph={"version": 1, "nodes": [{"id": "fake/a", "outputs": {"artifact": "k3-model"}}]},
        )
        tasks = [Task.from_payload({"id": "fake/a", "kind": "fake"})]

        def schedule() -> Scheduler:
            return Scheduler(
                config=config, tasks=tasks, store=self.store, run_dir=self.run_dir,
                runner=fake_runner(), guard=PollingGuard(),
            )  # fmt: skip

        if self.store.supports_graphs:
            self.assertIsNotNone(schedule().artifacts)
        else:
            with self.assertRaisesRegex(ConfigError, "dependency graph"):
                schedule()


class LinesContract(Contract, unittest.TestCase):
    def make(self) -> RunHistory:
        return ResultStore(self.run_dir / "results.jsonl")

    def seed_unversioned(self, records: list[dict[str, Any]]) -> None:
        with (self.run_dir / "results.jsonl").open("a", encoding="utf-8") as handle:
            handle.writelines(json.dumps(record) + "\n" for record in records)

    def test_results_are_in_the_run_directory_and_graphs_are_not_kept(self) -> None:
        self.assertEqual(self.store.location, self.run_dir)
        self.assertFalse(self.store.supports_graphs)


class DatabaseContract(Contract, unittest.TestCase):
    def make(self) -> RunHistory:
        return SQLiteStore(self.root / "results.sqlite")

    def seed_unversioned(self, records: list[dict[str, Any]]) -> None:
        LinesContract.seed_unversioned(self, records)  # type: ignore[arg-type]
        with SQLiteStore(self.root / "results.sqlite") as store:
            store.import_jsonl(self.run_dir)
        (self.run_dir / "results.jsonl").unlink()

    def test_results_are_in_the_database_and_graphs_are_kept(self) -> None:
        self.assertEqual(self.store.location, (self.root / "results.sqlite").resolve())
        self.assertTrue(self.store.supports_graphs)


if __name__ == "__main__":
    unittest.main()
