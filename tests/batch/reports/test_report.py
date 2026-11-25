"""The report: every task of the manifest is counted, and each kind of outcome has its table."""

from __future__ import annotations

import json
import tempfile
import unittest
from pathlib import Path
from typing import Any

from batch.records import Record, ResultStore, build, commit, log_path, method, surface
from batch.reports import render, summary, tables
from batch.tasks import Limits, Status, Task


def task(name: str, group: str = "pairs d2", **more: Any) -> dict[str, Any]:
    return {"id": name, "kind": "ext_pair", "group": group, "cost": 3} | more


def record(name: str, status: str, **more: Any) -> dict[str, Any]:
    base = {
        "task_id": name,
        "task": task(name),
        "status": status,
        "value": None,
        "predicted": {"chi": 2},
        "agrees": None,
        "detail": {},
        "error": None,
        "wall_seconds": 1.5,
        "peak_rss_mb": 120.0,
        "limits": {"time_seconds": 60, "memory_mb": 500},
        "log": None,
        "runner": {"m2_version": "1.25.11"},
        "code": {"commit": "abc123", "dirty": False},
    }
    return base | more


class Report(unittest.TestCase):
    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.run_dir = Path(scratch.name) / "example"

    def write(self, tasks: list[dict[str, Any]], records: list[dict[str, Any]]) -> None:
        with ResultStore(self.run_dir / "results.jsonl") as store:
            for entry in records:
                store.append(entry)
        (self.run_dir / "manifest.json").write_text(json.dumps({"tasks": tasks}))

    def test_every_outcome_has_its_place(self) -> None:
        names = ["good", "bad", "slow", "big", "broken", "none", "waiting"]
        self.write(
            [task(name) for name in names] + [task("other", group="pairs d3")],
            [
                record(
                    "good",
                    "ok",
                    value={"dims": [1, 0, 1], "chi": 2},
                    agrees=True,
                    detail={"method": "Hom sheaf"},
                ),
                record("bad", "mismatch", value={"dims": [1, 0, 0], "chi": 1}, agrees=False),
                record("slow", "timeout", wall_seconds=60.1),
                record("big", "memory", peak_rss_mb=499.0),
                record(
                    "broken", "error", error="tasks.m2:1:1: error: no sheaf named X", log="logs/broken.log"
                ),
                record("none", "unsupported"),
            ],
        )
        report = render(self.run_dir, full=True)

        self.assertIn("# Results in example", report)
        self.assertIn("- code: abc123", report)
        self.assertIn("- runner: m2_version 1.25.11", report)
        self.assertIn(
            "| group | tasks | ok | mismatch | unsupported | timeout | memory | error | not run |", report
        )
        self.assertIn("| pairs d2 | 7 | 1 | 1 | 1 | 1 | 1 | 1 | 1 |", report)
        self.assertIn("| pairs d3 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |", report)
        self.assertIn("| `bad` | chi 1, dims (1, 0, 0) | chi 2 |", report)
        self.assertIn("| `slow` | timeout | 3 | 60 | 500 | 60.1 | 120 |", report)
        self.assertIn("| `big` | memory | 3 | 60 | 500 | 1.5 | 499 |", report)
        self.assertIn(
            "| `broken` | error | tasks.m2:1:1: error: no sheaf named X | logs/broken.log |", report
        )
        self.assertIn("| `none` | chi 2 |", report)
        self.assertIn("| `good` | chi 2, dims (1, 0, 1) | chi 2 | yes | Hom sheaf | 1.5 | 120 |", report)

    def test_the_latest_record_of_a_task_counts(self) -> None:
        self.write([task("a")], [record("a", "timeout"), record("a", "ok", value=1, agrees=True)])
        report = render(self.run_dir)
        self.assertIn("| pairs d2 | 1 | 1 |", report)
        self.assertNotIn("Stopped at a limit", report)
        self.assertIn("## Slowest computed tasks", report)

    def test_records_from_uncommitted_code_and_unreadable_lines_are_pointed_out(self) -> None:
        self.write([task("a")], [record("a", "ok", value=1, code={"commit": "abc123", "dirty": True})])
        with (self.run_dir / "results.jsonl").open("a") as handle:
            handle.write('{"task_id": "b", "sta')
        report = render(self.run_dir)
        self.assertIn("uncommitted changes", report)
        self.assertIn("1 unreadable line(s)", report)

    def test_results_without_a_manifest_are_still_reported(self) -> None:
        with ResultStore(self.run_dir / "results.jsonl") as store:
            store.append(record("a", "ok", value=1))
        self.assertIn("| pairs d2 | 1 | 1 |", render(self.run_dir))


def member(name: str, group: str = "pairs d2", **more: Any) -> dict[str, Any]:
    """A task as the manifest of a versioned run lists it."""
    surface = {"d": 2, "seed": 1}
    return {"id": name, "kind": "ext_pair", "group": group, "cost": 3, "predicted": {"chi": 2}} | {
        "surface": surface,
        "set": 0,
        "computation_id": f"computation-{name}",
        "check_id": "check",
        "record_id": f"record-{name}",
        "check": {},
        **more,
    }


def built(name: str, status: str, result: dict[str, Any] | None = None, **more: Any) -> Record:
    """The record the scheduler writes for an attempt of `member(name)`."""
    entry = member(name)
    fields: dict[str, Any] = {
        "status": Status(status),
        "result": result or {},
        "error": None,
        "attempt_id": f"attempt-{name}",
        "started_at": "2026-01-01T00:00:00+00:00",
        "log": None,
        "exit_code": 0,
        "wall_seconds": 1.5,
        "measured": {"cpu_seconds": 1.2, "peak_rss_mb": 120.04, "peak_sampled_bytes": 125 << 20},
        "resource_controls": {"mode": "sampled"},
        "memory_guard": "poll",
        "stamp": {"run_id": "run", "runner": {"m2_version": "1.25.11"}, "code": {"commit": "abc123"}},
        "computation_id": entry["computation_id"],
        "check_id": entry["check_id"],
        "record_id": entry["record_id"],
    }
    task = {key: entry[key] for key in ("id", "kind", "group", "cost", "predicted", "surface", "set")}
    return build(Task.from_payload(task), Limits(60, 500), **(fields | more))


class Tables(unittest.TestCase):
    """The report from records as the scheduler builds them, with no store and no run."""

    def setUp(self) -> None:
        computed = {"status": "ok", "value": {"dims": [1, 0, 1], "chi": 2}, "agrees": True, "method": "Hom"}
        produced = {"artifact_outputs": {"model": {"kind": "k3-model", "digest": "sha256:abc"}}}
        self.records = [
            built("good", "ok", computed | produced | {"evidence": "resolution of length 2"}),
            built("bad", "mismatch", computed | {"status": "mismatch", "value": {"chi": 1}, "agrees": False}),
            built("slow", "timeout", exit_code=-9, wall_seconds=60.1234, log="logs/slow.log"),
            built("big", "memory", exit_code=-9, measured={"peak_rss_mb": 499}, log="logs/big.log"),
            built(
                "broken", "error", error="tasks.m2:1:1: error: no sheaf\nnamed X", exit_code=1, log="b.log"
            ),
            built("stuck", "blocked", error="prerequisite good ended error"),
            built("none", "unsupported"),
        ]
        names = [record["task_id"] for record in self.records]
        self.manifest = {
            "schema_version": 1,
            "run_id": "run",
            "run_state": "completed",
            "tasks": [member(name) for name in names] + [member("waiting", group="pairs d3")],
        }
        self.selected = {record["task_id"]: record for record in self.records}

    def test_the_summary_counts_every_member_and_every_record(self) -> None:
        stray = built("stray", "ok", {"value": 1})
        counts = summary(self.manifest, self.selected | {"stray": stray})
        self.assertEqual(counts["pairs d3"], {"not run": 1})
        self.assertEqual(counts["pairs d2"]["ok"], 2)
        self.assertEqual(counts["pairs d2"].total(), 8)
        self.assertEqual(summary({}, {"stray": stray}), {"pairs d2": {"ok": 1}})

    def test_each_outcome_has_its_table(self) -> None:
        report = tables("example", self.manifest, self.selected, full=True)
        for line in (
            "# Results in example",
            "- run: `run`",
            "- run state: completed",
            "- records: 7",
            "- code: abc123",
            "- runner: m2_version 1.25.11",
            "| group | tasks | ok | mismatch | unsupported | timeout | memory | blocked | error | not run |",
            "| pairs d2 | 7 | 1 | 1 | 1 | 1 | 1 | 1 | 1 | 0 |",
            "| pairs d3 | 1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 1 |",
            "| `bad` | chi 1 | chi 2 |",
            "| `slow` | timeout | 3 | 60 | 500 | 60.123 | 120 |",
            "| `big` | memory | 3 | 60 | 500 | 1.5 | 499 |",
            "| `broken` | error | tasks.m2:1:1: error: no sheaf; named X | b.log |",
            "| `stuck` | blocked | prerequisite good ended error |  |",
            "| `none` | chi 2 |",
            "| `good` | dims (1, 0, 1), chi 2 | chi 2 | yes | Hom | 1.5 | 120 |",
            "| `good` | outputs | model | sha256:abc | good | attempt-good | sampled |",
            "| `good` | resolution of length 2 |  |",
        ):
            with self.subTest(line=line):
                self.assertIn(line, report)
        self.assertNotIn("Slowest", report)

        brief = tables("example", self.manifest, self.selected, legacy=True, unreadable=2)
        self.assertIn("- selection: unversioned historical records", brief)
        self.assertIn("- 2 unreadable line(s) in results.jsonl were ignored", brief)
        self.assertIn("| `good` | 3 | 1.5 | 120 |", brief)
        self.assertNotIn("## Artifacts", brief)

    def test_a_record_is_read_the_same_way_by_the_report_and_by_the_database(self) -> None:
        good, slow = self.records[0], self.records[2]
        self.assertEqual((surface(good), method(good), commit(good)), ({"d": 2, "seed": 1}, "Hom", "abc123"))
        self.assertEqual((method(slow), log_path(slow)), (None, "logs/slow.log"))
        elsewhere: Record = {**slow, "log_directory": "/runs/earlier"}
        self.assertEqual(log_path(elsewhere), "/runs/earlier/logs/slow.log")
        old: Record = {"task_id": "a", "status": "ok"}
        self.assertEqual((surface(old), method(old), commit(old), log_path(old)), (None, None, None, None))

    def test_every_field_the_scheduler_writes_is_declared(self) -> None:
        declared = set(Record.__annotations__)
        for record in self.records:
            self.assertLessEqual(set(record), declared, record["task_id"])
        self.assertEqual((self.records[2]["exit_code"], self.records[2]["exit_signal"]), (None, "SIGKILL"))
        self.assertEqual(self.records[5]["exit_code"], None)
        self.assertEqual(self.records[0]["peak_rss_mb"], 120.0)
        self.assertEqual(self.records[0]["predicted"], {"chi": 2})
        self.assertEqual(self.records[0]["schema_version"], 1)


if __name__ == "__main__":
    unittest.main()
