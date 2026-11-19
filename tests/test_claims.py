"""The registry of claims and the tables generated from it."""

from __future__ import annotations

import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
from typing import Any

from k3batch.runner import DEFAULT_RUNNER, REPOSITORY

from . import helpers

sys.path.insert(0, str(REPOSITORY / "tools"))

import claims

MACAULAY2 = shutil.which(DEFAULT_RUNNER[0]) is not None


def listed(task_id: str, *batches: str, **payload: Any) -> claims.Listed:
    return {
        "id": task_id,
        "payload": {"id": task_id, "kind": "invariant"} | payload,
        "batches": list(batches),
    }


def record(
    task: claims.Listed,
    status: str = "ok",
    value: Any = 1,
    day: str = "2026-11-17",
    batch: str | None = None,
    **payload: Any,
) -> dict[str, Any]:
    """The record of `task` as it is now, in a run directory named `batch`; `payload` changes its task."""
    built = helpers.record(
        task["payload"] | payload,
        status,
        value=value,
        predicted=task["payload"].get("predicted"),
        agrees=status == "ok",
        wall_seconds=0.5,
        started_at=f"{day}T10:00:00+00:00",
        code={"commit": "a" * 40, "dirty": False},
    )
    return dict(built) | {"batch": batch or task["batches"][0]}


def by_id(*records: dict[str, Any]) -> dict[str, list[dict[str, Any]]]:
    found: dict[str, list[dict[str, Any]]] = {}
    for item in records:
        found.setdefault(item["task_id"], []).append(item)
    return found


FIRST = listed("invariant/d2/rank M_H", "invariants", predicted=3, surface={"d": 2})
SECOND = listed("invariant/d3/rank M_H", "long", predicted=4, surface={"d": 3})
SYNTHETIC = listed("synthetic/sleeps", "limits-demo") | {
    "payload": {"id": "synthetic/sleeps", "kind": "synthetic"}
}
# two batches use one id for two computations, and share a third task
POINT = listed("prefix/realize", "point", target="O_x")
BUNDLE = listed("prefix/realize", "bundle", target="O(1H)")
SHARED = listed("prefix/model", "bundle", "point")
TASKS: list[claims.Listed] = [FIRST, SECOND, SYNTHETIC, POINT, BUNDLE, SHARED]
CLAIM = {"id": "rank", "table": "t", "cells": ["rank M_H"], "tasks": ["invariant/*/rank M_H"]}
POINT_CLAIM = {"id": "point", "table": "t", "cells": ["x"], "tasks": ["prefix/*"], "batches": ["point"]}
BUNDLE_CLAIM = {"id": "bundle", "table": "t", "cells": ["x"], "tasks": ["prefix/*"], "batches": ["bundle"]}


@unittest.skipUnless(MACAULAY2, "Macaulay2 expands the batch files")
class Registry(unittest.TestCase):
    def test_the_registry_fits_the_batch_files(self) -> None:
        registry, tasks = claims.load_registry(), claims.batch_tasks()
        claims.validate(registry, tasks)
        self.assertGreater(len(tasks), 2000)
        self.assertEqual(len({claim["id"] for claim in registry["claim"]}), len(registry["claim"]))

    def test_the_dependent_batches_share_ids_and_not_computations(self) -> None:
        tasks = [task for task in claims.batch_tasks() if task["id"] == "quartic_prefix/realize"]
        self.assertGreater(len(tasks), 1)
        self.assertEqual({len(task["batches"]) for task in tasks}, {1})
        (model,) = [task for task in claims.batch_tasks() if task["id"] == "quartic_prefix/model"]
        self.assertEqual(sorted(model["batches"]), sorted(task["batches"][0] for task in tasks))

    def test_the_committed_tables_are_what_the_generator_writes(self) -> None:
        stale = [
            path.name for path, text in claims.outputs().items() if path.read_text(encoding="utf-8") != text
        ]
        self.assertEqual(stale, [], "run `make tables`")


class Validation(unittest.TestCase):
    def test_what_does_not_fit_is_reported(self) -> None:
        registry = {
            "table": {"t": {"heading": "T", "columns": ["a"]}},
            "claim": [
                {"id": "x", "table": "t", "cells": ["1"], "tasks": ["invariant/d4/*"]},
                {"id": "y", "table": "u", "cells": ["1"], "tasks": []},
                {"id": "z", "table": "t", "cells": ["1"], "tasks": ["prefix/*"], "batches": ["absent"]},
            ],
            "headline": [{"label": "l", "task": "invariant/d3/rank M_H"}],
        }
        with self.assertRaises(claims.RegistryError) as raised:
            claims.validate(registry, TASKS)
        message = str(raised.exception)
        for part in (
            "no task of its batches matches 'invariant/d4/*'",
            "no table 'u'",
            "either tasks or a reason",
            "no batch file 'absent'",
            "invariant/d2/rank M_H (invariants) belongs to no claim",
            "prefix/realize (point) belongs to no claim",
            "is not one task of batches/invariants.toml",
        ):
            self.assertIn(part, message)
        self.assertNotIn("synthetic", message)

    def test_a_star_after_a_number_is_refused(self) -> None:
        # "d2*" is meant for d = 2 and would also take d = 20
        registry: dict[str, Any] = {
            "table": {"t": {"heading": "T", "columns": ["a"]}},
            "claim": [
                {"id": "x", "table": "t", "cells": ["1"], "tasks": ["invariant/d2*", "invariant/d3/*"]},
                {"id": "p", "table": "t", "cells": ["1"], "tasks": ["prefix/*"]},
            ],
            "headline": [],
        }
        with self.assertRaisesRegex(claims.RegistryError, "the \\* follows a digit"):
            claims.validate(registry, TASKS)
        registry["claim"][0]["tasks"] = ["invariant/d2/*", "invariant/d3/*"]
        claims.validate(registry, TASKS)

    def test_synthetic_tasks_never_count_for_a_claim(self) -> None:
        everything = {"id": "c", "table": "t", "cells": ["x"], "tasks": ["*"]}
        self.assertNotIn(SYNTHETIC, claims.claim_tasks(everything, TASKS))

    def test_a_claim_that_names_batches_takes_their_tasks_only(self) -> None:
        self.assertEqual(claims.claim_tasks(POINT_CLAIM, TASKS), [SHARED, POINT])
        self.assertEqual(claims.claim_tasks(BUNDLE_CLAIM, TASKS), [SHARED, BUNDLE])


class Standing(unittest.TestCase):
    def test_a_record_counts_for_the_computation_it_was_made_for(self) -> None:
        records = by_id(record(POINT, value=5))
        self.assertEqual(claims.standing(POINT, records)[0], "ok")
        # the same id in another batch is another computation: this record says nothing about it
        self.assertEqual(claims.standing(BUNDLE, records), ("not re-run", None))

    def test_a_shared_task_is_answered_by_a_record_of_any_of_its_batches(self) -> None:
        self.assertEqual(claims.standing(SHARED, by_id(record(SHARED, batch="point")))[0], "ok")
        self.assertEqual(claims.standing(SHARED, by_id(record(SHARED, batch="elsewhere")))[0], "ok")

    def test_a_record_of_a_task_that_changed_since_is_stale(self) -> None:
        old = record(SECOND, value=5, predicted=5)
        self.assertEqual(claims.standing(SECOND, by_id(old))[0], "stale")
        moved = record(SECOND, set=3, cost=2, group="other")
        self.assertEqual(claims.standing(SECOND, by_id(moved))[0], "ok")
        # a record for the task as it is now counts, whatever was recorded for it before or after
        self.assertEqual(claims.standing(SECOND, by_id(old, record(SECOND, day="2026-11-01")))[0], "ok")

    def test_the_latest_record_for_the_task_wins(self) -> None:
        records = by_id(
            record(FIRST, "timeout", day="2026-11-17"), record(FIRST, day="2026-11-18", batch="b")
        )
        status, found = claims.standing(FIRST, records)
        self.assertEqual((status, found and found["batch"]), ("ok", "b"))

    def test_a_key_without_a_value_is_as_good_as_absent(self) -> None:
        self.assertTrue(claims.answers({"task": {"kind": "k", "seed": None}}, {"kind": "k", "id": "t"}))
        self.assertFalse(claims.answers({"task": {"kind": "k", "seed": 2}}, {"kind": "k"}))
        self.assertFalse(claims.answers({}, {"kind": "k"}))


class Summaries(unittest.TestCase):
    def test_a_claim_without_a_record_reads_not_re_run(self) -> None:
        text = claims.summary(CLAIM, TASKS, {})
        self.assertIn("**not re-run**: 2 tasks in `invariants`, `long`, no record", text)
        self.assertNotRegex(text, r"\bok\b")
        self.assertIn("**not re-run**: 2 tasks in `point`, no record", claims.summary(POINT_CLAIM, TASKS, {}))

    def test_a_claim_is_ok_only_when_every_task_is(self) -> None:
        text = claims.summary(CLAIM, TASKS, by_id(record(FIRST)))
        self.assertIn("tasks: ok 1; not re-run 1 (of 2); 2026-11-17, `aaaaaaa`", text)
        self.assertNotIn("**ok**", text)
        records = by_id(record(FIRST), record(SECOND, "mismatch"))
        self.assertIn("tasks: ok 1; mismatch 1 (of 2)", claims.summary(CLAIM, TASKS, records))
        records = by_id(record(FIRST), record(SECOND, day="2026-11-18"))
        self.assertIn("all 2 tasks **ok**; 2026-11-17 to 2026-11-18", claims.summary(CLAIM, TASKS, records))

    def test_a_stale_record_supports_nothing(self) -> None:
        old = record(SECOND, value=5, predicted=5)
        text = claims.summary(CLAIM, TASKS, by_id(record(FIRST), old))
        self.assertIn("tasks: ok 1; stale 1 (of 2); 2026-11-17, `aaaaaaa`", text)
        self.assertNotIn("**ok**", text)
        # a claim whose only records are stale names no day and no commit
        self.assertIn(
            "tasks: stale 1; not re-run 1 (of 2); [tasks]", claims.summary(CLAIM, TASKS, by_id(old))
        )
        page = claims.detail({"claim": [CLAIM]}, TASKS, by_id(old))
        self.assertIn(
            "| `invariant/d3/rank M_H` | long | 4 "
            "| stale: recorded 2026-11-17 at `aaaaaaa` for the task as it was then |  |",
            page,
        )

    def test_a_claim_without_tasks_says_why(self) -> None:
        claim = {"id": "c", "table": "t", "cells": ["x"], "tasks": [], "no_task": "a test of the package"}
        self.assertEqual(claims.summary(claim, TASKS, {}), "no task: a test of the package")

    def test_the_detail_page_lists_predicted_and_record(self) -> None:
        page = claims.detail({"claim": [CLAIM]}, TASKS, by_id(record(FIRST, value=3)))
        self.assertIn(
            "| `invariant/d2/rank M_H` | invariants | 3 | ok, 2026-11-17, `aaaaaaa`, 0.5 s | 3 |", page
        )
        self.assertIn("| `invariant/d3/rank M_H` | long | 4 | not re-run |  |", page)

    def test_the_headline_shows_no_value_for_a_stale_record(self) -> None:
        registry = {"headline": [{"label": "rank", "task": "invariant/d2/rank M_H"}]}
        row = "| rank | 3 | 3 | ok | `invariant/d2/rank M_H` |"
        self.assertIn(row, claims.headline(registry, TASKS, by_id(record(FIRST, value=3))))
        stale = by_id(record(FIRST, value=2, predicted=2))
        self.assertIn(
            "| rank | 3 |  | stale | `invariant/d2/rank M_H` |", claims.headline(registry, TASKS, stale)
        )

    def test_values_in_cells(self) -> None:
        self.assertEqual(claims.cell(1242), "1,242")
        self.assertEqual(claims.cell({"dims": [0, 0, 1], "chi": 1}), "dims (0, 0, 1), chi 1")
        self.assertEqual(claims.cell([[1, 4]]), "((1, 4))")
        self.assertEqual(claims.cell(True), "yes")
        self.assertEqual(claims.cell(None), "")
        self.assertEqual(len(claims.cell("x" * 500)), 160)


class Files(unittest.TestCase):
    def test_tasks_are_listed_once_per_computation_with_their_batches(self) -> None:
        one = {"id": "t", "kind": "k", "set": 0, "cost": 1}
        tasks = claims.list_tasks(
            {"a": [one], "b": [one | {"set": 4, "cost": 9}], "c": [one | {"target": "O_x"}]}
        )
        self.assertEqual([(task["id"], task["batches"]) for task in tasks], [("t", ["a", "b"]), ("t", ["c"])])

    def test_generated_parts_need_their_markers(self) -> None:
        begin, end = "<!-- BEGIN GENERATED x: tools/claims.py tables -->", "<!-- END GENERATED x -->"
        text = f"before\n{begin}\nold\n{end}\nafter\n"
        self.assertEqual(
            claims.splice(text, "x", ["new"], Path("f.md")), f"before\n{begin}\nnew\n{end}\nafter\n"
        )
        with self.assertRaises(claims.RegistryError):
            claims.splice("no markers", "x", ["new"], Path("f.md"))

    def test_records_are_read_from_every_run_directory(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            for name, day, status in (("a", "2026-11-17", "timeout"), ("b", "2026-11-18", "ok")):
                (Path(scratch) / name).mkdir()
                row = {key: value for key, value in record(FIRST, status, day=day).items() if key != "batch"}
                (Path(scratch) / name / "results.jsonl").write_text(json.dumps(row) + "\n")
            records = claims.committed_records(Path(scratch))
            found = [(item["batch"], item["status"]) for item in records[FIRST["id"]]]
            self.assertEqual(found, [("a", "timeout"), ("b", "ok")])
            self.assertEqual(claims.standing(FIRST, records)[0], "ok")
            self.assertEqual(claims.committed_records(Path(scratch) / "absent"), {})


if __name__ == "__main__":
    unittest.main()
