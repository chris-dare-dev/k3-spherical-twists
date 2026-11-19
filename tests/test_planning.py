"""The planner: from a history of records to what a run reuses, computes, tries again or refuses."""

from __future__ import annotations

import tempfile
import unittest
from collections.abc import Callable, Collection, Sequence
from dataclasses import replace
from pathlib import Path
from typing import Any
from uuid import uuid4

from k3batch.config import BatchConfig, ConfigError
from k3batch.graph import Graph
from k3batch.model import Limits, Task
from k3batch.planning import PlannedTask, Planner
from k3batch.resources import MIB, ResourcePolicy
from k3batch.runner import RunnerError
from k3batch.sqlite_store import SQLiteStore
from k3batch.store import ResultStore, RunHistory

from .fake_runner import expand as fake_tasks
from .helpers import fake_config

IMPLEMENTATION = "the code as it is"


def tasks_of(config: BatchConfig) -> list[Task]:
    return [Task.from_payload(task) for task in fake_tasks(config.description)]


class PlannerCase(unittest.TestCase):
    """A history that tests fill as a run would, and a planner that reads it."""

    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        self.run_dir = self.root / "run"
        self.run_dir.mkdir()
        self.history = self.make_history()
        self.clock = 0

    def make_history(self) -> RunHistory:
        return ResultStore(self.run_dir / "results.jsonl")

    def planner(
        self,
        config: BatchConfig,
        retry: Collection[str] = (),
        usable: Callable[[str, dict[str, Any]], bool] = lambda task_id, record: True,
    ) -> Planner:
        graph = Graph.build(tasks_of(config), config.graph)
        return Planner(
            config=config, graph=graph, history=self.history, guard="poll",
            cpu_cores=config.run_cores, retry=retry, usable=usable,
        )  # fmt: skip

    def plan(self, config: BatchConfig, **options: Any) -> dict[str, PlannedTask]:
        implementation = options.pop("implementation", IMPLEMENTATION)
        planned = self.planner(config, **options).plan(tasks_of(config), implementation)
        return {entry.task.id.removeprefix("fake/"): entry for entry in planned}

    def keep(self, planned: Sequence[PlannedTask], status: str = "ok", **fields: Any) -> None:
        """Record an attempt of each planned task that is not reused, as one run."""
        run_id = uuid4().hex
        manifest = {"run_id": run_id, "schema_version": 1, "tasks": [p.manifest_entry() for p in planned]}
        with self.history, self.history.run(self.run_dir, manifest, {"run_id": run_id}):
            for entry in planned:
                if entry.reused:
                    continue
                self.clock += 1
                attempt, started_at = uuid4().hex, f"2026-01-01T00:00:{self.clock:02d}+00:00"
                self.history.start_attempt(run_id, entry.manifest_entry(), attempt, started_at, None)
                stamps = {"attempt_id": attempt, "started_at": started_at, "run_id": run_id}
                self.history.append(self.ended(entry, status, **stamps) | fields)

    def ended(self, entry: PlannedTask, status: str, **fields: Any) -> dict[str, Any]:
        """The record of an attempt of a planned task, with what the planner reads of it."""
        predicted = entry.task.payload.get("predicted")
        value = None if status not in {"ok", "mismatch"} else entry.task.payload.get("value", 1)
        record = {
            "task_id": entry.task.id,
            "task": entry.task.payload,
            "status": status,
            "value": value,
            "predicted": predicted,
            "agrees": None if predicted is None or value is None else value == predicted,
            "detail": {"method": "fake"},
            "error": None,
            "limits": entry.limits.as_dict(),
            "wall_seconds": 4,
            "cpu_seconds": 2,
            "peak_rss_mb": 40.0,
            "peak_sampled_bytes": 40 * MIB,
            "cgroup_memory_peak_bytes": None,
            "cgroup_memory_events": None,
            "resource_controls": {"mode": "sampled"},
            "attempt_id": uuid4().hex,
            "trial_id": uuid4().hex,
            "started_at": "2026-01-01T00:00:00+00:00",
            "log": None,
            "schema_version": 1,
            "computation_id": entry.computation_id,
            "check_id": entry.check_id,
            "record_id": entry.record_id,
        }
        if entry.resources is not None:
            record["resource_context"] = entry.resources["fingerprint_context"]
        return record | fields


class Reuse(PlannerCase):
    def test_without_a_history_everything_is_computed(self) -> None:
        config = fake_config([{"name": "a"}, {"name": "b", "cost": 3}])
        first, again = self.plan(config), self.plan(config)
        for name in ("a", "b"):
            entry = first[name]
            self.assertEqual(
                (entry.reused, entry.check, entry.resources, entry.graph), (False, {}, None, None)
            )
            self.assertEqual(entry.limits, Limits(20, 100))
            self.assertRegex(entry.record_id, "^[0-9a-f]{32}$")
            # the computation is the same one; the record it would leave is a new one each time
            self.assertEqual(entry.computation_id, again[name].computation_id)
            self.assertNotEqual(entry.record_id, again[name].record_id)
        self.assertNotEqual(first["a"].computation_id, first["b"].computation_id)

    def test_the_latest_record_of_the_same_computation_answers_the_task(self) -> None:
        config = fake_config([{"name": "a", "sleep": 1}])
        first = self.plan(config)["a"]
        self.keep([first])
        stands = self.plan(config)["a"]
        self.assertEqual((stands.reused, stands.record_id, stands.check), (True, first.record_id, {}))

        # where a task sits in its batch is not what is computed; anything else of it is, and so is the code
        moved = self.plan(
            fake_config([{"name": "other"}], {"group": "g", "items": [{"name": "a", "sleep": 1, "cost": 9}]})
        )
        self.assertEqual((moved["a"].reused, moved["a"].record_id), (True, first.record_id))
        self.assertFalse(self.plan(fake_config([{"name": "a", "sleep": 2}]))["a"].reused)
        self.assertFalse(self.plan(config, implementation="edited code")["a"].reused)

        self.keep([self.plan(config, retry={"ok"})["a"]], value=5)
        self.assertNotEqual(self.plan(config)["a"].record_id, first.record_id)

    def test_a_chosen_status_or_a_larger_limit_computes_a_stopped_task_again(self) -> None:
        names = ("error", "timeout", "memory")
        config = fake_config([{"name": name} for name in names])
        planned = self.plan(config)
        for name in names:
            self.keep([planned[name]], status=name)

        def computed(config: BatchConfig, **options: Any) -> set[str]:
            return {name for name, entry in self.plan(config, **options).items() if not entry.reused}

        self.assertEqual(computed(config), set())
        self.assertEqual(computed(config, retry={"error"}), {"error"})
        self.assertEqual(computed(config, retry={"timeout", "memory"}), {"timeout", "memory"})
        items = [{"name": name} for name in names]
        self.assertEqual(computed(fake_config(items, time_seconds=30)), {"timeout"})
        self.assertEqual(computed(fake_config(items, memory_mb=150)), {"memory"})
        self.assertEqual(computed(fake_config(items, time_seconds=10, memory_mb=50)), set())

    def test_a_record_whose_output_cannot_be_read_does_not_answer_the_task(self) -> None:
        config = fake_config([{"name": "fine"}, {"name": "failed"}])
        planned = self.plan(config)
        self.keep([planned["fine"]])
        self.keep([planned["failed"]], status="error")
        asked = []

        def unreadable(task_id: str, record: dict[str, Any]) -> bool:
            asked.append((task_id, record["record_id"]))
            return False

        again = self.plan(config, usable=unreadable)
        # only a successful record promises an output
        self.assertEqual(asked, [("fake/fine", planned["fine"].record_id)])
        self.assertEqual((again["fine"].reused, again["failed"].reused), (False, True))


class Recheck(PlannerCase):
    def test_a_changed_prediction_is_checked_against_the_stored_value(self) -> None:
        def config(predicted: Any, **more: Any) -> BatchConfig:
            return fake_config(
                [{"name": "a", "value": 7, "predicted": predicted, "comparison": "equals"} | more]
            )

        first = self.plan(config(7))["a"]
        self.keep([first])
        self.assertEqual(self.plan(config(7))["a"].check, {})

        revised = self.plan(config(8))["a"]
        self.assertEqual((revised.reused, revised.record_id), (True, first.record_id))
        self.assertEqual(revised.computation_id, first.computation_id)
        self.assertNotEqual(revised.check_id, first.check_id)
        self.assertEqual(revised.check, {"status": "mismatch", "predicted": 8, "agrees": False})
        self.assertEqual(revised.manifest_entry()["check"], revised.check)
        self.assertEqual(
            self.plan(config(None))["a"].check, {"status": "ok", "predicted": None, "agrees": None}
        )

        # the status that counts for --retry is the one of the new check
        again = self.plan(config(8), retry={"mismatch"})["a"]
        self.assertEqual((again.reused, again.check), (False, {}))
        self.assertTrue(self.plan(config(8), retry={"ok"})["a"].reused)
        self.assertFalse(self.plan(config(7), retry={"ok"})["a"].reused)

    def test_named_fields_are_compared_and_must_have_been_computed(self) -> None:
        def config(predicted: Any) -> BatchConfig:
            value = {"dims": [1, 0, 1], "chi": 2}
            return fake_config(
                [{"name": "a", "value": value, "predicted": predicted, "comparison": "fields"}]
            )

        self.keep([self.plan(config({"chi": 2}))["a"]], agrees=True)
        self.assertEqual(
            self.plan(config({"chi": 3}))["a"].check,
            {"status": "mismatch", "predicted": {"chi": 3}, "agrees": False},
        )
        self.assertEqual(self.plan(config({"dims": [1, 0, 1]}))["a"].check["status"], "ok")
        with self.assertRaisesRegex(RunnerError, "missing predicted fields"):
            self.plan(config({"rank": 1}))

    def test_a_task_that_computed_nothing_keeps_its_status_under_a_new_prediction(self) -> None:
        def config(predicted: Any) -> BatchConfig:
            items = [
                {"name": name, "predicted": predicted, "comparison": "equals"} for name in ("slow", "none")
            ]
            return fake_config(items)

        planned = self.plan(config(1))
        self.keep([planned["slow"]], status="timeout")
        self.keep([planned["none"]], status="unsupported")
        revised = self.plan(config(2))
        self.assertEqual(revised["slow"].check, {"status": "timeout", "predicted": 2, "agrees": None})
        self.assertEqual(revised["none"].check, {"status": "unsupported", "predicted": 2, "agrees": None})
        self.assertTrue(revised["slow"].reused and revised["none"].reused)

    def test_without_a_declared_comparison_the_prediction_is_part_of_the_computation(self) -> None:
        self.keep([self.plan(fake_config([{"name": "a", "predicted": 1}]))["a"]])
        self.assertFalse(self.plan(fake_config([{"name": "a", "predicted": 2}]))["a"].reused)


class Refusal(PlannerCase):
    def test_a_task_above_a_budget_is_refused_unless_its_record_stands(self) -> None:
        large = {"items": [{"name": "large"}], "limits": {"memory_mb": 900}}
        with self.assertRaisesRegex(ConfigError, "fake/large has a memory limit of 900 MB, above the budget"):
            self.plan(fake_config([{"name": "a"}], large))
        self.keep([self.plan(fake_config(large, memory_budget_mb=1000))["large"]])
        self.assertTrue(self.plan(fake_config(large))["large"].reused)
        with self.assertRaisesRegex(ConfigError, "above the budget"):
            self.plan(fake_config(large), retry={"ok"})

        wide = fake_config({"items": [{"name": "wide"}], "limits": {"cpu_cores": 8}}, workers=4)
        with self.assertRaisesRegex(ConfigError, "fake/wide exceeds the run CPU budget"):
            self.plan(wide)


class Resources(PlannerCase):
    def policy(self, **fields: int) -> BatchConfig:
        config = fake_config([{"name": "a"}], memory_mb=42)
        return replace(config, resources=ResourcePolicy(**fields))

    def test_limits_come_from_comparable_successes_once_there_are_enough(self) -> None:
        config = self.policy(minimum_samples=2, memory_ceiling_mb=256)
        first = self.plan(config)["a"]
        assert first.resources is not None
        self.assertEqual(first.limits, Limits(20, 42, 1))
        self.assertEqual(first.resources["basis"], "configured defaults and tiers")
        self.assertEqual(first.manifest_entry()["resource_estimate"], first.resources)
        self.keep([first])
        second = self.plan(config, retry={"ok"})["a"]
        assert second.resources is not None
        # one success is on record and is named, but it is not enough to change the limits
        self.assertEqual((second.limits, second.resources["samples"]), (Limits(20, 42, 1), [first.record_id]))
        self.assertEqual(second.resources["basis"], "configured defaults and tiers")
        self.keep([second])

        informed = self.plan(config)["a"]
        assert informed.resources is not None
        self.assertEqual(informed.resources["basis"], "compatible successes")
        self.assertEqual(informed.resources["samples"], [second.record_id, first.record_id])
        # 1.5 times the longest wall time and a second; 1.3 times the largest peak; the busiest cores
        self.assertEqual(informed.limits, Limits(7, 52, 1))
        self.assertEqual((informed.reused, informed.record_id), (True, second.record_id))
        # a record measured under another guard is not comparable
        other = Planner(
            config=config, graph=Graph.build(tasks_of(config), None), history=self.history,
            guard="cgroup", cpu_cores=config.run_cores,
        ).plan(tasks_of(config), IMPLEMENTATION)[0]  # fmt: skip
        assert other.resources is not None
        self.assertEqual((other.resources["samples"], other.limits), ([], Limits(20, 42, 1)))

    def test_an_attempt_stopped_at_a_limit_is_tried_again_within_the_allowance(self) -> None:
        config = self.policy(retry_attempts=1, memory_ceiling_mb=100)
        planner = self.planner(config)
        (entry,) = planner.plan(tasks_of(config), IMPLEMENTATION)
        self.assertIsNone(planner.attempt_of("fake/a"))

        first = self.ended(entry, "memory", attempt_id="attempt")
        self.assertEqual(planner.settle(first), Limits(20, 63, 1))
        self.assertNotIn("resource_attempts", first)
        self.assertEqual(planner.attempt_of("fake/a"), "attempt")

        second = self.ended(entry, "memory", attempt_id="attempt", limits=Limits(20, 63, 1).as_dict())
        self.assertIsNone(planner.settle(second))
        self.assertEqual(
            [(trial["limits"]["memory_mb"], trial["decision"]) for trial in second["resource_attempts"]],
            [(42, "retry with larger reservation"), (63, "retry allowance exhausted")],
        )
        self.assertEqual(second["resource_attempts"][0]["trial_id"], first["trial_id"])
        self.assertIsNone(planner.attempt_of("fake/a"))

    def test_the_outcome_of_a_trial_decides_what_is_written_of_it(self) -> None:
        config = self.policy(retry_attempts=3, memory_ceiling_mb=42, time_ceiling_seconds=45)
        planner = self.planner(config)
        (entry,) = planner.plan(tasks_of(config), IMPLEMENTATION)

        def decisions(*statuses: str) -> list[str]:
            limits = entry.limits
            record: dict[str, Any] = {}
            for status in statuses:
                record = self.ended(entry, status, limits=limits.as_dict())
                limits = planner.settle(record) or limits
            return [trial["decision"] for trial in record.get("resource_attempts", [])]

        self.assertEqual(decisions("ok"), ["finished"])
        self.assertEqual(decisions("error"), ["finished"])
        self.assertEqual(decisions("memory"), ["ceiling reached"])
        self.assertEqual(
            decisions("timeout", "timeout", "timeout"),
            ["retry with larger reservation", "retry with larger reservation", "ceiling reached"],
        )
        self.assertEqual(decisions("timeout", "ok"), ["retry with larger reservation", "finished"])
        # a task blocked after a trial keeps the trial; one blocked before any has none
        self.assertEqual(decisions("timeout", "blocked"), ["retry with larger reservation"])
        self.assertEqual(decisions("blocked"), [])

        self.assertIsNotNone(planner.settle(self.ended(entry, "timeout")))
        planner.begin()
        self.assertIsNone(planner.attempt_of("fake/a"))

    def test_without_a_policy_every_record_stands_as_it_is(self) -> None:
        config = fake_config([{"name": "a"}])
        planner = self.planner(config)
        (entry,) = planner.plan(tasks_of(config), IMPLEMENTATION)
        record = self.ended(entry, "memory")
        self.assertIsNone(planner.settle(record))
        self.assertNotIn("resource_attempts", record)
        self.assertIsNone(planner.attempt_of("fake/a"))


class ReuseFromADatabase(Reuse):
    def make_history(self) -> RunHistory:
        return SQLiteStore(self.root / "results.sqlite")


class RecheckFromADatabase(Recheck):
    def make_history(self) -> RunHistory:
        return SQLiteStore(self.root / "results.sqlite")


class Dependencies(PlannerCase):
    def make_history(self) -> RunHistory:
        return SQLiteStore(self.root / "results.sqlite")

    def test_a_task_is_computed_again_when_the_record_of_its_prerequisite_is_another(self) -> None:
        source = {"producer": "fake/model", "output": "artifact", "kind": "k3-model"}
        config = replace(
            fake_config([{"name": "model"}, {"name": "reader"}, {"name": "alone"}]),
            graph={
                "version": 1,
                "nodes": [
                    {"id": "fake/model", "outputs": {"artifact": "k3-model"}},
                    {"id": "fake/reader", "inputs": {"value": source}},
                ],
            },
        )
        first = self.plan(config)
        contract = first["reader"].graph
        assert contract is not None
        self.assertEqual(contract["inputs"]["value"]["record_id"], first["model"].record_id)
        self.assertIsNone(first["alone"].graph)
        self.assertNotEqual(first["reader"].computation_id, self.plan(config)["reader"].computation_id)

        self.keep(list(first.values()))
        stands = self.plan(config)
        self.assertEqual({name: entry.reused for name, entry in stands.items()}, dict.fromkeys(first, True))
        self.assertEqual(stands["reader"].computation_id, first["reader"].computation_id)

        lost = self.plan(config, usable=lambda task_id, record: task_id != "fake/model")
        self.assertEqual(
            {name: entry.reused for name, entry in lost.items()},
            {"model": False, "reader": False, "alone": True},
        )


if __name__ == "__main__":
    unittest.main()
