"""The scheduler with fake tasks: outcomes, isolation, resumption, ordering, the memory budget."""

from __future__ import annotations

import unittest
from unittest.mock import patch

from batch.jobs import CgroupGuard
from batch.records import Record, ResultStore
from batch.scheduler import Scheduler
from batch.tasks import ConfigError

from ..helpers import FILE_VERSIONS, MARKER_VERSIONS, SchedulerCase, fake_config

SLEEPER = {"name": "sleeper", "sleep": 60}
HOG = {"name": "hog", "allocate_mb": 400, "sleep": 60}


class Outcomes(SchedulerCase):
    def test_each_way_a_task_can_end_is_recorded(self) -> None:
        config = fake_config(
            [
                {"name": "fine", "value": 7, "predicted": 7},
                {"name": "no-prediction", "value": [1, 0, 1]},
                {"name": "differs", "value": 1, "predicted": 2},
                {"name": "no-method", "unsupported": True, "predicted": 5},
                {"name": "fails", "exit": 3},
                {"name": "segfault", "signal": "SIGSEGV"},
                {"name": "says-nothing", "silent": True},
                {"name": "garbled", "garbled": True},
            ],
            {"items": [SLEEPER], "limits": {"time_seconds": 0.4}},
            [HOG],
        )
        outcome = self.run_batch(config)

        self.assertEqual(
            self.statuses(),
            {
                "fine": "ok",
                "no-prediction": "ok",
                "differs": "mismatch",
                "no-method": "unsupported",
                "fails": "error",
                "segfault": "crashed",
                # no result is a crash for marker lines; the file protocol knows the response is missing
                "says-nothing": "crashed" if self.markers else "error",
                "garbled": "crashed" if self.markers else "error",
                "sleeper": "timeout",
                "hog": "memory",
            },
        )
        self.assertEqual(outcome.total(), 10)
        records = {task_id.removeprefix("fake/"): record for task_id, record in self.latest().items()}

        for name, record in records.items():
            self.assertLessEqual(set(record), set(Record.__annotations__), name)

        fine = records["fine"]
        self.assertEqual((fine["value"], fine["predicted"], fine["agrees"]), (7, 7, True))
        self.assertEqual(fine["task"]["name"], "fine")
        timing = {} if self.markers else {"setup_seconds": 0, "compute_seconds": 0}
        self.assertEqual(fine["detail"], {"method": "fake"} | timing)
        self.assertEqual(fine["limits"], {"time_seconds": 20, "memory_mb": 100})
        self.assertEqual(fine["runner"], MARKER_VERSIONS if self.markers else FILE_VERSIONS)
        self.assertEqual(fine["code"], {"commit": "0" * 40, "dirty": False})
        self.assertEqual(fine["memory_guard"], self.guard_class.name)
        self.assertGreater(fine["peak_rss_mb"], 1)
        self.assertGreaterEqual(fine["wall_seconds"], 0)
        self.assertIsNone(fine["log"])

        self.assertEqual(records["no-prediction"]["agrees"], None)
        self.assertEqual((records["differs"]["value"], records["differs"]["agrees"]), (1, False))
        # a task that computed nothing still carries the predicted value it was given
        self.assertEqual(records["no-method"]["predicted"], 5)
        self.assertEqual(records["sleeper"]["predicted"], None)

        self.assertIn("asked to fail", records["fails"]["error"])
        self.assertEqual(records["fails"]["exit_code"], 3)
        self.assertEqual(records["segfault"]["exit_signal"], "SIGSEGV")
        if self.markers:
            self.assertEqual(records["says-nothing"]["error"], "ended without a result")
            self.assertEqual(records["garbled"]["error"], "ended without a result")
        else:
            self.assertIn("exited successfully without a response", records["says-nothing"]["error"])
            self.assertIn("invalid response JSON", records["garbled"]["error"])

        self.assertEqual(records["sleeper"]["exit_signal"], "SIGKILL")
        self.assertLess(records["sleeper"]["wall_seconds"], 5)
        self.assertEqual(records["sleeper"]["limits"]["time_seconds"], 0.4)
        self.assertLess(records["hog"]["wall_seconds"], 20)
        self.assertGreater(records["hog"]["peak_rss_mb"], 50)

        for name in ("fails", "segfault", "says-nothing", "garbled", "sleeper", "hog"):
            self.assertTrue((self.run_dir / records[name]["log"]).exists(), name)
        self.assertEqual(len(list((self.run_dir / "logs").iterdir())), 6)

    def test_a_killed_task_does_not_lose_the_others(self) -> None:
        quick = [{"name": f"quick-{i}", "sleep": 0.05, "value": i, "predicted": i} for i in range(12)]
        config = fake_config(
            quick[:6],
            {"items": [SLEEPER], "limits": {"time_seconds": 0.3}},
            [HOG],
            quick[6:],
            workers=3,
            memory_budget_mb=300,
        )
        self.run_batch(config)
        statuses = self.statuses()
        self.assertEqual(statuses.pop("sleeper"), "timeout")
        self.assertEqual(statuses.pop("hog"), "memory")
        self.assertEqual(statuses, {f"quick-{i}": "ok" for i in range(12)})


class Resumption(SchedulerCase):
    """The sleeper's time limit counts from the launch of its watchdog, and on a slow machine it can end
    before the runner has written its start line.  So the sleeper's attempts are counted in the records;
    the journal counts only the tasks that end by themselves."""

    def started_besides_the_sleeper(self) -> list[str]:
        return [task_id for task_id in self.journal.started() if task_id != "fake/sleeper"]

    def test_a_rerun_computes_nothing(self) -> None:
        config = fake_config(
            [{"name": "a"}, {"name": "b", "exit": 1}, {"name": "c", "value": 1, "predicted": 2}],
            {"items": [SLEEPER], "limits": {"time_seconds": 0.3}},
        )
        self.run_batch(config)
        self.assertEqual(self.statuses(), {"a": "ok", "b": "error", "c": "mismatch", "sleeper": "timeout"})
        self.assertCountEqual(self.started_besides_the_sleeper(), ["fake/a", "fake/b", "fake/c"])
        records = ResultStore(self.run_dir / "results.jsonl").records()
        started = self.journal.started()

        outcome = self.run_batch(config)
        self.assertEqual(outcome.total(), 0)
        self.assertEqual(ResultStore(self.run_dir / "results.jsonl").records(), records)
        self.assertEqual(self.journal.started(), started)

    def test_a_rerun_computes_only_what_has_no_record(self) -> None:
        first = [{"name": "a"}, {"name": "b"}]
        self.run_batch(fake_config(first))
        self.run_batch(fake_config([*first, {"name": "c"}, {"name": "d"}]))
        self.assertEqual(sorted(self.journal.started()), ["fake/a", "fake/b", "fake/c", "fake/d"])

    def test_retry_computes_again_the_chosen_statuses_only(self) -> None:
        config = fake_config(
            [{"name": "a"}, {"name": "b", "exit": 1}],
            {"items": [SLEEPER], "limits": {"time_seconds": 0.3}},
        )
        self.run_batch(config)
        outcome = self.run_batch(config, retry={"timeout"})
        self.assertEqual(dict(outcome), {"timeout": 1})
        # both attempts of the sleeper are on record, and nothing else ran again
        records = ResultStore(self.run_dir / "results.jsonl").records()
        attempts = [record for record in records if record["task_id"] == "fake/sleeper"]
        self.assertEqual([record["status"] for record in attempts], ["timeout", "timeout"])
        self.assertEqual(len({record["attempt_id"] for record in attempts}), 2)
        self.assertEqual(len(records), 4)
        self.assertCountEqual(self.started_besides_the_sleeper(), ["fake/a", "fake/b"])

    def test_interrupted_and_successful_retries_preserve_the_first_attempts_log(self) -> None:
        failed = fake_config([{"name": "retry", "exit": 1}])
        self.run_batch(failed)
        history = ResultStore(self.run_dir / "results.jsonl")
        first = history.latest()["fake/retry"]
        log = self.run_dir / first["log"]
        contents = log.read_bytes()
        self.assertIn(b"asked to fail", contents)
        self.assertIn(first["attempt_id"], log.name)

        with (
            patch.object(Scheduler, "_collect", side_effect=KeyboardInterrupt),
            self.assertRaises(KeyboardInterrupt),
        ):
            self.run_batch(failed, retry={"error"})
        self.assertEqual(log.read_bytes(), contents)
        self.assertEqual(history.records(), [first])
        interrupted_logs = set(log.parent.glob("*.log")) - {log}
        self.assertEqual(len(interrupted_logs), 1)

        self.assertEqual(self.run_batch(fake_config([{"name": "retry"}]), retry={"error"}), {"ok": 1})
        earlier, latest = history.records()
        self.assertEqual(earlier, first)
        self.assertNotEqual(latest["attempt_id"], first["attempt_id"])
        self.assertIsNone(latest["log"])
        self.assertEqual(log.read_bytes(), contents)
        self.assertEqual(set(log.parent.glob("*.log")), {log} | interrupted_logs)


class Scheduling(SchedulerCase):
    def test_cheapest_first_and_the_given_order_among_equals(self) -> None:
        costs = [5, 1, 3, 1, 0, 4, 3]
        items = [{"name": f"t{i}", "cost": cost} for i, cost in enumerate(costs)]
        self.run_batch(fake_config(items, workers=1))
        self.assertEqual(self.journal.started(), [f"fake/t{i}" for i in (4, 1, 3, 2, 6, 5, 0)])

    def test_limits_of_running_tasks_stay_within_the_budget(self) -> None:
        small = [{"name": f"small-{i}", "sleep": 0.3} for i in range(6)]
        large = [{"name": f"large-{i}", "sleep": 0.3, "cost": 10} for i in range(3)]
        config = fake_config(
            small,
            {"items": large, "limits": {"memory_mb": 250}},
            workers=4,
            memory_budget_mb=300,
            memory_mb=100,
        )
        self.run_batch(config)
        limit = {f"fake/small-{i}": 100 for i in range(6)} | {f"fake/large-{i}": 250 for i in range(3)}
        intervals = self.journal.intervals()
        self.assertEqual(len(intervals), 9)
        most_at_once = 0
        for start, _ in intervals.values():
            together = [task for task, (s, e) in intervals.items() if s <= start < e]
            most_at_once = max(most_at_once, len(together))
            self.assertLessEqual(sum(limit[task] for task in together), 300, together)
        # three small tasks fit the budget together; a large one runs alone
        self.assertEqual(most_at_once, 3)

    def test_workers_bound_the_number_of_processes(self) -> None:
        items = [{"name": f"t{i}", "sleep": 0.2} for i in range(6)]
        self.run_batch(fake_config(items, workers=2, memory_budget_mb=10_000))
        intervals = self.journal.intervals()
        for start, _ in intervals.values():
            self.assertLessEqual(sum(1 for s, e in intervals.values() if s <= start < e), 2)

    def test_tiers_give_costly_tasks_their_own_limits(self) -> None:
        items = [{"name": "cheap", "cost": 1}, {"name": "costly", "cost": 30, "sleep": 60}]
        tiers = [{"min_cost": 10, "time_seconds": 0.3, "memory_mb": 200}]
        self.run_batch(fake_config(items, tiers=tiers))
        records = self.latest()
        self.assertEqual(records["fake/cheap"]["limits"], {"time_seconds": 20, "memory_mb": 100})
        self.assertEqual(records["fake/costly"]["limits"], {"time_seconds": 0.3, "memory_mb": 200})
        self.assertEqual(records["fake/costly"]["status"], "timeout")

    def test_a_limit_above_the_budget_is_refused_before_anything_runs(self) -> None:
        config = fake_config([{"name": "a"}], {"items": [{"name": "b"}], "limits": {"memory_mb": 900}})
        with self.assertRaises(ConfigError):
            self.run_batch(config)
        self.assertEqual(self.journal.started(), [])


class OutcomesOfAMarkerLineRunner(Outcomes):
    markers = True


@unittest.skipUnless(CgroupGuard.available(), "systemd-run --user --scope is not available")
class OutcomesUnderCgroupLimits(Outcomes):
    guard_class = CgroupGuard


if __name__ == "__main__":
    unittest.main()
