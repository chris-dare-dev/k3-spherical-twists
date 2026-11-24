"""The command line with fake tasks: planning, running, reporting, exit statuses, interruption."""

from __future__ import annotations

import json
import os
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

from batch.cli import EXIT_FAILED, EXIT_INTERRUPTED, EXIT_LIMITS, EXIT_OK, EXIT_USAGE, exit_status
from batch.records import SQLiteStore
from batch.runner import REPOSITORY, code_version
from batch.tasks import Status

from .helpers import FAKE_RUNNER, FILE_VERSIONS, Journal, fake_runner, still_runs

HEADER = """
name = "cli"
[scheduler]
workers = 4
memory_budget_mb = 400
[limits]
time_seconds = 20
memory_mb = 100
"""


def items(*entries: str, limits: str = "") -> str:
    return f'[[tasks]]\nkind = "fake"\n{limits}\nitems = [{", ".join(entries)}]\n'


AGREEING = items('{ name = "a", value = 1, predicted = 1 }', '{ name = "b", cost = 3 }')
DIFFERING = items('{ name = "differs", value = 1, predicted = 2 }')
SLEEPING = items('{ name = "sleeper", sleep = 60 }', limits="limits = { time_seconds = 0.3 }")


class ExitStatus(unittest.TestCase):
    def test_a_failure_outweighs_a_limit_and_a_limit_outweighs_success(self) -> None:
        for statuses, expected in (
            ([], EXIT_OK),
            (["ok", "ok"], EXIT_OK),
            (["ok", "unsupported"], EXIT_OK),
            (["ok", "timeout"], EXIT_LIMITS),
            (["memory", "unsupported"], EXIT_LIMITS),
            (["ok", "mismatch"], EXIT_FAILED),
            (["timeout", "error"], EXIT_FAILED),
            (["memory", "crashed", "ok"], EXIT_FAILED),
            (["unsupported", "blocked"], EXIT_FAILED),
            (["ok", "a status of a later version"], EXIT_LIMITS),
        ):
            with self.subTest(statuses=statuses):
                self.assertEqual(exit_status(statuses), expected)
                self.assertEqual(exit_status(iter(statuses)), expected)
        self.assertEqual(exit_status(list(Status)), EXIT_FAILED)


class CommandLine(unittest.TestCase):
    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.scratch = Path(scratch.name)
        self.run_dir = self.scratch / "run"
        self.journal = Journal(self.scratch / "journal")
        self.runner = shlex.join(fake_runner(self.journal.path))

    def batch(self, *task_sets: str) -> Path:
        path = self.scratch / "cli.toml"
        path.write_text(HEADER + "\n".join(task_sets))
        return path

    def command(self, verb: str, *arguments: object) -> list[str]:
        command = [sys.executable, "-m", "batch", verb, *map(str, arguments)]
        if verb != "report":
            command += ["--runner", self.runner, "--out", str(self.run_dir)]
        return command

    def cli(self, verb: str, *arguments: object) -> subprocess.CompletedProcess[str]:
        return subprocess.run(
            self.command(verb, *arguments), capture_output=True, text=True, cwd=REPOSITORY, timeout=120
        )

    def records(self) -> list[dict]:
        path = self.run_dir / "results.jsonl"
        return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []

    def test_run_wall_deadline_preserves_committed_work_for_resume(self) -> None:
        batch = self.batch(items('{ name = "quick" }', '{ name = "slow", sleep = 2.5 }'))
        database = self.scratch / "ledger.sqlite"
        options = ("--store", database, "--workers", 1, "--memory-guard", "poll")
        first = self.cli("run", batch, *options, "--run-time-limit", 1.5)
        self.assertEqual(first.returncode, EXIT_LIMITS, first.stderr)
        self.assertIn("run wall deadline", first.stderr)
        store = SQLiteStore(database)
        manifest = store.manifest(self.run_dir)
        self.assertEqual(manifest["run_state"], "interrupted")
        self.assertEqual([r["task_id"] for r in store.query(run_id=manifest["run_id"])], ["fake/quick"])
        self.assertTrue(all(not still_runs(pid) for pid in self.journal.pids()))
        second = self.cli("run", batch, *options)
        self.assertEqual(second.returncode, EXIT_OK, second.stderr)
        self.assertIn("1 to compute, 1 already recorded", second.stderr)

    def test_weighted_cpu_admission_respects_the_run_budget(self) -> None:
        batch = self.batch(
            items('{ name = "big", sleep = 0.6 }', limits="limits = { cpu_cores = 2 }"),
            items('{ name = "small" }'),
        )
        done = self.cli("run", batch, "--cpu-budget", 2, "--memory-guard", "poll")
        self.assertEqual(done.returncode, EXIT_OK, done.stderr)
        spans = self.journal.intervals()
        self.assertGreaterEqual(spans["fake/small"][0], spans["fake/big"][1])
        self.assertEqual([row["limits"]["cpu_cores"] for row in self.records()], [2, 1])

    def test_run_then_rerun_then_report(self) -> None:
        batch = self.batch(AGREEING)
        plan = self.cli("plan", batch)
        self.assertEqual(plan.returncode, EXIT_OK, plan.stderr)
        self.assertIn("2 tasks, 2 to compute, 0 already recorded", plan.stdout)
        self.assertEqual(self.journal.started(), [])
        self.assertFalse(self.run_dir.exists())

        first = self.cli("run", batch)
        self.assertEqual(first.returncode, EXIT_OK, first.stderr)
        self.assertIn("this run: 2 ok", first.stderr)
        self.assertEqual(len(self.records()), 2)

        second = self.cli("run", batch)
        self.assertEqual(second.returncode, EXIT_OK, second.stderr)
        self.assertIn("this run: nothing to do", second.stderr)
        self.assertEqual(len(self.journal.started()), 2)
        self.assertEqual(len(self.records()), 2)
        self.assertIn("2 tasks, 0 to compute, 2 already recorded", self.cli("plan", batch).stdout)

        report = self.cli("report", self.run_dir, "--full")
        self.assertEqual(report.returncode, EXIT_OK, report.stderr)
        self.assertIn("| fake | 2 | 2 |", report.stdout)
        self.assertIn("| `fake/a` | 1 | 1 | yes | fake |", report.stdout)

    def test_the_configuration_of_each_run_is_recorded_with_the_results(self) -> None:
        batch = self.batch(AGREEING)
        self.cli("run", batch, "--workers", 2, "--time-limit", 7)
        self.cli("run", batch)
        runs = [json.loads(line) for line in (self.run_dir / "runs.jsonl").read_text().splitlines()]
        self.assertEqual(len(runs), 2)
        self.assertEqual(runs[0]["config"]["scheduler"], {"workers": 2, "memory_budget_mb": 400})
        self.assertEqual(runs[0]["config"]["limits"]["time_seconds"], 7)
        self.assertEqual((runs[0]["tasks"], runs[0]["pending"], runs[1]["pending"]), (2, 2, 0))
        self.assertEqual(runs[0]["runner"], FILE_VERSIONS)
        self.assertEqual(runs[0]["code"], code_version())
        self.assertIn(runs[0]["memory_guard"], ("cgroup", "poll"))
        for record in self.records():
            self.assertEqual(record["run_id"], runs[0]["run_id"])
            self.assertEqual(record["limits"]["time_seconds"], 7)
            self.assertEqual(record["code"], runs[0]["code"])
        manifest = json.loads((self.run_dir / "manifest.json").read_text())
        self.assertEqual([task["id"] for task in manifest["tasks"]], ["fake/a", "fake/b"])

    def test_tasks_keep_using_the_captured_source_after_a_commit_or_edit(self) -> None:
        for sqlite in (False, True):
            for commit in (False, True):
                with self.subTest(sqlite=sqlite, commit=commit):
                    self._assert_run_uses_snapshot(sqlite=sqlite, commit=commit)

    def _assert_run_uses_snapshot(self, *, sqlite: bool, commit: bool) -> None:
        checkout = self.scratch / f"checkout-{sqlite}-{commit}"
        shutil.copytree(
            REPOSITORY / "src" / "batch",
            checkout / "src" / "batch",
            ignore=shutil.ignore_patterns("__pycache__"),
        )
        shutil.copy2(FAKE_RUNNER, checkout / "src" / "batch" / "runner")
        self.run_dir = checkout / "results"
        database = self.run_dir / "ledger.sqlite"
        source = checkout / "src" / "macaulay2" / "K3Twists.m2"
        source.parent.mkdir()
        source.write_text("before capture\n")

        def git(*args: str) -> str:
            return subprocess.check_output(["git", *args], cwd=checkout, text=True).strip()

        git("init", "-q")
        git("config", "user.name", "batch test")
        git("config", "user.email", "batch@example.invalid")
        (checkout / ".gitignore").write_text("__pycache__/\nresults/\n")
        git("add", ".")
        git("commit", "-qm", "initial source")
        before = git("rev-parse", "HEAD")
        journal = Journal(checkout.parent / f"{checkout.name}.journal")
        runner = (sys.executable, "src/batch/runner/fake_runner.py", "--journal", str(journal.path))
        self.runner = shlex.join(runner)
        mutate = (
            '{ name = "first", read_source = true, '
            f"edit_source = {json.dumps(str(checkout))}, commit_source = {str(commit).lower()} }}"
        )
        observe = '{ name = "second", cost = 1, read_source = true }'
        options = ("--store", database) if sqlite else ()

        def run(*entries: str) -> None:
            done = subprocess.run(
                self.command("run", self.batch(items(*entries)), "--workers", 1,
                             "--memory-guard", "poll", *options),
                cwd=checkout, capture_output=True, text=True, timeout=30,
                env={**os.environ, "PYTHONPATH": str(checkout / "src")},
            )  # fmt: skip
            self.assertEqual(done.returncode, EXIT_OK, done.stderr)

        def records() -> list[dict]:
            if sqlite:
                store = SQLiteStore(database)
                manifest = store.manifest(self.run_dir)
                return store.query(run_id=manifest["run_id"])
            return self.records()

        run(mutate, observe)
        self.assertEqual(journal.started(), ["fake/first", "fake/second"])
        self.assertEqual(source.read_text(), "after capture\n")
        after = git("rev-parse", "HEAD")
        self.assertEqual(after != before, commit)
        first_records = records()
        self.assertCountEqual([r["task_id"] for r in first_records], ["fake/first", "fake/second"])
        for record in first_records:
            self.assertEqual(record["value"], ["before capture\n"] * 2)
            self.assertEqual(record["code"], {"commit": before, "dirty": False})

        run(observe)
        later = records()[-1]
        self.assertEqual(later["value"], ["after capture\n"] * 2)
        self.assertEqual(later["code"], {"commit": after, "dirty": not commit})
        prior = next(r for r in first_records if r["task_id"] == later["task_id"])
        self.assertNotEqual(later["computation_id"], prior["computation_id"])

    def test_exit_status_tells_failures_from_limits(self) -> None:
        stopped = self.cli("run", self.batch(AGREEING, SLEEPING))
        self.assertEqual(stopped.returncode, EXIT_LIMITS, stopped.stderr)
        self.assertIn("1 timeout", stopped.stderr)

        failed = self.cli("run", self.batch(AGREEING, SLEEPING, DIFFERING))
        self.assertEqual(failed.returncode, EXIT_FAILED, failed.stderr)
        self.assertIn("computed 1, predicted 2", failed.stderr)

        report = self.cli("report", self.run_dir).stdout
        self.assertIn("## Computed values that differ from the predicted ones", report)
        self.assertIn("| `fake/differs` | 1 | 2 |", report)
        self.assertIn("## Stopped at a limit", report)
        self.assertIn("| `fake/sleeper` | timeout | 0 | 0.3 | 100 |", report)

    def test_retry_runs_stopped_tasks_again(self) -> None:
        batch = self.batch(AGREEING, SLEEPING)
        self.cli("run", batch)
        again = self.cli("run", batch, "--retry", "timeout,memory")
        self.assertEqual(again.returncode, EXIT_LIMITS, again.stderr)
        # The watchdog may time out before the runner emits a start event.
        # The two persisted attempts establish the retry independently of startup time.
        rows = self.records()
        attempts = [row for row in rows if row["task_id"] == "fake/sleeper"]
        self.assertEqual([row["status"] for row in attempts], ["timeout", "timeout"])
        self.assertEqual(len({row["attempt_id"] for row in attempts}), 2)
        self.assertEqual(len(rows), 4)
        self.assertCountEqual([row["task_id"] for row in rows if row["status"] == "ok"], ["fake/a", "fake/b"])
        self.assertCountEqual(
            [task_id for task_id in self.journal.started() if task_id != "fake/sleeper"], ["fake/a", "fake/b"]
        )

    def test_changed_definition_and_removed_task_only_affect_the_new_report(self) -> None:
        first = self.cli("run", self.batch(AGREEING, DIFFERING))
        self.assertEqual(first.returncode, EXIT_FAILED, first.stderr)
        old_manifest = json.loads((self.run_dir / "manifest.json").read_text())
        old_id = old_manifest["run_id"]

        revised = self.batch(items('{ name = "a", value = 2, predicted = 2 }'))
        plan = self.cli("plan", revised)
        self.assertIn("1 tasks, 1 to compute, 0 already recorded", plan.stdout)
        second = self.cli("run", revised)
        self.assertEqual(second.returncode, EXIT_OK, second.stderr)
        self.assertEqual(self.journal.started().count("fake/a"), 2)
        self.assertEqual(json.loads((self.run_dir / "runs" / f"{old_id}.json").read_text()), old_manifest)

        latest = self.cli("report", self.run_dir, "--full").stdout
        self.assertIn("| fake | 1 | 1 |", latest)
        self.assertIn("| `fake/a` | 2 | 2 | yes |", latest)
        self.assertNotIn("fake/differs", latest)
        pinned = self.cli("report", self.run_dir, "--run", old_id, "--full").stdout
        self.assertIn("| `fake/a` | 1 | 1 | yes |", pinned)
        self.assertIn("| `fake/differs` | 1 | 2 |", pinned)

    def test_revised_prediction_compares_an_existing_observation(self) -> None:
        original = self.batch(items('{ name = "a", value = 1, predicted = 2, comparison = "equals" }'))
        initial = self.cli("run", original)
        self.assertEqual(initial.returncode, EXIT_FAILED, initial.stderr)
        old_manifest = json.loads((self.run_dir / "manifest.json").read_text())
        revised = self.batch(items('{ name = "a", value = 1, predicted = 1, comparison = "equals" }'))
        result = self.cli("run", revised)
        self.assertEqual(result.returncode, EXIT_OK, result.stderr)
        new_task = json.loads((self.run_dir / "manifest.json").read_text())["tasks"][0]
        self.assertEqual(new_task["record_id"], old_manifest["tasks"][0]["record_id"])
        self.assertNotEqual(new_task["check_id"], old_manifest["tasks"][0]["check_id"])
        self.assertEqual(len(self.records()), 1)
        self.assertEqual(self.journal.started(), ["fake/a"])
        self.assertIn("| `fake/a` | 1 | 1 | yes |", self.cli("report", self.run_dir, "--full").stdout)
        old = self.cli("report", self.run_dir, "--run", old_manifest["run_id"], "--full")
        self.assertIn("| `fake/a` | 1 | 2 |", old.stdout)

    def test_increasing_a_wall_time_limit_retries_a_timeout(self) -> None:
        batch = self.batch(items('{ name = "slow", sleep = 0.4 }', limits="limits = { time_seconds = 0.1 }"))
        first = self.cli("run", batch)
        self.assertEqual(first.returncode, EXIT_LIMITS, first.stderr)
        batch = self.batch(items('{ name = "slow", sleep = 0.4 }', limits="limits = { time_seconds = 5 }"))
        second = self.cli("run", batch)
        self.assertEqual(second.returncode, EXIT_OK, second.stderr)
        before, after = self.records()
        pinned = self.cli("report", self.run_dir, "--run", before["run_id"]).stdout
        self.assertIn("| `fake/slow` | timeout | 0 | 0.1 |", pinned)
        self.assertEqual(before["computation_id"], after["computation_id"])
        self.assertNotEqual(before["record_id"], after["record_id"])
        self.assertEqual((before["status"], after["status"]), ("timeout", "ok"))

    def test_legacy_rows_are_readable_but_are_recomputed(self) -> None:
        batch = self.batch(AGREEING)
        first = self.cli("run", batch)
        self.assertEqual(first.returncode, EXIT_OK, first.stderr)
        legacy = [
            {key: value for key, value in record.items() if key not in {"schema_version", "record_id"}}
            for record in self.records()
        ]
        (self.run_dir / "results.jsonl").write_text("".join(json.dumps(row) + "\n" for row in legacy))
        (self.run_dir / "manifest.json").unlink()
        report = self.cli("report", self.run_dir, "--full")
        self.assertIn("| `fake/a` | 1 | 1 | yes |", report.stdout)
        again = self.cli("run", batch)
        self.assertEqual(again.returncode, EXIT_OK, again.stderr)
        self.assertEqual(self.journal.started().count("fake/a"), 2)
        self.assertEqual(self.records()[:2], legacy)
        historic = self.cli("report", self.run_dir, "--legacy", "--full")
        self.assertEqual(historic.returncode, EXIT_OK, historic.stderr)
        self.assertIn("unversioned historical records", historic.stdout)
        self.assertIn("| `fake/a` | 1 | 1 | yes |", historic.stdout)

    def test_an_edited_runner_with_the_same_version_invalidates_prior_results(self) -> None:
        script = self.scratch / "runner.py"
        original = FAKE_RUNNER.read_text()
        script.write_text(original)
        self.runner = shlex.join(fake_runner(self.journal.path, script=script))
        batch = self.batch(items('{ name = "a", value = 1 }'))
        first = self.cli("run", batch)
        self.assertEqual(first.returncode, EXIT_OK, first.stderr)

        script.write_text(
            original.replace('task.get("value", len(held))', 'task.get("value", len(held)) + 2')
        )
        second = self.cli("run", batch)
        self.assertEqual(second.returncode, EXIT_OK, second.stderr)
        before, after = self.records()
        self.assertEqual(before["runner"], after["runner"])
        self.assertEqual(before["task"], after["task"])
        self.assertEqual((before["value"], after["value"]), (1, 3))
        self.assertNotEqual(before["computation_id"], after["computation_id"])

    def test_sqlite_cli_pins_reused_observations_and_keeps_jsonl_export_standalone(self) -> None:
        database = self.scratch / "results.sqlite"
        batch = self.batch(items('{ name = "a", value = 1, predicted = 2, comparison = "equals" }'))
        plan = self.cli("plan", batch, "--store", database, "--memory-guard", "poll")
        self.assertEqual(plan.returncode, EXIT_OK, plan.stderr)
        self.assertFalse(database.exists())
        first = self.cli("run", batch, "--store", database, "--memory-guard", "poll")
        self.assertEqual(first.returncode, EXIT_FAILED, first.stderr)
        original_dir = self.run_dir
        old_run = SQLiteStore(database).manifest(original_dir)["run_id"]

        self.run_dir = self.scratch / "second"
        batch = self.batch(items('{ name = "a", value = 1, predicted = 1, comparison = "equals" }'))
        reused = self.cli("run", batch, "--store", database, "--memory-guard", "poll")
        self.assertEqual(reused.returncode, EXIT_OK, reused.stderr)
        self.assertIn("this run: nothing to do", reused.stderr)
        self.assertEqual(self.journal.started(), ["fake/a"])
        current = self.cli("report", self.run_dir, "--store", database, "--full")
        self.assertEqual(current.returncode, EXIT_OK, current.stderr)
        self.assertIn("| `fake/a` | 1 | 1 | yes |", current.stdout)
        old = self.cli("report", original_dir, "--store", database, "--run", old_run, "--full")
        self.assertEqual(old.returncode, EXIT_OK, old.stderr)
        self.assertIn("| `fake/a` | 1 | 2 |", old.stdout)

        exported = subprocess.run(
            [sys.executable, "-m", "batch", "export-jsonl", "--store", str(database), "--method", "fake"],
            cwd=REPOSITORY,
            capture_output=True,
            text=True,
            timeout=10,
        )
        self.assertEqual(exported.returncode, EXIT_OK, exported.stderr)
        row = json.loads(exported.stdout)
        self.assertEqual(row["run_id"], old_run)
        self.assertEqual(row["predicted"], 2)
        self.assertEqual(Path(row["log_directory"]), original_dir.resolve())
        self.assertFalse((original_dir / "results.jsonl").exists())

    def test_what_cannot_run_is_refused_before_any_task_starts(self) -> None:
        batch = self.batch(AGREEING)
        refused = [
            self.cli("run", batch, "--memory-budget", 10**9),  # more than the machine has
            self.cli("run", batch, "--memory-limit", 500),  # a task limit above the budget
            self.cli("run", batch, "--retry", "sometimes"),
            self.cli("run", batch, "--workers", 0),
            self.cli("run", self.scratch / "missing.toml"),
            self.cli("report", self.scratch / "nothing-here"),
        ]
        for done in refused:
            self.assertEqual(done.returncode, EXIT_USAGE, done.stderr)
            self.assertIn("batch:", done.stderr)
        self.assertEqual(self.journal.started(), [])
        self.assertEqual(self.records(), [])

    def test_two_runs_cannot_write_to_the_same_results(self) -> None:
        batch = self.batch(items('{ name = "slow", sleep = 2 }'))
        first = subprocess.Popen(self.command("run", batch), cwd=REPOSITORY, stderr=subprocess.DEVNULL)
        self.addCleanup(first.wait)
        self.wait_for(lambda: len(self.journal.started()) == 1)
        second = self.cli("run", batch)
        self.assertEqual(second.returncode, EXIT_USAGE)
        self.assertIn("another run is writing", second.stderr)
        self.assertEqual(first.wait(), EXIT_OK)
        self.assertEqual(len(self.journal.started()), 1)

    def wait_for(self, condition: object, seconds: float = 20) -> None:
        deadline = time.monotonic() + seconds
        while not condition():  # type: ignore[operator]
            if time.monotonic() > deadline:
                self.fail("timed out waiting")
            time.sleep(0.02)

    def start_long_run(self) -> subprocess.Popen[bytes]:
        long = items(*(f'{{ name = "long-{i}", sleep = 60, cost = 1 }}' for i in range(3)))
        quick = items('{ name = "quick" }')
        process = subprocess.Popen(
            self.command("run", self.batch(quick, long)), cwd=REPOSITORY, stderr=subprocess.DEVNULL
        )
        self.wait_for(lambda: len(self.journal.started()) == 4 and len(self.records()) == 1)
        return process

    def assert_gone(self, pids: list[int]) -> None:
        self.wait_for(lambda: not any(still_runs(pid) for pid in pids), seconds=5)

    def test_an_interrupted_run_stops_its_tasks_and_a_rerun_computes_them(self) -> None:
        for stop in (signal.SIGINT, signal.SIGTERM):
            with self.subTest(signal=stop.name):
                process = self.start_long_run()
                process.send_signal(stop)
                self.assertEqual(process.wait(timeout=20), EXIT_INTERRUPTED)
                self.assert_gone(self.journal.pids())
                # the finished task keeps its record; the three in flight have none
                self.assertEqual([record["task_id"] for record in self.records()], ["fake/quick"])
                plan = self.cli("plan", self.scratch / "cli.toml").stdout
                self.assertIn("4 tasks, 3 to compute, 1 already recorded", plan)
                self.journal.path.unlink()
                (self.run_dir / "results.jsonl").unlink()

    def test_tasks_do_not_outlive_a_killed_scheduler(self) -> None:
        process = self.start_long_run()
        os.kill(process.pid, signal.SIGKILL)
        process.wait(timeout=20)
        self.assert_gone(self.journal.pids())
        self.assertEqual([record["task_id"] for record in self.records()], ["fake/quick"])


if __name__ == "__main__":
    unittest.main()
