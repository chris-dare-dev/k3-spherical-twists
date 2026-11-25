"""The scheduler with the Macaulay2 runner: a few real tasks, and limits that stop Macaulay2."""

from __future__ import annotations

import json
import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from batch.jobs import CgroupGuard, MemoryGuard, PollingGuard
from batch.records import ResultStore
from batch.runner import DEFAULT_RUNNER, RunnerInvocation, WireError, check_task, expand, parse_result
from batch.scheduler import Scheduler
from batch.tasks import parse_config

BATCH = {
    "name": "macaulay2",
    "scheduler": {"workers": 4, "memory_budget_mb": 2400},
    "limits": {"time_seconds": 120, "memory_mb": 600},
    "surfaces": [{"d": 2}],
    "tasks": [
        {"kind": "ext_pair", "sources": ["O(1H)", "M_x", "O_x"], "targets": ["M_H", "O_x"]},
        {"kind": "invariant", "names": ["h^i(M_x(-H))"]},
        {
            "kind": "synthetic",
            "limits": {"time_seconds": 3},
            "items": [{"name": "sleeps", "sleep_seconds": 120}],
        },
        {
            "kind": "synthetic",
            "items": [
                {"name": "allocates", "allocate_mb": 1500, "sleep_seconds": 120},
                {"name": "fails", "fail": True},
                {"name": "differs", "value": 1, "predicted": 2},
            ],
        },
    ],
}


@unittest.skipUnless(shutil.which(DEFAULT_RUNNER[0]), "Macaulay2 is not installed")
class Macaulay2Runner(unittest.TestCase):
    guard_class: type[MemoryGuard] = PollingGuard

    def run_batch(self, run_dir: Path) -> tuple[int, dict[str, dict]]:
        config = parse_config(BATCH)
        tasks, versions = expand(DEFAULT_RUNNER, config.description)
        with ResultStore(run_dir / "results.jsonl") as store:
            outcome = Scheduler(
                config=config, tasks=tasks, store=store, run_dir=run_dir, runner=DEFAULT_RUNNER,
                guard=self.guard_class(), stamp={"runner": versions},
            ).run()  # fmt: skip
        return outcome.total(), store.latest()

    def test_real_tasks_and_limits(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        ran, records = self.run_batch(Path(scratch.name))
        self.assertEqual(ran, 11)

        def pair(source: str, target: str) -> dict:
            return records[f"ext_pair/d2-p32003-s1/{source}/{target}"]

        self.assertEqual(pair("O(1H)", "M_H")["value"], {"dims": [0, 1, 15], "chi": 14})
        self.assertEqual(pair("O(1H)", "M_H")["predicted"], {"chi": 14})
        self.assertEqual(pair("M_x", "O_x")["value"]["dims"], [2, 0, 0])
        self.assertEqual(pair("M_x", "M_H")["value"]["dims"], [1, 0, 0])
        for record in (pair("O(1H)", "M_H"), pair("M_x", "O_x"), pair("M_x", "M_H"), pair("O_x", "M_H")):
            self.assertEqual((record["status"], record["agrees"]), ("ok", True))
            self.assertEqual(
                record["task"]["surface"],
                {"d": 2, "seed": 1, "characteristic": 32003, "special_quadric": False},
            )
            self.assertRegex(record["runner"]["m2_version"], r"^\d+\.\d+")
            self.assertGreater(record["peak_rss_mb"], 50)
            self.assertGreater(record["detail"]["compute_seconds"], 0)
        self.assertEqual(pair("O_x", "M_H")["detail"]["method"], "Serre duality")

        unsupported = pair("O_x", "O_x")
        self.assertEqual((unsupported["status"], unsupported["value"]), ("unsupported", None))
        self.assertEqual(unsupported["predicted"], {"chi": 0})

        invariant = records["invariant/d2-p32003-s1/h^i(M_x(-H))"]
        self.assertEqual(
            (invariant["status"], invariant["value"], invariant["predicted"]), ("ok", [0, 0, 11], [0, 0, 11])
        )

        self.assertEqual(records["synthetic/sleeps"]["status"], "timeout")
        self.assertLess(records["synthetic/sleeps"]["wall_seconds"], 10)
        self.assertEqual(records["synthetic/allocates"]["status"], "memory")
        self.assertLess(records["synthetic/allocates"]["wall_seconds"], 60)
        self.assertEqual(records["synthetic/fails"]["status"], "error")
        self.assertIn("synthetic task asked to fail", records["synthetic/fails"]["error"])
        self.assertEqual(records["synthetic/differs"]["status"], "mismatch")

        again, _ = self.run_batch(Path(scratch.name))
        self.assertEqual(again, 0)


@unittest.skipUnless(CgroupGuard.available(), "systemd-run --user --scope is not available")
class Macaulay2RunnerUnderCgroupLimits(Macaulay2Runner):
    guard_class = CgroupGuard


@unittest.skipUnless(shutil.which(DEFAULT_RUNNER[0]), "Macaulay2 is not installed")
class Macaulay2FileProtocol(unittest.TestCase):
    def invoke(self, command: list[str], *, check: bool = True) -> subprocess.CompletedProcess[str]:
        return subprocess.run(command, text=True, capture_output=True, check=check, timeout=25)

    def test_legacy_and_file_transports_produce_the_same_tasks_and_values(self) -> None:
        value = {
            "integer": 2**90 + 1,
            "fraction": -0.1501,
            "optional": None,
            "string": 'quote: " and braces: { }',
            "real_zero": 0.0,
        }
        description = {
            "surfaces": [{"d": 2, "seed": None}],
            "tasks": [
                {"kind": "ext_pair", "sheaves": ["O"]},
                {"kind": "invariant", "names": ["rank M_x"]},
                {"kind": "synthetic", "items": [{"name": "fixture", "value": value}]},
            ],
        }
        expanded = self.invoke([*DEFAULT_RUNNER, "expand", json.dumps(description)])
        legacy = [json.loads(line[6:]) for line in expanded.stdout.splitlines() if line.startswith("@task ")]
        tasks, versions = expand(DEFAULT_RUNNER, description)
        self.assertEqual(versions["protocol_version"], 2)
        self.assertEqual([task.payload for task in tasks], legacy)

        with tempfile.TemporaryDirectory() as scratch:
            for task, expected in zip(tasks, ({"dims": [1, 0, 1], "chi": 2}, 2, value), strict=True):
                with self.subTest(kind=task.kind):
                    old = self.invoke([*DEFAULT_RUNNER, "run", json.dumps(task.payload)])
                    invocation = RunnerInvocation.prepare(DEFAULT_RUNNER, "run", task.payload, Path(scratch))
                    try:
                        new = self.invoke(invocation.command)
                        result = invocation.task_result(new.stdout, new.returncode)
                        self.assertNotIn("@result", new.stdout)
                    finally:
                        invocation.cleanup()
                    old_result = parse_result(old.stdout)
                    assert old_result is not None and result is not None
                    selected = ("status", "value", "predicted", "agrees", "method")
                    self.assertEqual(
                        {key: result[key] for key in selected}, {key: old_result[key] for key in selected}
                    )
                    self.assertEqual(result["value"], expected)
                    if task.kind == "synthetic":
                        self.assertIs(type(result["value"]["real_zero"]), float)

    def test_macaulay2_and_python_refuse_the_same_tasks(self) -> None:
        tasks, _ = expand(DEFAULT_RUNNER, {"tasks": [{"kind": "synthetic", "items": [{"name": "x"}]}]})
        task = tasks[0].payload
        self.assertEqual(check_task(task), tasks[0])
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        invocation = RunnerInvocation.prepare(DEFAULT_RUNNER, "run", task, Path(scratch.name))
        request = Path(invocation.command[-2])
        assert invocation.request is not None
        envelope = json.loads(request.read_text(encoding="utf-8"))
        for change, python, macaulay2 in (
            ({"id": ""}, "id must be a nonempty string", "task requires a string field id"),
            ({"set": -1}, "set must be an integer >= 0", "nonnegative integer field set"),
            ({"kind_version": 0}, "kind_version must be an integer >= 1", "kind_version must be positive"),
            ({"cost": -1}, "cost must be a nonnegative number", "task requires a nonnegative cost"),
            ({"requirements": "none"}, "requirements must be a list", "task requires a list of requirements"),
        ):
            with self.subTest(change=change):
                with self.assertRaisesRegex(WireError, python):
                    check_task(task | change)
                request.write_text(json.dumps(envelope | {"payload": task | change}), encoding="utf-8")
                done = self.invoke(invocation.command, check=False)
                self.assertNotEqual(done.returncode, 0)
                self.assertIn(macaulay2, done.stderr + done.stdout)
                with self.assertRaisesRegex(WireError, "operation_failed"):
                    invocation.request.read(done.returncode)
        request.write_text(json.dumps(envelope), encoding="utf-8")
        done = self.invoke(invocation.command)
        result = invocation.task_result(done.stdout, done.returncode)
        assert result is not None
        self.assertEqual(result["status"], "ok")

    def test_macaulay2_validates_file_headers_and_reports_a_structured_failure(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            invocation = RunnerInvocation.prepare(DEFAULT_RUNNER, "expand", {}, Path(scratch))
            request = Path(invocation.command[-2])
            assert invocation.request is not None
            for fields, expected in (
                ({"version": 8}, "unsupported protocol version"),
                ({"operation_version": 3}, "unsupported operation version"),
                ({"payload": {"tasks": [{"kind": "synthetic"}]}}, "synthetic set is missing items"),
            ):
                with self.subTest(fields=fields):
                    envelope = json.loads(request.read_text(encoding="utf-8")) | fields
                    request.write_text(json.dumps(envelope), encoding="utf-8")
                    done = self.invoke(invocation.command, check=False)
                    self.assertNotEqual(done.returncode, 0)
                    self.assertIn(expected, done.stderr + done.stdout)
                    with self.assertRaisesRegex(WireError, "invalid_request|operation_failed"):
                        invocation.request.read(done.returncode)
                    # Restore the original envelope before the next mutation.
                    envelope.update({"version": 2, "operation_version": 1, "payload": {}})
                    request.write_text(json.dumps(envelope), encoding="utf-8")
            request.write_text(request.read_text(encoding="utf-8") + "{}", encoding="utf-8")
            done = self.invoke(invocation.command, check=False)
            self.assertNotEqual(done.returncode, 0)
            self.assertIn("expected exactly one request object", done.stderr + done.stdout)
            invocation.cleanup()


if __name__ == "__main__":
    unittest.main()
