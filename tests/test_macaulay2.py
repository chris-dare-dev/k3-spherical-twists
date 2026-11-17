"""The scheduler with the Macaulay2 runner: a few real tasks, and limits that stop Macaulay2."""

from __future__ import annotations

import shutil
import tempfile
import unittest
from pathlib import Path

from k3batch.config import parse_config
from k3batch.memory import CgroupGuard, MemoryGuard, PollingGuard
from k3batch.runner import DEFAULT_RUNNER, expand
from k3batch.scheduler import Scheduler
from k3batch.store import ResultStore

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


if __name__ == "__main__":
    unittest.main()
