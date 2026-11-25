"""Replay the arrow fixtures and check that their chain witnesses reach the ledger."""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from batch.records import ResultStore
from batch.runner import REPOSITORY


@unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("M2"), "requires M2 on Linux")
class HNArrows(unittest.TestCase):
    def test_recorded_squares_and_attachments(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            run = subprocess.run(
                [sys.executable, "-m", "batch", "run", "data/batches/hn-arrows.toml",
                 "--out", scratch, "--memory-guard", "poll"],
                cwd=REPOSITORY, capture_output=True, text=True, timeout=120,
            )  # fmt: skip
            self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
            records = {
                r["task"]["case"]: r for r in ResultStore(Path(scratch) / "results.jsonl").latest().values()
            }
        self.assertEqual(
            set(records),
            {
                "cone-split",
                "cone-u",
                "fibre-uu",
                "fibre-uv",
                "fibre-vu",
                "fibre-vv",
                "point-forward",
                "ideal-inverse",
            },
        )
        for name, record in records.items():
            with self.subTest(case=name):
                self.assertEqual(record["status"], "ok")
                self.assertEqual(record["value"], record["predicted"])
                evidence = record["detail"]["evidence"]
                for arrow in (
                    "input_map",
                    "cut",
                    "reference",
                    "source_identification",
                    "output_identification",
                    "lower_projection",
                    "quotient_identification",
                ):
                    self.assertIn(arrow, evidence)
                self.assertIn("terms", evidence["output"])
        self.assertEqual(
            [records["fibre-" + pair]["value"]["yoneda"] for pair in ("uu", "uv", "vu", "vv")], [0, 1, -1, 0]
        )
