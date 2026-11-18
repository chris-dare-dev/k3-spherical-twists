"""Exercise the marked-quartic graph through the Linux CLI and its pinned report."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

from k3batch.artifacts import ArtifactStore
from k3batch.runner import REPOSITORY


@unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("M2"), "requires M2 on Linux")
class ResumableQuartic(unittest.TestCase):
    def test_two_observations_reuse_one_realization_after_checkpoint(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            ledger = root / "study.sqlite"
            output = root / "run"
            database = ("--store", str(ledger))
            batch = "batches/resumable-quartic.toml"
            run = ("run", batch, "--out", str(output), "--memory-guard", "poll", *database)

            def cli(*args: str, code: int = 0) -> str:
                done = subprocess.run(
                    [sys.executable, "-m", "k3batch", *args],
                    cwd=REPOSITORY,
                    capture_output=True,
                    text=True,
                    timeout=100,
                )
                self.assertEqual(done.returncode, code, done.stdout + done.stderr)
                return done.stderr + done.stdout

            def selected(run_id: str) -> dict:
                rows = map(json.loads, cli("export-jsonl", *database, "--run", run_id).splitlines())
                return {r["task_id"].split("/")[-1]: r for r in rows}

            def run_id(output: str) -> str:
                return next(
                    line.split()[1].rstrip(",") for line in output.splitlines() if line.startswith("run ")
                )

            first_output = cli(*run, "--checkpoint-after", "quartic_prefix/realize", code=130)
            self.assertIn("checkpoint committed", first_output)
            first_id = run_id(first_output)
            first = selected(first_id)
            self.assertEqual(set(first), {"model", "realize"})
            second_output = cli(*run)
            self.assertIn("2 to compute, 2 already recorded", second_output)
            second_id = run_id(second_output)
            records = selected(second_id)
            self.assertEqual(set(records), {"model", "realize", "cohomology", "ext"})
            durable = records["realize"]
            self.assertEqual(first["realize"]["attempt_id"], durable["attempt_id"])
            self.assertEqual(durable["value"], {"class": [-3, [1, 0], -1], "shift": 1})
            self.assertIn("RHom concentrated in degree zero", durable["detail"]["evidence"]["hypotheses"])
            model = first["model"]["detail"]["artifact_outputs"]["model"]["digest"]
            cone = durable["detail"]["artifact_outputs"]["cone"]["digest"]
            store = ArtifactStore(root / "study.sqlite.artifacts")
            self.assertEqual(
                json.loads(store.read(model))["payload"]["parameters"]["family"], "quartic_with_conic"
            )
            self.assertEqual(json.loads(store.read(cone))["payload"]["model_digest"], model)
            for name, table, support in (
                ("cohomology", [[-1, 0], [0, 0], [1, 4]], [-1, 1]),
                ("ext", [[1, 4], [2, 0], [3, 0]], [1, 3]),
            ):
                record = records[name]
                self.assertEqual(record["status"], "ok")
                self.assertTrue(record["agrees"])
                self.assertEqual(record["value"]["dimensions"], table)
                self.assertEqual(record["task"]["prediction"]["version"], "1")
                self.assertEqual(record["detail"]["evidence"]["support"], support)
                self.assertEqual(record["detail"]["evidence"]["shift"], 1)
                self.assertEqual(record["resource_controls"]["mode"], "sampled")
                source = record["detail"]["artifact_inputs"]
                self.assertEqual(source["surface"]["digest"], model)
                self.assertEqual(source["prefix"]["digest"], cone)
                self.assertEqual(source["prefix"]["attempt_id"], durable["attempt_id"])
            args = ("report", str(output), *database, "--run", second_id, "--full")
            report = cli(*args)
            self.assertIn(cone, report)
            self.assertIn(durable["attempt_id"], report)
            self.assertIn("sampled", report)
            self.assertIn("RHom concentrated in degree zero", report)
            cli(*run)
            self.assertEqual(cli(*args), report)

            revised = root / "revised.toml"
            original = (REPOSITORY / batch).read_text(encoding="utf-8")
            revised.write_text(
                original.replace('version = "1"', 'version = "2"', 1).replace("[1, 4]]", "[1, 5]]", 1),
                encoding="utf-8",
            )
            revision = cli(run[0], str(revised), *run[2:], code=1)
            self.assertIn("0 to compute, 4 already recorded", revision)
            invalid = selected(run_id(revision))["cohomology"]
            self.assertEqual(invalid["record_id"], records["cohomology"]["record_id"])
            self.assertNotEqual(invalid["check_id"], records["cohomology"]["check_id"])
            self.assertEqual(invalid["status"], "mismatch")
            self.assertEqual(cli(*args), report)
