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
        self.check_checkpoint(
            "resumable-quartic",
            "O(1H)",
            1,
            {"class": [-3, [1, 0], -1], "shift": 1},
            {"cohomology": [[-1, 0], [0, 0], [1, 4]], "ext": [[1, 4], [2, 0], [3, 0]]},
        )

    def test_point_observations_reuse_the_version_two_cone(self) -> None:
        self.check_checkpoint(
            "resumable-quartic-point",
            "O_x",
            2,
            {"class": [-1, [0, 0], 0], "shift": 1},
            {"cohomology": [[-1, 0], [0, 0], [1, 1]], "ext": [[1, 1], [2, 0], [3, 0]]},
        )

    def test_hypercohomology_uses_the_reloaded_degree_two_cone(self) -> None:
        self.check_checkpoint(
            "resumable-quartic-hypercohomology",
            "O(-1H)",
            1,
            {"class": [-3, [-1, 0], -1], "shift": 0},
            {"hypercohomology": [[-1, 0], [0, 0], [1, 0], [2, 0], [3, 4]]},
        )

    def test_inverse_and_hypercohomology_share_one_saved_forward_prefix(self) -> None:
        self.check_checkpoint(
            "resumable-quartic-inverse",
            "O(-1H)",
            1,
            {"class": [-3, [-1, 0], -1], "shift": 0},
            {"hypercohomology": [[-1, 0], [0, 0], [1, 0], [2, 0], [3, 4]]},
            inverse=True,
        )

    def check_checkpoint(
        self,
        batch_name: str,
        target: str,
        artifact_version: int,
        realization: dict,
        tables: dict[str, list[list[int]]],
        *,
        inverse: bool = False,
    ) -> None:
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            ledger = root / "study.sqlite"
            output = root / "run"
            database = ("--store", str(ledger))
            batch = f"batches/{batch_name}.toml"
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
            self.assertIn(f"{len(tables) + inverse} to compute, 2 already recorded", second_output)
            second_id = run_id(second_output)
            records = selected(second_id)
            expected = {"model", "realize", *tables}
            if inverse:
                expected.add("inverse")
            self.assertEqual(set(records), expected)
            durable = records["realize"]
            self.assertEqual(first["realize"]["attempt_id"], durable["attempt_id"])
            self.assertEqual(durable["task"]["target"], target)
            self.assertEqual(durable["value"], realization)
            hypothesis = (
                "Serre-dual coordinate evaluation"
                if target == "O(-1H)"
                else "RHom concentrated in degree zero"
            )
            self.assertIn(hypothesis, durable["detail"]["evidence"]["hypotheses"])
            model = first["model"]["detail"]["artifact_outputs"]["model"]["digest"]
            cone = durable["detail"]["artifact_outputs"]["cone"]["digest"]
            store = ArtifactStore(root / "study.sqlite.artifacts")
            self.assertEqual(
                json.loads(store.read(model))["payload"]["parameters"]["family"], "quartic_with_line"
            )
            artifact = json.loads(store.read(cone))
            self.assertEqual(artifact["version"], artifact_version)
            self.assertEqual(artifact["payload"]["model_digest"], model)
            for name, table in tables.items():
                record = records[name]
                self.assertEqual(record["status"], "ok")
                self.assertTrue(record["agrees"])
                self.assertEqual(record["value"]["dimensions"], table)
                self.assertEqual(record["task"]["prediction"]["version"], "1")
                evidence = record["detail"]["evidence"]
                self.assertEqual(evidence["support"], [table[0][0], table[-1][0]])
                self.assertEqual(evidence["convention"], "cohomological")
                if name != "hypercohomology":
                    self.assertEqual(evidence["shift"], 1)
                self.assertEqual(record["resource_controls"]["mode"], "sampled")
                source = record["detail"]["artifact_inputs"]
                self.assertEqual(source["surface"]["digest"], model)
                self.assertEqual(source["surface"]["attempt_id"], first["model"]["attempt_id"])
                self.assertEqual(source["prefix"]["digest"], cone)
                self.assertEqual(source["prefix"]["attempt_id"], durable["attempt_id"])
            if inverse:
                self.check_inverse(records["inverse"], durable, store, model, cone)
            args = ("report", str(output), *database, "--run", second_id, "--full")
            report = cli(*args)
            self.assertIn(cone, report)
            self.assertIn(durable["attempt_id"], report)
            self.assertIn("sampled", report)
            self.assertIn(hypothesis, report)
            if "hypercohomology" in tables:
                self.assertIn("degree-zero Koszul total complex", report)
            if inverse:
                self.assertIn("nonzero_dimensions ((3, 4))", report)
                self.assertIn("sheaf quasi-isomorphism with O(-H)", report)
                for name in ("evaluation", "augmentation"):
                    self.assertIn(durable["detail"]["artifact_outputs"][name]["digest"], report)
            cli(*run)
            self.assertEqual(cli(*args), report)

            revised = root / "revised.toml"
            original = (REPOSITORY / batch).read_text(encoding="utf-8")
            observation, table = next(iter(tables.items()))
            degree, dimension = next((d, n) for d, n in table if n)
            revised.write_text(
                original.replace('version = "1"', 'version = "2"', 1).replace(
                    f"[{degree}, {dimension}]]", f"[{degree}, {dimension + 1}]]", 1
                ),
                encoding="utf-8",
            )
            revision = cli(run[0], str(revised), *run[2:], code=1)
            self.assertIn(f"0 to compute, {len(records)} already recorded", revision)
            invalid = selected(run_id(revision))[observation]
            self.assertEqual(invalid["record_id"], records[observation]["record_id"])
            self.assertNotEqual(invalid["check_id"], records[observation]["check_id"])
            self.assertEqual(invalid["status"], "mismatch")
            self.assertEqual(cli(*args), report)

    def check_inverse(self, record: dict, forward: dict, store: ArtifactStore, model: str, cone: str) -> None:
        self.assertEqual(record["status"], "ok")
        self.assertTrue(record["agrees"])
        self.assertEqual(
            record["value"],
            {"class": [1, [-1, 0], 3], "serre_pairing_rank": 4, "sheaf_quasi_isomorphism": True},
        )
        self.assertEqual(record["detail"]["method"], "quartic-degree-two-inverse-cancellation")
        self.assertEqual(record["detail"]["evidence"]["directions"], [1, -1])
        inputs = record["detail"]["artifact_inputs"]
        outputs = forward["detail"]["artifact_outputs"]
        self.assertEqual(inputs["surface"]["digest"], model)
        self.assertEqual(inputs["prefix"]["digest"], cone)
        self.assertEqual(set(inputs), {"surface", "prefix"} | (outputs.keys() - {"cone"}))
        for name in inputs.keys() - {"surface"}:
            self.assertEqual(inputs[name]["attempt_id"], forward["attempt_id"])
            self.assertEqual(inputs[name]["digest"], outputs["cone" if name == "prefix" else name]["digest"])
        for name, target in (("evaluation", "evaluation_target"), ("augmentation", "augmentation_target")):
            artifact = json.loads(store.read(inputs[name]["digest"]))
            self.assertEqual(artifact["kind"], "graded-chain-map")
            self.assertEqual(artifact["payload"]["source_digest"], inputs["evaluation_source"]["digest"])
            self.assertEqual(artifact["payload"]["target_digest"], inputs[target]["digest"])
            self.assertEqual(artifact["payload"]["model_digest"], model)
