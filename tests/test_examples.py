"""The examples a reader starts from: each script runs, and the batch file agrees with its predictions."""

from __future__ import annotations

import json
import shutil
import subprocess
import sys
import tempfile
import tomllib
import unittest
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
EXAMPLES = REPOSITORY / "data" / "examples"
BATCH = EXAMPLES / "own-surfaces.toml"
SCHEDULER = (sys.executable, "-m", "batch")
GUARD = ("--memory-guard", "poll")
RECORDED = {"seed": 1, "characteristic": 32003}  # the one seed and prime of the committed records


def macaulay2(script: Path) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        ["M2", "--script", str(script.relative_to(REPOSITORY))],
        capture_output=True,
        text=True,
        cwd=REPOSITORY,
        timeout=300,
    )


class Layout(unittest.TestCase):
    def test_the_guide_names_every_example(self) -> None:
        guide = (REPOSITORY / "GUIDE.md").read_text(encoding="utf-8")
        names = sorted(path.name for path in EXAMPLES.iterdir())
        self.assertEqual(
            names,
            ["own-pair.m2", "own-surface.m2", "own-surfaces.toml", "own-word.m2", "resumable-quartic.m2"],
        )
        for name in names:
            self.assertIn(f"data/examples/{name}", guide)

    def test_the_example_batch_is_on_other_surfaces_and_outside_the_claims(self) -> None:
        # every task of data/batches/ must belong to a claim; a reader's surfaces belong to none
        self.assertFalse((REPOSITORY / "data" / "batches" / BATCH.name).exists())
        surfaces = tomllib.loads(BATCH.read_text(encoding="utf-8"))["surfaces"]
        self.assertEqual(sorted({surface["d"] for surface in surfaces}), [2, 3, 4])
        for surface in surfaces:
            chosen = {key: surface[key] for key in RECORDED}
            self.assertNotEqual(chosen, RECORDED)


@unittest.skipUnless(shutil.which("M2"), "Macaulay2 is not installed")
class Scripts(unittest.TestCase):
    def test_every_script_runs_and_its_assertions_hold(self) -> None:
        for script in sorted(EXAMPLES.glob("*.m2")):
            with self.subTest(script=script.name):
                done = macaulay2(script)
                self.assertEqual(done.returncode, 0, done.stdout[-2000:] + done.stderr[-2000:])

    def test_a_surface_of_another_degree_prime_and_seed_agrees_with_the_predictions(self) -> None:
        output = macaulay2(EXAMPLES / "own-surface.m2").stdout
        self.assertIn("degree 6 in P^4 over the field of 101 elements, seed 7", output)
        self.assertIn("15 of 15 invariants agree with their predictions", output)

    def test_a_word_gives_its_class_and_says_what_it_cannot_build(self) -> None:
        output = macaulay2(EXAMPLES / "own-word.m2").stdout
        self.assertIn("{rank, divisor, Euler component}: {-9, {3}, -2}", output)
        self.assertIn("twist realization unsupported: a longer word requires derived evaluation", output)

    def test_a_pair_gives_its_ext_groups_or_says_there_is_no_method(self) -> None:
        output = macaulay2(EXAMPLES / "own-pair.m2").stdout
        self.assertIn("{M_H, M_x, {0, 0, 1}, 1, Serre duality}", output)
        self.assertIn("{O_x, O_x, , 0, not computed}", output)


@unittest.skipUnless(sys.platform.startswith("linux") and shutil.which("M2"), "requires M2 on Linux")
class Batch(unittest.TestCase):
    def test_the_example_batch_agrees_with_its_predictions_on_every_surface(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            done = subprocess.run(
                [*SCHEDULER, "run", str(BATCH.relative_to(REPOSITORY)), "--out", scratch, *GUARD],
                capture_output=True,
                text=True,
                cwd=REPOSITORY,
                timeout=600,
            )
            self.assertEqual(done.returncode, 0, done.stdout[-2000:] + done.stderr[-2000:])
            lines = (Path(scratch) / "results.jsonl").read_text(encoding="utf-8").splitlines()
        records = [json.loads(line) for line in lines]
        self.assertEqual(len(records), 84)
        self.assertEqual({record["status"] for record in records}, {"ok"})
        self.assertTrue(all(record["agrees"] is True for record in records))
        surfaces = {record["task_id"].split("/")[1] for record in records}
        self.assertEqual(surfaces, {"d2-p101-s2", "d2-p10007-s3", "d3-p101-s5", "d4-p10007-s4"})


if __name__ == "__main__":
    unittest.main()
