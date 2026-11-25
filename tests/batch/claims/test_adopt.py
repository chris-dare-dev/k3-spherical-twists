"""Adoption: which records of a run may be committed, and what happens to them on the way."""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import Any
from uuid import uuid4

from batch.claims import adopt
from batch.jobs import PollingGuard
from batch.records import SQLiteStore
from batch.runner import REPOSITORY, expand
from batch.scheduler import Scheduler

from .. import helpers


def record(task_id: str, commit: str = "a" * 40, dirty: bool = False, **fields: Any) -> dict[str, Any]:
    code = {"commit": commit, "dirty": dirty}
    return dict(helpers.record({"id": task_id, "kind": "k"}, "ok", code=code, **fields))


def run_directory(scratch: str, *rows: dict[str, Any]) -> Path:
    run_dir = Path(scratch) / "results" / "trial"
    run_dir.mkdir(parents=True, exist_ok=True)
    (run_dir / "manifest.json").write_text("{}")
    (run_dir / "results.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in rows))
    return run_dir


def repository(root: Path) -> str:
    """A repository with one commit; its number."""

    def git(*arguments: str) -> str:
        identity = ["-c", "user.name=t", "-c", "user.email=t@example.org", "-c", "commit.gpgsign=false"]
        done = subprocess.run(
            ["git", "-C", str(root), *identity, *arguments], capture_output=True, text=True, check=True
        )
        return done.stdout.strip()

    root.mkdir()
    git("init", "-q")
    (root / "code.py").write_text("1\n")
    git("add", "code.py")
    git("commit", "-q", "-m", "first")
    return git("rev-parse", "HEAD")


class Adoption(unittest.TestCase):
    def test_only_records_of_committed_code_are_adopted(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            records = Path(scratch) / "records"
            run_dir = run_directory(scratch, record("t", dirty=True))
            with self.assertRaisesRegex(adopt.AdoptError, "uncommitted changes"):
                adopt.adopt(run_dir, records, REPOSITORY)
            run_dir = run_directory(scratch)
            with self.assertRaisesRegex(adopt.AdoptError, "no records"):
                adopt.adopt(run_dir, records, REPOSITORY)
            self.assertFalse(records.exists())

    def test_a_record_that_names_this_machine_is_not_adopted(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            row = record("t", error=f"work directory kept at {Path.home()}/somewhere")
            run_dir = run_directory(scratch, row)
            with self.assertRaisesRegex(adopt.AdoptError, "names this machine or a directory outside"):
                adopt.adopt(run_dir, Path(scratch) / "records", REPOSITORY)
            self.assertFalse((Path(scratch) / "records").exists())

    def test_a_record_follows_its_commit_through_a_rewrite_of_the_messages(self) -> None:
        def git(*arguments: str) -> str:
            identity = ["-c", "user.name=t", "-c", "user.email=t@example.org", "-c", "commit.gpgsign=false"]
            done = subprocess.run(
                ["git", "-C", str(root), *identity, *arguments], capture_output=True, text=True
            )
            self.assertEqual(done.returncode, 0, done.stderr)
            return done.stdout.strip()

        with tempfile.TemporaryDirectory() as scratch:
            root = Path(scratch) / "repository"
            before = repository(root)
            git("commit", "-q", "--amend", "-m", "first, reworded")  # the same tree under a new number
            after = git("rev-parse", "HEAD")
            (root / "code.py").write_text("2\n")
            git("commit", "-q", "-am", "second")
            head = git("rev-parse", "HEAD")
            self.assertNotEqual(before, after)
            rows = [record("old", commit=before), record("new", commit=head)]
            run_dir = run_directory(scratch, *rows)
            text = (run_dir / "results.jsonl").read_text()

            done = adopt.adopt(run_dir, root / "records", root)
            self.assertEqual([row["task_id"] for row in done.records], ["old", "new"])
            self.assertEqual(dict(done.moved), {(before, after): 1})
            adopted = (root / "records" / "trial" / "results.jsonl").read_text().splitlines()
            self.assertEqual(json.loads(adopted[0])["code"]["commit"], after)
            self.assertEqual(json.loads(adopted[0]) | {"code": None}, rows[0] | {"code": None})
            self.assertEqual(adopted[1], text.splitlines()[1])  # untouched, byte for byte
            self.assertEqual((root / "records" / "trial" / "manifest.json").read_text(), "{}")
            # next to the records: the tree of each commit they name
            trees = json.loads((root / "records" / "trial" / "adopted.json").read_text())["trees"]
            self.assertEqual(trees, {c: git("rev-parse", f"{c}^{{tree}}") for c in (after, head)})
            # a commit that is nowhere in the repository cannot be placed
            run_dir = run_directory(scratch, record("lost"))
            with self.assertRaisesRegex(adopt.AdoptError, "not in this repository"):
                adopt.adopt(run_dir, root / "records", root)


class FromADatabase(helpers.SchedulerCase):
    """A batch with a dependency graph runs with the SQLite store; its records are adopted from there."""

    def test_the_records_of_a_database_are_written_out_as_the_store_holds_them(self) -> None:
        root = self.run_dir.parent / "repository"
        commit = repository(root)
        run_dir = root / "results" / "trial"
        config = helpers.fake_config(
            [{"name": "one", "value": 3}, {"name": "two", "value": 4, "predicted": 4}]
        )
        tasks, versions = expand(self.runner, config.description)
        run_id = uuid4().hex
        with SQLiteStore(run_dir / adopt.DATABASE) as store:
            scheduler = Scheduler(
                config=config, tasks=tasks, store=store, run_dir=run_dir, runner=self.runner,
                guard=PollingGuard(),
                stamp={"runner": versions, "run_id": run_id, "code": {"commit": commit, "dirty": False}},
            )  # fmt: skip
            plan = scheduler.plan()
            manifest = {"run_id": run_id, "schema_version": 1, "tasks": [p.manifest_entry() for p in plan]}
            with store.run(run_dir, manifest, {}):
                scheduler.run(plan)

        done = adopt.adopt(run_dir, root / "records", root)
        self.assertEqual(sorted(row["task_id"] for row in done.records), ["fake/one", "fake/two"])
        target = root / "records" / "trial"
        self.assertEqual(sorted(path.name for path in target.iterdir()), ["adopted.json", "results.jsonl"])
        rows = [json.loads(line) for line in (target / "results.jsonl").read_text().splitlines()]
        self.assertEqual({row["task_id"]: row["value"] for row in rows}, {"fake/one": 3, "fake/two": 4})
        for row in rows:
            self.assertNotIn("log_directory", row)  # where the run was is not part of the record
            self.assertEqual(row["task"]["id"], row["task_id"])  # the task as the runner expanded it
            self.assertEqual(row["code"], {"commit": commit, "dirty": False})


if __name__ == "__main__":
    unittest.main()
