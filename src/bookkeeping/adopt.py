"""adopt.py -- copy the records of a finished run into the directory of committed records.

`adopt` writes data/records/<batch>/results.jsonl and, next to it, adopted.json: the commit of each record
with the hash of its tree.  The records of a run with the default store are the lines of its
results.jsonl, copied unchanged, with its manifest.json.  A batch with a dependency graph runs with a
SQLite store; `make record` puts it at results/<batch>/results.sqlite, and its records are written out
as the store holds them, one line each.

It refuses records that were computed from a working tree with uncommitted changes, and records that
name this machine or a directory outside the repository: a record is committed, and it must name the
commit of the code that computed it.  One field can change on the way: if the history was rewritten
after the run (messages only, every tree as it was), a record's commit is replaced by the commit that
now has the same tree.

It is run as `src/bookkeeping/claims.py adopt RUN_DIRECTORY...`.  Nothing here knows about claims: it reads
the records of the scheduler and the history of the repository.
"""

from __future__ import annotations

import json
import shutil
import socket
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPOSITORY))

from k3batch.record import Record  # noqa: E402
from k3batch.sqlite_store import SQLiteStore  # noqa: E402
from k3batch.store import ResultStore  # noqa: E402

RESULTS = "results.jsonl"
DATABASE = "results.sqlite"
MANIFEST = "manifest.json"
# what a store adds when it hands a record out; not part of the record it keeps
HANDED_OUT = ("log_directory",)


class AdoptError(ValueError):
    """The records of a run cannot be committed as they are."""


class History:
    """The commits of a repository, as far as placing the commit of a record needs them."""

    def __init__(self, repository: Path) -> None:
        self.repository = repository
        self._placed: dict[str, str] = {}

    def _git(self, *arguments: str) -> str | None:
        done = subprocess.run(
            ["git", "-C", str(self.repository), *arguments], capture_output=True, text=True, check=False
        )
        return done.stdout.strip() if done.returncode == 0 else None

    def tree(self, commit: str) -> str | None:
        return self._git("rev-parse", f"{commit}^{{tree}}")

    def place(self, commit: str) -> str:
        """The commit of the present history that a record's commit stands for.

        A record names the commit of the code that computed it.  If the history was rewritten since (its
        messages changed, its trees not), that commit is no longer in it; the commit that now has the same
        tree is the same code under a new number.  Any other case is refused.
        """
        if commit not in self._placed:
            self._placed[commit] = self._place(commit)
        return self._placed[commit]

    def _place(self, commit: str) -> str:
        if self._git("merge-base", "--is-ancestor", commit, "HEAD") is not None:
            return commit
        tree = self.tree(commit)
        if tree is None:
            raise AdoptError(f"the commit {commit[:7]} of a record is not in this repository")
        history = [line.split() for line in (self._git("log", "--format=%H %T", "HEAD") or "").splitlines()]
        same = [number for number, its_tree in history if its_tree == tree]
        if len(same) != 1:
            raise AdoptError(
                f"the commit {commit[:7]} of a record is not in the history, and {len(same)} commits of the "
                "history have its tree: the record cannot be placed"
            )
        return same[0]


def private_words(repository: Path) -> list[str]:
    """Text that a committed record must not contain: this machine's name and directories outside the tree."""
    words = [str(Path.home()), str(repository), socket.gethostname()]
    return [word for word in words if len(word) > 3]


def stored_lines(run_dir: Path) -> list[str]:
    """The records a run left, one line each: the lines of its results.jsonl, or the rows of its database."""
    if (run_dir / RESULTS).is_file():
        return (run_dir / RESULTS).read_text(encoding="utf-8").splitlines()
    if (run_dir / DATABASE).is_file():
        rows = SQLiteStore(run_dir / DATABASE).query()
        return [
            json.dumps(
                {key: value for key, value in row.items() if key not in HANDED_OUT},
                sort_keys=True,
                ensure_ascii=False,
                allow_nan=False,
            )
            for row in rows
        ]
    return []


@dataclass(frozen=True)
class Adopted:
    """What `adopt` copied: the records now committed, and the commits it replaced, each with a count."""

    records: list[Record]
    moved: Counter[tuple[str, str]]


def adopt(run_dir: Path, records: Path, repository: Path) -> Adopted:
    """Copies the records of `run_dir` to the directory of its name under `records`."""
    text = "\n".join(stored_lines(run_dir))
    found = [json.loads(line) for line in text.splitlines() if line.strip().startswith("{")]
    if not found:
        raise AdoptError(f"no records in {run_dir}")
    dirty = [r.get("task_id") for r in found if (r.get("code") or {}).get("dirty") is not False]
    if dirty:
        raise AdoptError(
            f"{run_dir}: {len(dirty)} records, among them {dirty[0]}, were computed from a working tree with "
            "uncommitted changes or outside a checkout; commit the code and run the batch again"
        )
    manifest = run_dir / MANIFEST
    committed = text + (manifest.read_text(encoding="utf-8") if manifest.is_file() else "")
    for word in private_words(repository):
        if word.lower() in committed.lower():
            raise AdoptError(
                f"{run_dir}: a record names this machine or a directory outside the repository; "
                "records are committed, so it is not adopted"
            )
    # every line is copied as it is, unless its commit was renumbered by a rewrite of the history:
    # then that one field changes, and nothing else
    history = History(repository)
    moved: Counter[tuple[str, str]] = Counter()
    trees: dict[str, str] = {}
    lines = []
    for line in text.splitlines():
        try:
            record = json.loads(line)
            commit = record["code"]["commit"]
        except (json.JSONDecodeError, KeyError, TypeError):
            lines.append(line)
            continue
        now = history.place(commit)
        if now != commit:
            record["code"]["commit"] = now
            moved[commit, now] += 1
            line = json.dumps(record, sort_keys=True, ensure_ascii=False, allow_nan=False)
        if now not in trees:
            trees[now] = history.tree(now) or "unknown"
        lines.append(line)
    target = records / run_dir.name
    target.mkdir(parents=True, exist_ok=True)
    (target / RESULTS).write_text("\n".join(lines) + "\n", encoding="utf-8")
    if manifest.is_file():
        shutil.copyfile(manifest, target / MANIFEST)
    sidecar = {"trees": dict(sorted(trees.items()))}
    (target / "adopted.json").write_text(json.dumps(sidecar, indent=1) + "\n", encoding="utf-8")
    return Adopted(list(ResultStore(target / RESULTS).latest().values()), moved)
