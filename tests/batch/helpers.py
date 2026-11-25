"""Shared pieces of the scheduler tests: a batch of fake tasks and a way to run it."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from collections import Counter
from pathlib import Path
from typing import Any

from batch.jobs import MemoryGuard, PollingGuard
from batch.records import Record, ResultStore, build
from batch.runner import expand
from batch.scheduler import Scheduler
from batch.tasks import BatchConfig, Limits, Status, Task, parse_config

FAKE_RUNNER = Path(__file__).with_name("fake_runner.py")
# what the fake runner says of itself, in marker lines and through the file protocol
MARKER_VERSIONS = {"fake_version": "1"}
FILE_VERSIONS = MARKER_VERSIONS | {"m2_version": "none", "package": "fake 1", "protocol_version": 2}


def fake_runner(
    journal: Path | None = None, *, markers: bool = False, script: Path = FAKE_RUNNER
) -> tuple[str, ...]:
    """The fake runner's command: the file protocol of the bundled runner, or the legacy marker lines."""
    command = (sys.executable, str(script), *(("--journal", str(journal)) if journal else ()))
    return command if markers else (*command, "protocol-v2")


def fake_config(
    *task_sets: list[dict[str, Any]] | dict[str, Any],
    workers: int = 4,
    memory_budget_mb: int = 800,
    time_seconds: float = 20,
    memory_mb: int = 100,
    tiers: list[dict[str, Any]] | None = None,
) -> BatchConfig:
    """A batch whose task sets are lists of fake-runner items, or tables with "items" and "limits"."""
    sets = [{"kind": "fake", "items": s} if isinstance(s, list) else {"kind": "fake"} | s for s in task_sets]
    return parse_config(
        {
            "name": "fake",
            "scheduler": {"workers": workers, "memory_budget_mb": memory_budget_mb},
            "limits": {"time_seconds": time_seconds, "memory_mb": memory_mb, "tier": tiers or []},
            "tasks": sets,
        }
    )


def record(payload: dict[str, Any], status: str = "ok", **fields: Any) -> Record:
    """The record the scheduler builds for an attempt of the task `payload`, for tests that read records.

    `value`, `predicted` and `agrees` are what the runner reported; `code` is the stamp of the run; any
    other field is an argument of `batch.records.build`.
    """
    result = {key: fields.pop(key) for key in ("value", "predicted", "agrees") if key in fields}
    stamp = {"run_id": "run", "runner": {}, "code": fields.pop("code", {"commit": "0" * 40, "dirty": False})}
    arguments: dict[str, Any] = {
        "status": Status(status),
        "result": result,
        "error": None,
        "attempt_id": "attempt",
        "started_at": "2026-01-01T00:00:00+00:00",
        "log": None,
        "exit_code": 0,
        "wall_seconds": 1.0,
        "measured": {},
        "resource_controls": {},
        "memory_guard": "poll",
        "stamp": stamp,
        "computation_id": "computation",
        "check_id": "check",
        "record_id": "record",
    }
    return build(Task.from_payload(payload), Limits(60, 500), **(arguments | fields))


class Journal:
    """What the fake runner wrote down: which tasks ran, in which order, and when."""

    def __init__(self, path: Path) -> None:
        self.path = path

    def lines(self) -> list[tuple[str, int, float, str]]:
        if not self.path.exists():
            return []
        rows = [line.split(" ", 3) for line in self.path.read_text().splitlines()]
        return [(word, int(pid), float(when), task_id) for word, pid, when, task_id in rows]

    def started(self) -> list[str]:
        return [task_id for word, _, _, task_id in self.lines() if word == "start"]

    def pids(self) -> list[int]:
        return [pid for word, pid, _, _ in self.lines() if word == "start"]

    def intervals(self) -> dict[str, tuple[float, float]]:
        starts = {task_id: when for word, _, when, task_id in self.lines() if word == "start"}
        ends = {task_id: when for word, _, when, task_id in self.lines() if word == "end"}
        return {task_id: (starts[task_id], ends[task_id]) for task_id in ends}


class SchedulerCase(unittest.TestCase):
    """A test case with a run directory, a journal and a fake runner."""

    guard_class: type[MemoryGuard] = PollingGuard
    markers = False  # the file protocol, as the bundled runner speaks it

    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.run_dir = Path(scratch.name) / "run"
        self.journal = Journal(Path(scratch.name) / "journal")
        self.runner = fake_runner(self.journal.path, markers=self.markers)

    def run_batch(self, config: BatchConfig, **options: Any) -> Counter[str]:
        tasks, versions = expand(self.runner, config.description)
        with ResultStore(self.run_dir / "results.jsonl") as store:
            scheduler = Scheduler(
                config=config,
                tasks=tasks,
                store=store,
                run_dir=self.run_dir,
                runner=self.runner,
                guard=self.guard_class(),
                stamp={"run_id": "test", "runner": versions, "code": {"commit": "0" * 40, "dirty": False}},
                **options,
            )
            return scheduler.run()

    def latest(self) -> dict[str, dict[str, Any]]:
        return ResultStore(self.run_dir / "results.jsonl").latest()

    def statuses(self) -> dict[str, str]:
        return {task_id.removeprefix("fake/"): record["status"] for task_id, record in self.latest().items()}


def still_runs(pid: int) -> bool:
    """Whether a process is running.  A killed process stays listed as a zombie until its parent
    collects it, which the first process of a container may never do; a zombie does not run."""
    try:
        stat = Path(f"/proc/{pid}/stat").read_text()
    except OSError:
        return False
    return stat.rpartition(")")[2].split()[0] != "Z"


MODEL = {
    "version": 1,
    "kind": "k3-model",
    "payload": {"parameters": {}, "coordinates": [], "grading": [], "equations": [], "markings": {}},
}


def body(data: dict) -> bytes:
    return (json.dumps(data, sort_keys=True, separators=(",", ":")) + "\n").encode()
