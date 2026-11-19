"""Command line: plan a batch, run it, report on its results."""

from __future__ import annotations

import argparse
import json
import os
import shlex
import socket
import sqlite3
import sys
from collections import Counter
from collections.abc import Iterable, Sequence
from dataclasses import asdict, replace
from datetime import UTC, datetime
from pathlib import Path
from typing import Any
from uuid import uuid4

from . import __version__, report
from .artifacts import ArtifactStore, read_artifact_json
from .bundle import export_run, verify_run
from .config import BatchConfig, ConfigError, load_config
from .execution import LocalBackend, RunDeadlineExpired
from .identity import RECORD_SCHEMA
from .memory import MemoryGuard, available_mb, choose_guard
from .model import COMPLETED_STATUSES, FAILED_STATUSES, Limits, Status, Task
from .planning import PlannedTask
from .record import Record
from .resources import ResourcePolicy
from .runner import DEFAULT_RUNNER, REPOSITORY, RunnerError
from .scheduler import Scheduler
from .source import source_snapshot
from .sqlite_store import SQLiteStore
from .store import ResultStore, RunHistory, StoreLocked

EXIT_OK = 0
EXIT_FAILED = 1  # a mismatch, an error or a crash
EXIT_USAGE = 2
EXIT_LIMITS = 3  # nothing failed, but some tasks were stopped at a limit
EXIT_INTERRUPTED = 130


def _parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="k3batch", description="Run batches of Macaulay2 tasks under time and memory limits."
    )
    parser.add_argument("--version", action="version", version=f"k3batch {__version__}")
    commands = parser.add_subparsers(dest="command", required=True)

    def database_argument(command: argparse.ArgumentParser) -> None:
        command.add_argument("--store", type=Path, metavar="DATABASE", help="use a SQLite results database")

    def batch_arguments(command: argparse.ArgumentParser) -> None:
        database_argument(command)
        command.add_argument(
            "--resource-retries", type=int, metavar="N", help="override automatic retry count"
        )
        command.add_argument("batch", type=Path, help="the batch file (TOML)")
        command.add_argument("--out", type=Path, help="run directory (default: results/<name of the batch>)")
        command.add_argument("--workers", type=int, help="task processes at a time")
        command.add_argument(
            "--memory-budget", type=int, metavar="MB", help="sum of the memory limits allowed at a time"
        )
        command.add_argument(
            "--run-time-limit", type=float, metavar="S", help="wall limit for planning and tasks"
        )
        command.add_argument("--cpu-budget", type=int, metavar="CORES", help="run-wide CPU budget")
        command.add_argument("--scratch-root", type=Path, help="directory on a size-limited tmpfs")
        command.add_argument(
            "--scratch-budget", type=int, metavar="MB", help="maximum size of the scratch mount"
        )
        command.add_argument("--time-limit", type=float, metavar="S", help="default time limit of a task")
        command.add_argument("--memory-limit", type=int, metavar="MB", help="default memory limit of a task")
        command.add_argument(
            "--retry", default="", metavar="STATUS[,STATUS]",
            help="compute again the tasks whose latest record has one of these statuses",
        )  # fmt: skip
        command.add_argument(
            "--runner", help="command that expands batches and runs tasks (default: the Macaulay2 runner)"
        )

        command.add_argument(
            "--memory-guard",
            choices=["auto", "cgroup", "poll"],
            default="auto",
            help="resource control mode (default: enforced cgroups when available, otherwise sampled)",
        )

    plan = commands.add_parser("plan", help="list what a run would compute, without computing")
    batch_arguments(plan)

    run = commands.add_parser("run", help="compute the tasks of a batch that lack reusable results")
    batch_arguments(run)
    run.add_argument(
        "--overcommit", action="store_true",
        help="run even if the memory budget is above the memory now available",
    )  # fmt: skip
    run.add_argument(
        "--checkpoint-after", metavar="TASK_ID", help="pause after committing a newly successful task"
    )
    run.add_argument("--quiet", action="store_true", help="do not print a line per task")

    rep = commands.add_parser("report", help="print tables from the records of a run directory")
    rep.add_argument("run_dir", type=Path)
    database_argument(rep)
    report_selection = rep.add_mutually_exclusive_group()
    report_selection.add_argument("--run", metavar="ID", help="select a run by ID (default: latest)")
    report_selection.add_argument("--legacy", action="store_true", help="report unversioned results")
    rep.add_argument(
        "--full", action="store_true", help="list every computed value against its predicted value"
    )
    importer = commands.add_parser("import-jsonl", help="import a JSONL result directory into SQLite")
    importer.add_argument("run_dir", type=Path)
    importer.add_argument("--store", type=Path, required=True, metavar="DATABASE")
    export = commands.add_parser("export-jsonl", help="write SQLite result records to stdout as JSONL")
    export.add_argument("--store", type=Path, required=True, metavar="DATABASE")
    export.add_argument("--run", metavar="ID", help="export the records and checks pinned by a run")
    export.add_argument("--surface", metavar="JSON", help="match a complete task surface object")
    export.add_argument("--method", help="match the recorded computation method")
    export.add_argument("--observation", metavar="ID", help="match a result record ID")
    export.add_argument("--commit", help="match the recorded code commit")
    bundle = commands.add_parser("export-run", help="export a pinned run and its mathematical artifacts")
    bundle.add_argument("run_dir", type=Path)
    bundle.add_argument("destination", type=Path)
    bundle.add_argument("--store", type=Path, required=True, metavar="DATABASE")
    bundle.add_argument("--run", metavar="ID", help="select a run by ID (default: latest)")
    verify = commands.add_parser("verify-run", help="verify an exported run offline and print its report")
    verify.add_argument("directory", type=Path)
    verify.add_argument(
        "--full", action="store_true", help="list every computed value against its predicted value"
    )
    publish = commands.add_parser("publish-artifact", help="register an immutable mathematical artifact")
    publish.add_argument("directory", type=Path)
    publish.add_argument("file", type=Path)
    publish.add_argument("--producer", required=True, help="run or attempt ID")
    artifact = commands.add_parser("read-artifact", help="verify and write a registered artifact as JSON")
    artifact.add_argument("directory", type=Path)
    artifact.add_argument("digest")
    return parser


def _prepare(arguments: argparse.Namespace) -> tuple[BatchConfig, tuple[str, ...], Path, frozenset[str]]:
    config = load_config(arguments.batch).with_overrides(
        workers=arguments.workers,
        memory_budget_mb=arguments.memory_budget,
        time_seconds=arguments.time_limit,
        memory_mb=arguments.memory_limit,
        cpu_budget_cores=arguments.cpu_budget,
        run_time_seconds=arguments.run_time_limit,
        scratch_root=arguments.scratch_root,
        scratch_budget_mb=arguments.scratch_budget,
    )
    if arguments.resource_retries is not None:
        settings = asdict(config.resources or ResourcePolicy()) | {
            "retry_attempts": arguments.resource_retries
        }
        config = replace(config, resources=ResourcePolicy.parse(settings))
    if config.graph is not None and arguments.store is None:
        raise ConfigError("a dependency graph requires --store DATABASE")
    runner = tuple(shlex.split(arguments.runner)) if arguments.runner else DEFAULT_RUNNER
    run_dir = arguments.out or REPOSITORY / "results" / config.name
    retry = frozenset(name for name in arguments.retry.split(",") if name)
    unknown = retry - {str(status) for status in Status}
    if unknown:
        raise ConfigError(f"--retry: unknown status {sorted(unknown)[0]!r}")
    return config, runner, run_dir, retry


def _plan_lines(
    config: BatchConfig, plan: Sequence[PlannedTask], pending: Sequence[tuple[Task, Limits]]
) -> list[str]:
    recorded = len(plan) - len(pending)
    lines = [
        f"batch {config.name}: {len(plan)} tasks, {len(pending)} to compute, {recorded} already recorded",
        f"workers {config.workers}, memory budget {config.memory_budget_mb} MB",
    ]
    classes: Counter[tuple[float, int]] = Counter(
        (limits.time_seconds, limits.memory_mb) for _, limits in pending
    )
    for (time_seconds, memory_mb), count in sorted(classes.items()):
        alone = " (one at a time)" if 2 * memory_mb > config.memory_budget_mb else ""
        lines.append(f"  {count:5d} tasks with limits {time_seconds:g} s, {memory_mb} MB{alone}")
    return lines


def _command_plan(arguments: argparse.Namespace) -> int:
    config, runner, run_dir, retry = _prepare(arguments)
    guard = choose_guard(arguments.memory_guard)
    with (
        source_snapshot(runner, REPOSITORY) as source,
        LocalBackend(guard, config.memory_budget_mb, config.workers) as backend,
    ):
        tasks, runner_versions = source.expand(config.description, backend)
        scheduler = Scheduler(
            config=config, tasks=tasks, store=_result_store(run_dir, arguments.store),
            run_dir=run_dir, runner=runner, guard=guard, retry=retry, source=source,
            stamp={"runner": runner_versions},
        )  # fmt: skip
        plan = scheduler.plan()
        pending = scheduler.pending(plan)
    print("\n".join(_plan_lines(config, plan, pending)))
    estimates = {entry.task.id: entry.resources for entry in plan}
    for task, limits in pending:
        request = f"{task.cost:8g}  {limits.time_seconds:8g} s  {limits.memory_mb:7d} MB"
        estimate = estimates[task.id]
        note = f"  {limits.cpu_cores} cores" if limits.cpu_cores is not None else ""
        if estimate:
            note += f"  {estimate['basis']}"
        print(f"{request}  {task.id}{note}")
    return EXIT_OK


def _local_backend(config: BatchConfig, guard: MemoryGuard) -> LocalBackend:
    return LocalBackend(
        guard, config.memory_budget_mb, config.run_cores, workers=config.workers,
        run_time_seconds=config.run_time_seconds, scratch_root=config.scratch_root,
        scratch_budget_mb=config.scratch_budget_mb,
    )  # fmt: skip


def exit_status(statuses: Iterable[str]) -> int:
    """The status a run ends with, from how the task of each member of the run ended.

    A mismatch, an error, a crash or a blocked task makes the run fail, whatever else happened. A run
    in which nothing failed but a task was stopped at a limit says so. Tasks without a method count
    as carried out.
    """
    ended = set(statuses)
    if ended & FAILED_STATUSES:
        return EXIT_FAILED
    if ended - COMPLETED_STATUSES:
        return EXIT_LIMITS
    return EXIT_OK


def _check_memory(config: BatchConfig, backend: LocalBackend, free: int | None, overcommit: bool) -> None:
    requested = config.memory_budget_mb + backend.coordinator_headroom_mb
    if free is not None and requested > free and not overcommit:
        raise ConfigError(
            f"the memory budget and coordinator headroom use {requested} MB but only {free} MB is available; "
            "lower --memory-budget, or pass --overcommit to run anyway"
        )


def _manifest(run_id: str, config: BatchConfig, plan: Sequence[PlannedTask]) -> dict[str, Any]:
    """The members of a run: what a report of this run will select, whatever is computed later."""
    return {
        "schema_version": RECORD_SCHEMA,
        "run_id": run_id,
        "batch": config.name,
        "tasks": [entry.manifest_entry() for entry in plan],
    }


def _command_run(arguments: argparse.Namespace) -> int:
    config, runner, run_dir, retry = _prepare(arguments)
    free = available_mb()
    guard = choose_guard(arguments.memory_guard)
    backend = _local_backend(config, guard)
    _check_memory(config, backend, free, arguments.overcommit)
    started_at = datetime.now(UTC)
    run_id = uuid4().hex
    store = _result_store(run_dir, arguments.store)
    with source_snapshot(runner, REPOSITORY) as source, store, backend:
        code = source.code
        tasks, runner_versions = source.expand(config.description, backend)
        checkpoint = arguments.checkpoint_after
        if checkpoint and not any(task.id == checkpoint for task in tasks):
            raise ConfigError(f"unknown checkpoint task {checkpoint!r}")

        def progress(record: Record, finished: int, total: int) -> None:
            if not arguments.quiet:
                _print_progress(record, finished, total)
            if record["task_id"] == checkpoint and record["status"] == Status.OK:
                print(f"checkpoint committed at {checkpoint}", file=sys.stderr)
                raise KeyboardInterrupt

        scheduler = Scheduler(
            config=config, tasks=tasks, store=store, run_dir=run_dir, runner=runner, guard=guard,
            backend=backend, source=source,
            stamp={"run_id": run_id, "runner": runner_versions, "code": code},
            retry=retry, progress=progress,
        )  # fmt: skip
        plan = scheduler.plan()
        pending = scheduler.pending(plan)
        manifest = _manifest(run_id, config, plan)
        metadata = {
            "run_id": run_id,
            "started_at": started_at.isoformat(timespec="seconds"),
            "command": sys.argv,
            "batch_file": str(arguments.batch),
            "config": config.as_dict(),
            "retry": sorted(retry),
            "runner_command": list(runner),
            "runner": runner_versions,
            "code": code,
            "memory_guard": guard.name,
            "resource_controls": backend.controls(),
            "memory_available_mb": free,
            "host": socket.gethostname(),
            "cpus": os.cpu_count(),
            "tasks": len(tasks),
            "pending": len(pending),
        }
        print("\n".join(_plan_lines(config, plan, pending)), file=sys.stderr)
        print(f"run {run_id}, memory guard: {guard.name}, results in {store.location}", file=sys.stderr)
        try:
            with store.run(run_dir, manifest, metadata):
                outcome = scheduler.run(plan)
                selected = report.selected_results(store, manifest)
                if len(selected) != len(plan):
                    raise RuntimeError(
                        f"missing results for {len(plan) - len(selected)} tasks in run {run_id}"
                    )
        except KeyboardInterrupt:
            print("interrupted: tasks in flight were stopped", file=sys.stderr)
            return EXIT_INTERRUPTED

    summary = ", ".join(f"{count} {status}" for status, count in sorted(outcome.items())) or "nothing to do"
    print(f"this run: {summary}", file=sys.stderr)
    return exit_status(record["status"] for record in selected.values())


def _result_store(run_dir: Path, database: Path | None) -> RunHistory:
    if database is None:
        return ResultStore(run_dir / "results.jsonl")
    return SQLiteStore(database)


def _print_progress(record: Record, done: int, total: int) -> None:
    note = ""
    if record["status"] == Status.MISMATCH:
        note = f"  computed {report.cell(record['value'])}, predicted {report.cell(record['predicted'])}"
    elif record["error"]:
        note = "  " + record["error"].splitlines()[-1]
    print(
        f"[{done}/{total}] {record['status']:<11} {record['wall_seconds']:8.1f} s "
        f"{record['peak_rss_mb']:7.0f} MB  {record['task_id']}{note}",
        file=sys.stderr, flush=True,
    )  # fmt: skip


def _command_report(arguments: argparse.Namespace) -> int:
    store = _result_store(arguments.run_dir, arguments.store)
    if not store.path.exists():
        raise ConfigError(f"no results at {store.path}")
    sys.stdout.write(
        report.render(
            arguments.run_dir, full=arguments.full, run_id=arguments.run, legacy=arguments.legacy, store=store
        )
    )
    return EXIT_OK


def _command_import(arguments: argparse.Namespace) -> int:
    if not (arguments.run_dir / "results.jsonl").is_file():
        raise ConfigError(f"no results.jsonl in {arguments.run_dir}")
    directory = arguments.run_dir.resolve()
    database = arguments.store.resolve()
    source_files = [directory / name for name in ("results.jsonl", "runs.jsonl", "manifest.json")]
    source_files.extend((directory / "runs").glob("*.json"))
    if any(source.resolve() == database for source in source_files):
        raise ConfigError("the SQLite database must have a different path from the source results")
    with SQLiteStore(database) as store:
        count = store.import_jsonl(arguments.run_dir)
    print(f"imported {count} result records")
    return EXIT_OK


def _command_export(arguments: argparse.Namespace) -> int:
    surface = json.loads(arguments.surface) if arguments.surface is not None else None
    if arguments.surface is not None and not isinstance(surface, dict):
        raise ConfigError("--surface requires a JSON object")
    for row in SQLiteStore(arguments.store).query(
        run_id=arguments.run,
        surface=surface,
        method=arguments.method,
        observation=arguments.observation,
        commit=arguments.commit,
    ):
        print(json.dumps(row, ensure_ascii=False, allow_nan=False))
    return EXIT_OK


def _command_export_run(arguments: argparse.Namespace) -> int:
    export_run(SQLiteStore(arguments.store), arguments.run_dir, arguments.destination, run_id=arguments.run)
    return EXIT_OK


def _command_verify_run(arguments: argparse.Namespace) -> int:
    sys.stdout.write(verify_run(arguments.directory, full=arguments.full))
    return EXIT_OK


def _command_publish_artifact(arguments: argparse.Namespace) -> int:
    store = ArtifactStore(arguments.directory)
    print(store.publish(read_artifact_json(arguments.file.read_bytes()), producer=arguments.producer))
    return EXIT_OK


def _command_read_artifact(arguments: argparse.Namespace) -> int:
    sys.stdout.buffer.write(ArtifactStore(arguments.directory).read(arguments.digest))
    return EXIT_OK


def main(argv: Sequence[str] | None = None) -> int:
    arguments = _parser().parse_args(argv)
    commands = {
        "plan": _command_plan,
        "run": _command_run,
        "report": _command_report,
        "import-jsonl": _command_import,
        "export-jsonl": _command_export,
        "export-run": _command_export_run,
        "verify-run": _command_verify_run,
        "publish-artifact": _command_publish_artifact,
        "read-artifact": _command_read_artifact,
    }
    try:
        return commands[arguments.command](arguments)
    except RunDeadlineExpired as problem:
        print(f"k3batch: {problem}", file=sys.stderr)
        return EXIT_LIMITS
    except (
        ConfigError,
        RunnerError,
        StoreLocked,
        RuntimeError,
        OSError,
        sqlite3.Error,
        ValueError,
    ) as problem:
        print(f"k3batch: {problem}", file=sys.stderr)
        return EXIT_USAGE
