"""Invoke the bundled file protocol or a legacy command-line runner."""

from __future__ import annotations

import json
import subprocess
import tempfile
from collections.abc import Callable
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from ..tasks import Task
from . import wire

# this file is src/batch/runner/runner.py; the script beside it is what Macaulay2 runs
REPOSITORY = Path(__file__).resolve().parents[3]
RUNNER_SCRIPT = Path(__file__).resolve().with_name("task-runner.m2").relative_to(REPOSITORY)
DEFAULT_RUNNER = ("M2", "--script", str(REPOSITORY / RUNNER_SCRIPT))

TASK_MARK = "@task "
META_MARK = "@meta "
RESULT_MARK = "@result "


class RunnerError(RuntimeError):
    """The runner failed or did not follow the protocol."""


@dataclass(frozen=True)
class RunnerInvocation:
    command: list[str]
    request: wire.FileRequest | None

    @classmethod
    def prepare(
        cls,
        runner: tuple[str, ...],
        operation: str,
        payload: dict[str, Any],
        directory: Path,
        *,
        repository: Path = REPOSITORY,
    ) -> RunnerInvocation:
        command = _file_protocol_command(runner, repository)
        if command is None:
            return cls([*runner, operation, json.dumps(payload)], None)
        try:
            request = wire.FileRequest.create(directory, operation, payload)
        except (ValueError, TypeError) as problem:
            raise RunnerError(f"cannot encode request JSON: {problem}") from problem
        return cls([*command, *request.args], request)

    def cleanup(self) -> None:
        if self.request is not None:
            self.request.cleanup()

    def task_result(self, output: str, exit_code: int) -> dict[str, Any] | None:
        if self.request is None:
            return parse_result(output) if exit_code == 0 else None
        try:
            payload = self.request.read(exit_code)
            return wire.check_result(payload) if payload is not None else None
        except (wire.WireError, OSError) as problem:
            raise RunnerError(str(problem)) from problem


def bundled_script(runner: tuple[str, ...], repository: Path) -> Path | None:
    """The bundled Macaulay2 runner as `repository` has it, if `runner` is that script."""
    if runner[-2:-1] == ("--script",):
        script = (repository / runner[-1]).resolve()
        if script == (repository / RUNNER_SCRIPT).resolve():
            return script
    return None


def _file_protocol_command(runner: tuple[str, ...], repository: Path) -> list[str] | None:
    """The command of a runner that takes request and response files, without its last three arguments.

    The bundled Macaulay2 runner does, and so does any runner whose command ends in `protocol-v2`.
    """
    if runner[-1:] == (wire.MODE,):
        return list(runner[:-1])
    script = bundled_script(runner, repository)
    if script is not None:
        return [*runner[:-1], str(script)]
    return None


def error_lines(output: str, limit: int = 5) -> str:
    """The lines of a runner's output that say what went wrong, without Macaulay2's backtrace."""
    lines = [line.strip() for line in output.splitlines()]
    lines = [line for line in lines if line and "--back trace--" not in line and not line.startswith("@")]
    errors = [line for line in lines if "error" in line.lower()]
    return "\n".join((errors or lines)[-limit:])


def expand(
    runner: tuple[str, ...],
    description: dict[str, Any],
    *,
    timeout: float = 600,
    repository: Path = REPOSITORY,
    scratch_root: Path | None = None,
    execute: Callable[[list[str], float], subprocess.CompletedProcess[str]] | None = None,
) -> tuple[list[Task], dict[str, Any]]:
    """Asks the runner for the tasks of a batch description and for its versions."""
    with tempfile.TemporaryDirectory(prefix="batch-", dir=scratch_root) as scratch:
        invocation = RunnerInvocation.prepare(
            runner, "expand", description, Path(scratch), repository=repository
        )
        try:
            return _expand(invocation, timeout, execute)
        finally:
            invocation.cleanup()


def _expand(
    invocation: RunnerInvocation,
    timeout: float,
    execute: Callable[[list[str], float], subprocess.CompletedProcess[str]] | None,
) -> tuple[list[Task], dict[str, Any]]:
    try:
        if execute is None:
            done = subprocess.run(
                invocation.command,
                capture_output=True,
                text=True,
                timeout=timeout,
                stdin=subprocess.DEVNULL,
                check=False,
            )
        else:
            done = execute(invocation.command, timeout)
    except FileNotFoundError:
        raise RunnerError(f"cannot start the runner: {invocation.command[0]} not found") from None
    except subprocess.TimeoutExpired:
        raise RunnerError(f"the runner did not expand the batch within {timeout:g} s") from None
    if invocation.request is not None:
        try:
            payload = invocation.request.read(done.returncode)
            if payload is not None:
                decoded_tasks, versions = wire.check_expansion(payload)
                _check_unique_tasks(decoded_tasks)
                return decoded_tasks, versions
        except (ValueError, OSError, OverflowError) as problem:
            diagnostics = error_lines(done.stderr + done.stdout)
            message = f"invalid expansion response: {problem}"
            raise RunnerError(f"{message}\n{diagnostics}" if diagnostics else message) from problem
    if done.returncode != 0:
        raise RunnerError(
            f"the runner could not expand the batch (status {done.returncode}):\n"
            + error_lines(done.stderr + done.stdout)
        )
    tasks: list[Task] = []
    meta: dict[str, Any] | None = None
    for line in done.stdout.splitlines():
        try:
            if line.startswith(TASK_MARK):
                tasks.append(Task.from_payload(json.loads(line[len(TASK_MARK) :])))
            elif line.startswith(META_MARK):
                meta = json.loads(line[len(META_MARK) :])
        except (json.JSONDecodeError, ValueError) as problem:
            raise RunnerError(f"the runner printed a line that cannot be read: {problem}") from None
    if meta is None or meta.get("tasks") != len(tasks):
        raise RunnerError("the runner's list of tasks is incomplete")
    _check_unique_tasks(tasks)
    meta.pop("tasks")
    return tasks, meta


def _check_unique_tasks(tasks: list[Task]) -> None:
    if len({task.id for task in tasks}) != len(tasks):
        raise RunnerError("the runner produced two tasks with the same id")


def run_command(runner: tuple[str, ...], task: Task) -> list[str]:
    """The command that computes one task."""
    return [*runner, "run", json.dumps(task.payload)]


def parse_result(output: str) -> dict[str, Any] | None:
    """The result a task printed, or None if it printed none that can be read."""
    for line in reversed(output.splitlines()):
        if line.startswith(RESULT_MARK):
            try:
                result = json.loads(line[len(RESULT_MARK) :])
            except json.JSONDecodeError:
                return None
            return result if isinstance(result, dict) else None
    return None


def code_version(repository: Path = REPOSITORY) -> dict[str, Any]:
    """The git commit of the code and whether the working tree differs from it."""

    def git(*arguments: str) -> str | None:
        try:
            done = subprocess.run(
                ["git", "-C", str(repository), *arguments],
                capture_output=True, text=True, timeout=30, check=False,
            )  # fmt: skip
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return None
        return done.stdout.strip() if done.returncode == 0 else None

    commit = git("rev-parse", "HEAD")
    changes = git("status", "--porcelain")
    return {"commit": commit, "dirty": None if commit is None or changes is None else bool(changes)}
