"""The Macaulay2 end of a batch: the script Macaulay2 runs (task-runner.m2), the request and
reply files it exchanges with it, and the version of the code that ran.

In: a batch description or one task. Out: the expanded Tasks, or the result of one task. Only
task-runner.m2 loads the package in src/macaulay2; the Python side knows the protocol, not the
mathematics.
"""

from .runner import (
    DEFAULT_RUNNER,
    REPOSITORY,
    RUNNER_SCRIPT,
    RunnerError,
    RunnerInvocation,
    bundled_script,
    code_version,
    error_lines,
    expand,
    parse_result,
    run_command,
)
from .wire import FileRequest, WireError, check_result, check_task, unique_object

__all__ = [
    "DEFAULT_RUNNER",
    "REPOSITORY",
    "RUNNER_SCRIPT",
    "FileRequest",
    "RunnerError",
    "RunnerInvocation",
    "WireError",
    "bundled_script",
    "check_result",
    "check_task",
    "code_version",
    "error_lines",
    "expand",
    "parse_result",
    "run_command",
    "unique_object",
]
