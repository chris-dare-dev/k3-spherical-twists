"""One command on Linux under a time and memory limit, watched by a separate process.

In: a command, its Limits and a log path. Out: a JobResult (exit, signal, time, peak memory, whether a
limit stopped it). It knows nothing of tasks' meaning, Macaulay2 or records; watchdog.py runs as its
own process and imports nothing from the package.
"""

from .execution import WATCHDOG, JobResult, LocalBackend, LocalJob, read_output
from .memory import CgroupGuard, MemoryGuard, PollingGuard, available_mb, choose_guard
from .scratch import tmpfs_capacity

__all__ = [
    "WATCHDOG",
    "CgroupGuard",
    "JobResult",
    "LocalBackend",
    "LocalJob",
    "MemoryGuard",
    "PollingGuard",
    "available_mb",
    "choose_guard",
    "read_output",
    "tmpfs_capacity",
]
