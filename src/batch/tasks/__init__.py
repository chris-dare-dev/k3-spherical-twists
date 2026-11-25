"""What a batch asks for: the batch file, the tasks the runner expands it into, and the limits
each task runs under.

In: a batch file (data/batches/*.toml). Out: a BatchConfig, Tasks, Limits, and the statuses an attempt
can end with. It imports no other box: everything else in the scheduler is written in its terms.
"""

from .config import BatchConfig, ConfigError, Tier, load_config, parse_config
from .model import (
    COMPLETED_STATUSES,
    FAILED_STATUSES,
    RUNNER_STATUSES,
    TASK_LABELS,
    Limits,
    RunDeadlineExpired,
    Status,
    Task,
    TaskError,
)
from .resources import HISTORY_WINDOW, MIB, ResourcePolicy, estimate, grow_limits, resource_context

__all__ = [
    "COMPLETED_STATUSES",
    "FAILED_STATUSES",
    "HISTORY_WINDOW",
    "MIB",
    "RUNNER_STATUSES",
    "TASK_LABELS",
    "BatchConfig",
    "ConfigError",
    "Limits",
    "ResourcePolicy",
    "RunDeadlineExpired",
    "Status",
    "Task",
    "TaskError",
    "Tier",
    "estimate",
    "grow_limits",
    "load_config",
    "parse_config",
    "resource_context",
]
