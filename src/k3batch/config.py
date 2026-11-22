"""The batch file: what to compute, with which limits, on how much of the machine."""

from __future__ import annotations

import math
import tomllib
from dataclasses import asdict, dataclass, replace
from pathlib import Path
from typing import Any

from .model import Limits, Task
from .resources import ResourcePolicy


class ConfigError(ValueError):
    """The batch file or the command line asks for something that cannot be run."""


@dataclass(frozen=True)
class Tier:
    """Limits for tasks whose cost is at least `min_cost`; a missing limit is inherited."""

    min_cost: float
    time_seconds: float | None = None
    memory_mb: int | None = None
    cpu_cores: int | None = None


@dataclass(frozen=True)
class BatchConfig:
    name: str
    workers: int
    memory_budget_mb: int
    default_limits: Limits
    tiers: tuple[Tier, ...]
    # one entry per [[tasks]] table: the limits written in that table, if any
    set_limits: tuple[dict[str, Any], ...]
    # what the runner expands: {"surfaces": [...], "tasks": [...]}
    description: dict[str, Any]
    graph: dict[str, Any] | None = None
    resources: ResourcePolicy | None = None
    cpu_budget_cores: int | None = None
    run_time_seconds: float | None = None
    scratch_root: Path | None = None
    scratch_budget_mb: int | None = None

    @property
    def run_cores(self) -> int:
        return self.cpu_budget_cores if self.cpu_budget_cores is not None else self.workers

    @property
    def weighted_cpu(self) -> bool:
        return (
            self.cpu_budget_cores is not None
            or self.default_limits.cpu_cores is not None
            or any(tier.cpu_cores is not None for tier in self.tiers)
            or any("cpu_cores" in limits for limits in self.set_limits)
        )

    def limits_for(self, task: Task) -> Limits:
        """Limits of a task: its set's own, else those of the highest tier it reaches, else the defaults."""
        time_seconds: float = self.default_limits.time_seconds
        memory_mb: int = self.default_limits.memory_mb
        cpu_cores = self.default_limits.cpu_cores
        for tier in sorted(self.tiers, key=lambda t: t.min_cost):
            if task.cost >= tier.min_cost:
                if tier.time_seconds is not None:
                    time_seconds = tier.time_seconds
                if tier.memory_mb is not None:
                    memory_mb = tier.memory_mb
                if tier.cpu_cores is not None:
                    cpu_cores = tier.cpu_cores
        own = self.set_limits[task.set] if task.set < len(self.set_limits) else {}
        return Limits(
            time_seconds=own.get("time_seconds", time_seconds),
            memory_mb=own.get("memory_mb", memory_mb),
            cpu_cores=own.get("cpu_cores", cpu_cores or (1 if self.weighted_cpu else None)),
        )

    def with_overrides(
        self,
        *,
        workers: int | None = None,
        memory_budget_mb: int | None = None,
        time_seconds: float | None = None,
        memory_mb: int | None = None,
        cpu_budget_cores: int | None = None,
        run_time_seconds: float | None = None,
        scratch_root: Path | None = None,
        scratch_budget_mb: int | None = None,
    ) -> BatchConfig:
        """The configuration with command-line values for the scheduler settings and the default limits."""
        config = replace(
            self,
            workers=self.workers if workers is None else workers,
            memory_budget_mb=self.memory_budget_mb if memory_budget_mb is None else memory_budget_mb,
            cpu_budget_cores=self.cpu_budget_cores if cpu_budget_cores is None else cpu_budget_cores,
            run_time_seconds=self.run_time_seconds if run_time_seconds is None else run_time_seconds,
            scratch_root=self.scratch_root if scratch_root is None else scratch_root,
            scratch_budget_mb=self.scratch_budget_mb if scratch_budget_mb is None else scratch_budget_mb,
            default_limits=Limits(
                time_seconds=self.default_limits.time_seconds if time_seconds is None else time_seconds,
                memory_mb=self.default_limits.memory_mb if memory_mb is None else memory_mb,
                cpu_cores=self.default_limits.cpu_cores,
            ),
        )
        config.validate()
        return config

    def validate(self) -> None:
        if self.workers < 1:
            raise ConfigError("workers must be at least 1")
        if self.memory_budget_mb < 1:
            raise ConfigError("memory_budget_mb must be positive")
        for field, value in (
            ("cpu_budget_cores", self.cpu_budget_cores),
            ("scratch_budget_mb", self.scratch_budget_mb),
        ):
            if value is not None and (type(value) is not int or value <= 0):
                raise ConfigError(f"scheduler.{field} must be a positive integer")
        if self.run_time_seconds is not None:
            _check_limits("scheduler run deadline", {"time_seconds": self.run_time_seconds})
        if (self.scratch_root is None) != (self.scratch_budget_mb is None):
            raise ConfigError("scheduler requires both scratch_root and scratch_budget_mb")
        _check_limits("limits", self.default_limits.as_dict())
        for tier in self.tiers:
            _check_limits(
                f"tier min_cost = {tier.min_cost}",
                _present(tier.time_seconds, tier.memory_mb, tier.cpu_cores),
            )
        for index, own in enumerate(self.set_limits):
            _check_limits(f"tasks[{index}].limits", own)

    def as_dict(self) -> dict[str, Any]:
        """The resolved configuration, as written to the run's record."""
        return {
            "name": self.name,
            "scheduler": {"workers": self.workers, "memory_budget_mb": self.memory_budget_mb}
            | {
                name: value
                for name, value in {
                    "cpu_budget_cores": self.cpu_budget_cores,
                    "run_time_seconds": self.run_time_seconds,
                    "scratch_root": str(self.scratch_root) if self.scratch_root is not None else None,
                    "scratch_budget_mb": self.scratch_budget_mb,
                }.items()
                if value is not None
            },
            "limits": self.default_limits.as_dict()
            | {
                "tier": [
                    {"min_cost": t.min_cost} | _present(t.time_seconds, t.memory_mb, t.cpu_cores)
                    for t in self.tiers
                ]
            },
            "set_limits": list(self.set_limits),
            "description": self.description,
            "graph": self.graph,
            **({"resources": asdict(self.resources)} if self.resources else {}),
        }


def _present(time_seconds: float | None, memory_mb: int | None, cpu_cores: int | None) -> dict[str, Any]:
    out: dict[str, Any] = {}
    if time_seconds is not None:
        out["time_seconds"] = time_seconds
    if memory_mb is not None:
        out["memory_mb"] = memory_mb
    if cpu_cores is not None:
        out["cpu_cores"] = cpu_cores
    return out


def _check_limits(where: str, limits: dict[str, Any]) -> None:
    unknown = set(limits) - {"time_seconds", "memory_mb", "cpu_cores"}
    if unknown:
        raise ConfigError(f"{where}: unknown key {sorted(unknown)[0]!r}")
    for key, value in limits.items():
        if isinstance(value, bool) or not isinstance(value, (int, float)) or value <= 0:
            raise ConfigError(f"{where}: {key} must be a positive number")
        if isinstance(value, float) and not math.isfinite(value):
            raise ConfigError(f"{where}: {key} must be a finite number")
    for key in ("memory_mb", "cpu_cores"):
        if key in limits and not isinstance(limits[key], int):
            raise ConfigError(f"{where}: {key} must be a whole number")


def _table(data: dict[str, Any], key: str, where: str) -> dict[str, Any]:
    value = data.get(key, {})
    if not isinstance(value, dict):
        raise ConfigError(f"{where}{key} must be a table")
    return value


def _require(table: dict[str, Any], key: str, where: str) -> Any:
    if key not in table:
        raise ConfigError(f"{where} needs {key}")
    return table[key]


def parse_config(data: dict[str, Any], *, default_name: str = "batch") -> BatchConfig:
    """Builds the configuration from the content of a batch file."""
    known = {"name", "scheduler", "limits", "surfaces", "tasks", "graph", "resources"}
    unknown = set(data) - known
    if unknown:
        raise ConfigError(f"unknown key {sorted(unknown)[0]!r}; expected {', '.join(sorted(known))}")

    scheduler = _table(data, "scheduler", "")
    limits = dict(_table(data, "limits", ""))
    tiers_data = limits.pop("tier", [])
    if not isinstance(tiers_data, list):
        raise ConfigError("limits.tier must be an array of tables")
    tiers = []
    for entry in tiers_data:
        entry = dict(entry)
        min_cost = entry.pop("min_cost", None)
        if not isinstance(min_cost, (int, float)) or isinstance(min_cost, bool):
            raise ConfigError("every [[limits.tier]] needs a number min_cost")
        _check_limits(f"tier min_cost = {min_cost}", entry)
        tiers.append(
            Tier(min_cost, entry.get("time_seconds"), entry.get("memory_mb"), entry.get("cpu_cores"))
        )

    task_sets = data.get("tasks", [])
    if not isinstance(task_sets, list) or not task_sets:
        raise ConfigError("the batch needs at least one [[tasks]] table")
    set_limits = []
    described_sets = []
    for index, task_set in enumerate(task_sets):
        if not isinstance(task_set, dict) or "kind" not in task_set:
            raise ConfigError(f"tasks[{index}] needs a kind")
        task_set = dict(task_set)
        own = task_set.pop("limits", {})
        if not isinstance(own, dict):
            raise ConfigError(f"tasks[{index}].limits must be a table")
        set_limits.append(dict(own))
        described_sets.append(task_set)

    _check_limits("limits", limits)
    try:
        resources = ResourcePolicy.parse(_table(data, "resources", "")) if "resources" in data else None
    except ValueError as problem:
        raise ConfigError(str(problem)) from problem
    raw_scratch = scheduler.get("scratch_root")
    if raw_scratch is not None and (not isinstance(raw_scratch, str) or not raw_scratch):
        raise ConfigError("scheduler.scratch_root must be a directory path")
    config = BatchConfig(
        name=str(data.get("name", default_name)),
        workers=_require(scheduler, "workers", "[scheduler]"),
        memory_budget_mb=_require(scheduler, "memory_budget_mb", "[scheduler]"),
        default_limits=Limits(
            time_seconds=_require(limits, "time_seconds", "[limits]"),
            memory_mb=_require(limits, "memory_mb", "[limits]"),
            cpu_cores=limits.get("cpu_cores"),
        ),
        tiers=tuple(tiers),
        set_limits=tuple(set_limits),
        description={"surfaces": data.get("surfaces", []), "tasks": described_sets},
        graph=_table(data, "graph", "") if "graph" in data else None,
        resources=resources,
        cpu_budget_cores=scheduler.get("cpu_budget_cores"),
        run_time_seconds=scheduler.get("run_time_seconds"),
        scratch_root=Path(raw_scratch) if raw_scratch is not None else None,
        scratch_budget_mb=scheduler.get("scratch_budget_mb"),
    )
    if not isinstance(config.workers, int) or not isinstance(config.memory_budget_mb, int):
        raise ConfigError("[scheduler] workers and memory_budget_mb must be whole numbers")
    config.validate()
    return config


def load_config(path: Path) -> BatchConfig:
    """Reads a batch file (TOML)."""
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except tomllib.TOMLDecodeError as problem:
        raise ConfigError(f"{path}: {problem}") from None
    try:
        return parse_config(data, default_name=path.stem)
    except ConfigError as problem:
        raise ConfigError(f"{path}: {problem}") from None
