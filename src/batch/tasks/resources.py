"""Opt-in resource estimates and bounded retries for comparable computations."""

from __future__ import annotations

import math
from collections.abc import Mapping, Sequence
from dataclasses import dataclass, fields
from typing import Any

from .model import Limits, Status, Task

MIB = 1 << 20
HISTORY_WINDOW = 12


@dataclass(frozen=True)
class ResourcePolicy:
    minimum_samples: int = 3
    retry_attempts: int = 0
    memory_ceiling_mb: int = 4096
    time_ceiling_seconds: int = 600
    cpu_ceiling: int = 4

    @classmethod
    def parse(cls, data: dict[str, Any]) -> ResourcePolicy:
        if data.keys() - {field.name for field in fields(cls)}:
            raise ValueError("unknown resource policy field")
        for name, value in data.items():
            minimum = 0 if name == "retry_attempts" else 1
            if type(value) is not int or value < minimum:
                raise ValueError(f"resources.{name} must be an integer >= {minimum}")
        policy = cls(**data)
        if policy.minimum_samples > HISTORY_WINDOW:
            raise ValueError(f"resources.minimum_samples cannot exceed {HISTORY_WINDOW}")
        if policy.retry_attempts > 5:
            raise ValueError("resources.retry_attempts cannot exceed 5")
        return policy

    def caps(self, memory_budget: int, core_budget: int) -> Limits:
        return Limits(
            self.time_ceiling_seconds,
            min(self.memory_ceiling_mb, memory_budget),
            min(self.cpu_ceiling, core_budget),
        )


def resource_context(task: Task, computation_id: str, guard: str, core_budget: int) -> dict[str, Any]:
    surface = task.payload.get("surface") or {}
    return {
        "version": 1,
        "computation_id": computation_id,
        "operation": task.kind,
        "method_hint": task.payload.get("method_hint", task.kind),
        "family": surface.get("family", "complete_intersection") if isinstance(surface, dict) else None,
        "input_size": task.payload.get("input_size", {"cost": task.cost}),
        "backend": "linux-local",
        "guard": guard,
        "run_cpu_cores": core_budget,
        "memory_measure": "cgroup_memory_peak_bytes" if guard == "cgroup" else "peak_sampled_bytes",
        "units": {"memory": "bytes", "time": "seconds", "cpu": "cores"},
        "measurement_basis": "job tree and execution wall time",
    }


def estimate(
    defaults: Limits,
    caps: Limits,
    policy: ResourcePolicy,
    context: dict[str, Any],
    history: Sequence[Mapping[str, Any]],
) -> tuple[Limits, dict[str, Any]]:
    comparable = [row for row in history if row.get("resource_context") == context]
    measure = context["memory_measure"]
    measured = [
        row
        for row in comparable
        if row["status"] in {Status.OK, Status.MISMATCH}
        and type(row.get(measure)) is int
        and row[measure] > 0
        and row.get("wall_seconds", 0) > 0
        and row.get("cpu_seconds", 0) > 0
    ]
    chosen_method = measured[0].get("detail", {}).get("method") if measured else None
    measured = [row for row in measured if row.get("detail", {}).get("method") == chosen_method]
    enough = len(measured) >= policy.minimum_samples
    if enough:
        time = max(1, math.ceil(1.5 * max(row["wall_seconds"] for row in measured) + 1))
        memory = max(32, math.ceil(1.3 * max(row[measure] for row in measured) / MIB))
        cores = max(1, math.ceil(1.25 * max(row["cpu_seconds"] / row["wall_seconds"] for row in measured)))
    else:
        time, memory, cores = defaults.time_seconds, defaults.memory_mb, defaults.cpu_cores or 1
    censored = [
        trial
        for row in comparable
        for trial in row.get("resource_attempts", [row])
        if trial["status"] in {Status.MEMORY, Status.TIMEOUT}
    ]
    if enough:
        for trial in censored:
            if trial["status"] == Status.MEMORY:
                memory = max(memory, math.ceil(1.25 * trial["limits"]["memory_mb"]))
            if trial["status"] == Status.TIMEOUT:
                time = max(time, math.ceil(1.25 * trial["limits"]["time_seconds"]))
    limits = Limits(
        min(time, caps.time_seconds), min(memory, caps.memory_mb), min(cores, caps.cpu_cores or 1)
    )
    return limits, {
        "basis": "compatible successes" if enough else "configured defaults and tiers",
        "fingerprint_context": context,
        "measured_method": chosen_method,
        "samples": [row["record_id"] for row in measured],
        "censored_trials": len(censored),
        "ceilings": caps.as_dict(),
        "request": limits.as_dict(),
    }


def grow_limits(limits: Limits, caps: Limits, status: str) -> Limits | None:
    if status == Status.MEMORY and limits.memory_mb < caps.memory_mb:
        return Limits(
            limits.time_seconds, min(caps.memory_mb, math.ceil(limits.memory_mb * 1.5)), limits.cpu_cores
        )
    if status == Status.TIMEOUT and limits.time_seconds < caps.time_seconds:
        return Limits(min(caps.time_seconds, limits.time_seconds * 1.5), limits.memory_mb, limits.cpu_cores)
    return None
