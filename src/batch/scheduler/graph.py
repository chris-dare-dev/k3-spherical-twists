"""Versioned task dependencies and the contracts for their artifacts."""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import asdict, dataclass
from graphlib import CycleError, TopologicalSorter
from typing import Any

from ..records import PAYLOAD_FIELDS
from ..tasks import ConfigError, Task


@dataclass(frozen=True)
class Input:
    producer: str
    output: str
    kind: str
    model_input: str | None = None


@dataclass(frozen=True)
class Node:
    inputs: dict[str, Input]
    outputs: dict[str, str]

    def identity(self, results: dict[str, str]) -> dict[str, Any]:
        return {
            "version": 1,
            "outputs": self.outputs,
            "inputs": {
                name: asdict(source) | {"record_id": results[source.producer]}
                for name, source in self.inputs.items()
            },
        }


@dataclass(frozen=True)
class Graph:
    nodes: dict[str, Node]
    levels: list[tuple[str, ...]]

    @classmethod
    def build(cls, tasks: Sequence[Task], definition: dict[str, Any] | None) -> Graph:
        ids = {task.id for task in tasks}
        if len(ids) != len(tasks):
            raise ConfigError("duplicate task definitions")
        if definition is None:
            return cls({}, [tuple(task.id for task in tasks)])
        if (
            type(definition.get("version")) is not int
            or definition["version"] != 1
            or set(definition) - {"version", "nodes"}
        ):
            raise ConfigError("expected a version 1 graph")
        declarations = definition.get("nodes", [])
        if not isinstance(declarations, list):
            raise ConfigError("graph.nodes must be an array of tables")
        nodes: dict[str, Node] = {}
        supplied_inputs = {task.id for task in tasks if "inputs" in task.payload}
        for item in declarations:
            if not isinstance(item, dict) or set(item) - {"id", "inputs", "outputs"}:
                raise ConfigError("invalid graph node definition")
            task_id = item.get("id")
            if not isinstance(task_id, str) or task_id not in ids:
                raise ConfigError(f"graph node {task_id!r} has no expanded task")
            if task_id in supplied_inputs:
                raise ConfigError(f"{task_id} sets inputs reserved by the graph")
            node = _node(item, task_id)
            if task_id in nodes and nodes[task_id] != node:
                raise ConfigError(f"conflicting graph definitions for {task_id}")
            nodes[task_id] = node
        for task_id, node in nodes.items():
            for source in node.inputs.values():
                producer = nodes.get(source.producer)
                if producer is None or source.output not in producer.outputs:
                    raise ConfigError(
                        f"{task_id} needs missing producer output {source.producer}/{source.output}"
                    )
                if producer.outputs[source.output] != source.kind:
                    raise ConfigError(f"{task_id} expects incompatible artifact kind {source.kind}")
        sorter = TopologicalSorter(
            {
                task.id: tuple(source.producer for source in nodes[task.id].inputs.values())
                if task.id in nodes
                else ()
                for task in tasks
            }
        )
        try:
            sorter.prepare()
        except CycleError as problem:
            raise ConfigError("cycle in task dependencies: " + " -> ".join(problem.args[1])) from None
        levels = []
        while sorter.is_active():
            level = sorter.get_ready()
            levels.append(level)
            sorter.done(*level)
        return cls(nodes, levels)


def _node(item: dict[str, Any], task_id: str) -> Node:
    raw_inputs, outputs = item.get("inputs", {}), item.get("outputs", {})
    if not isinstance(raw_inputs, dict) or not isinstance(outputs, dict):
        raise ConfigError(f"{task_id} inputs and outputs must be tables")
    inputs = {}
    for name, source in raw_inputs.items():
        if (
            not name
            or not isinstance(source, dict)
            or not {"producer", "output", "kind"} <= source.keys()
            or source.keys() - {"producer", "output", "kind", "model_input"}
            or not all(isinstance(value, str) and value for value in source.values())
            or source["kind"] not in PAYLOAD_FIELDS
        ):
            raise ConfigError(f"invalid graph input {task_id}/{name}")
        inputs[name] = Input(source["producer"], source["output"], source["kind"], source.get("model_input"))
    for name, binding in inputs.items():
        if binding.model_input is not None:
            parent = inputs.get(binding.model_input)
            if binding.kind == "k3-model" or parent is None or parent.kind != "k3-model":
                raise ConfigError(f"{task_id}/{name} needs a model_input bound to a k3-model")
    for name, kind in outputs.items():
        if not name or not isinstance(kind, str) or kind not in PAYLOAD_FIELDS:
            raise ConfigError(f"invalid graph output {task_id}/{name}")
    return Node(inputs, outputs)
