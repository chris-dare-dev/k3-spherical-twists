"""Dependency validation, durable readiness, and artifact reuse."""

from __future__ import annotations

import sqlite3
from dataclasses import replace
from hashlib import sha256
from typing import Any
from uuid import uuid4

from k3batch.config import ConfigError
from k3batch.graph import Graph
from k3batch.memory import PollingGuard
from k3batch.report import selected_results
from k3batch.runner import expand
from k3batch.scheduler import Progress, Scheduler
from k3batch.sqlite_store import SQLiteStore
from k3batch.store import StoreLocked
from tests.helpers import Journal, SchedulerCase, fake_config
from tests.test_artifacts import MODEL, body


def node(name: str, parent: str | None = None, *, output: str | None = None) -> dict:
    declaration: dict[str, Any] = {"id": f"fake/{name}"}
    if parent is not None:
        declaration["inputs"] = {
            "value": {"producer": f"fake/{parent}", "output": "artifact", "kind": "k3-model"}
        }
    if output is not None:
        declaration["outputs"] = {"artifact": output}
    return declaration


class DependencyGraph(SchedulerCase):
    def setUp(self) -> None:
        super().setUp()
        self.database = self.run_dir.parent / "ledger.sqlite"
        self.store = SQLiteStore(self.database)

    def graph_run(self, config: Any, progress: Progress | None = None) -> str:
        tasks, versions = expand(self.runner, config.description)
        run_id = uuid4().hex
        with SQLiteStore(self.database) as store:
            scheduler = Scheduler(
                config=config, tasks=tasks, store=store, run_dir=self.run_dir, runner=self.runner,
                guard=PollingGuard(), stamp={"runner": versions, "run_id": run_id}, progress=progress,
            )  # fmt: skip
            plan = scheduler.plan()
            manifest = {"run_id": run_id, "schema_version": 1, "tasks": [p.manifest_entry() for p in plan]}
            with store.run(self.run_dir, manifest, {}):
                scheduler.run(plan)
        return run_id

    def test_shared_prefix_survives_interruption_and_branch_failure(self) -> None:
        config = replace(
            fake_config(
                [
                    {"name": "prefix", "produce": {"artifact": MODEL}, "cost": 5},
                    {"name": "first", "exit": 3},
                    {"name": "second"},
                    {"name": "child-of-first"},
                ],
                workers=2,
            ),
            graph={
                "version": 1,
                "nodes": [
                    node("prefix", output="k3-model"),
                    node("first", "prefix", output="k3-model"),
                    node("second", "prefix"),
                    node("child-of-first", "first"),
                ],
            },
        )

        def interrupt(record: dict, *_: Any) -> None:
            self.assertEqual(record["task_id"], "fake/prefix")
            with self.assertRaises(StoreLocked), SQLiteStore(self.database):
                self.fail("a second coordinator acquired the graph")
            raise KeyboardInterrupt

        with self.assertRaises(KeyboardInterrupt):
            self.graph_run(config, interrupt)
        interrupted = self.store.manifest(self.run_dir)
        self.assertEqual(interrupted["run_state"], "interrupted")
        prefix = selected_results(self.store, interrupted)["fake/prefix"]
        self.assertEqual(self.journal.started(), ["fake/prefix"])

        resumed = self.graph_run(config)
        records = selected_results(self.store, self.store.manifest(run_id=resumed))
        self.assertEqual(records["fake/prefix"]["attempt_id"], prefix["attempt_id"])
        self.assertEqual(records["fake/first"]["status"], "error")
        self.assertEqual(records["fake/child-of-first"]["status"], "blocked")
        self.assertIn("fake/first ended error", records["fake/child-of-first"]["error"])
        self.assertEqual(records["fake/second"]["status"], "ok")
        ref = prefix["detail"]["artifact_outputs"]["artifact"]
        for name in ("first", "second"):
            provenance = records[f"fake/{name}"]["detail"]["artifact_inputs"]["value"]
            self.assertEqual(
                (provenance["digest"], provenance["attempt_id"]), (ref["digest"], prefix["attempt_id"])
            )
        self.assertEqual(self.journal.started().count("fake/prefix"), 1)
        self.assertNotIn("fake/child-of-first", self.journal.started())
        journal_before = self.journal.started()
        self.graph_run(config)
        self.assertEqual(self.journal.started(), journal_before)

        # A corrupt digest can no longer be reused, including by cached consumers.
        blob = self.database.with_suffix(".sqlite.artifacts") / "objects" / f"{ref['digest']}.json"
        blob.write_bytes(b"invalid")
        invalidated = self.graph_run(config)
        fresh = selected_results(self.store, self.store.manifest(run_id=invalidated))
        self.assertEqual(fresh["fake/prefix"]["status"], "error")
        self.assertEqual(fresh["fake/second"]["status"], "blocked")

    def test_validate_graph_before_execution(self) -> None:
        config = fake_config([{"name": "a"}, {"name": "b"}])
        tasks, _ = expand(self.runner, config.description)
        invalid = (
            ([node("a", "a", output="k3-model")], "cycle"),
            ([node("a", "b")], "missing producer"),
            ([node("a", "b"), node("b", output="graded-complex")], "incompatible artifact"),
            ([node("a"), node("a", output="k3-model")], "conflicting"),
        )
        for nodes, error in invalid:
            with self.subTest(error=error), self.assertRaisesRegex(ConfigError, error):
                Graph.build(tasks, {"version": 1, "nodes": nodes})
        self.assertEqual(self.journal.started(), [])

    def test_model_binding_is_verified_before_the_consumer_starts(self) -> None:
        other = MODEL | {"payload": MODEL["payload"] | {"coordinates": ["different"]}}
        cone = {
            "version": 1,
            "kind": "graded-complex",
            "payload": {
                "base": 0,
                "terms": [[0]],
                "differentials": [],
                "model_digest": sha256(body(MODEL)).hexdigest(),
            },
        }
        prefix = node("prefix", "first-model", output="graded-complex")
        consumer = node("consumer", "other-model")
        consumer["inputs"]["cone"] = {
            "producer": "fake/prefix",
            "output": "artifact",
            "kind": "graded-complex",
            "model_input": "value",
        }
        config = replace(
            fake_config(
                [
                    {"name": "first-model", "produce": {"artifact": MODEL}},
                    {"name": "other-model", "produce": {"artifact": other}},
                    {"name": "prefix", "produce": {"artifact": cone}},
                    {"name": "consumer"},
                ]
            ),
            graph={
                "version": 1,
                "nodes": [
                    node("first-model", output="k3-model"),
                    node("other-model", output="k3-model"),
                    prefix,
                    consumer,
                ],
            },
        )
        run = self.graph_run(config)
        records = selected_results(self.store, self.store.manifest(run_id=run))
        self.assertEqual(records["fake/prefix"]["status"], "ok")
        self.assertEqual(records["fake/consumer"]["status"], "blocked")
        self.assertIn("incompatible model", records["fake/consumer"]["error"])
        self.assertNotIn("fake/consumer", self.journal.started())

    def test_claim_requires_committed_parent_and_protects_record_id(self) -> None:
        one, two = (
            {"id": label, "computation_id": label, "record_id": label, "check_id": label}
            for label in ("one", "two")
        )
        manifest = {"run_id": "claim", "tasks": [one, two]}
        with self.assertRaises(KeyboardInterrupt), self.store, self.store.run(self.run_dir, manifest, {}):
            self.store.start_attempt("claim", one, "first", "now", None)
            with self.assertRaisesRegex(RuntimeError, "successful committed attempt"):
                self.store.start_attempt("claim", two, "second", "now", None, prerequisites=["one"])
            with self.assertRaises(sqlite3.IntegrityError):
                self.store.start_attempt("claim", one, "duplicate", "now", None)
            raise KeyboardInterrupt

    def test_empty_graph_preserves_values_and_attempts_of_independent_tasks(self) -> None:
        config = fake_config([{"name": "agree", "value": 2, "predicted": 2}, {"name": "fail", "exit": 3}])
        first = self.graph_run(config)
        second = self.graph_run(replace(config, graph={"version": 1}))
        selections = [
            selected_results(self.store, self.store.manifest(run_id=run_id)) for run_id in (first, second)
        ]
        self.assertEqual(selections[0], selections[1])
        self.assertCountEqual(Journal(self.journal.path).started(), ["fake/agree", "fake/fail"])
