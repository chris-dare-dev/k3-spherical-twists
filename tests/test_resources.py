"""Resource evidence, request ceilings, and admission of retries."""

from __future__ import annotations

import sys
import unittest
from dataclasses import replace

from k3batch.model import Limits, Task
from k3batch.record import Record
from k3batch.resources import MIB, ResourcePolicy, estimate, resource_context
from tests.helpers import SchedulerCase, fake_config


class ResourceEstimate(unittest.TestCase):
    def test_matches_method_and_measurement_and_keeps_limit_failures_censored(self) -> None:
        task = Task.from_payload({"id": "model", "kind": "fake", "input_size": {"rows": 6, "columns": 8}})
        context = resource_context(task, "request-id", "cgroup", 4)
        policy = ResourcePolicy(minimum_samples=2, memory_ceiling_mb=256)
        caps = policy.caps(512, 4)
        sample = {
            "status": "ok",
            "resource_context": context,
            "cgroup_memory_peak_bytes": 80 * MIB,
            "peak_sampled_bytes": 800 * MIB,
            "wall_seconds": 8,
            "cpu_seconds": 13,
            "detail": {"method": "first"},
        }
        censored = sample | {"status": "memory", "limits": {"memory_mb": 106}}
        history = [
            sample | {"record_id": "first"},
            sample | {"record_id": "second"},
            sample | {"record_id": "method", "detail": {"method": "different"}},
            sample | {"record_id": "poll", "resource_context": context | {"guard": "poll"}},
            censored,
        ]
        limits, evidence = estimate(Limits(60, 150), caps, policy, context, history)
        self.assertEqual(limits, Limits(13, 133, 3))
        self.assertEqual(evidence["samples"], ["first", "second"])
        self.assertEqual(evidence["censored_trials"], 1)
        self.assertEqual(evidence["measured_method"], "first")
        fallback, evidence = estimate(Limits(60, 150), caps, policy, context, history[:1])
        self.assertEqual(fallback, Limits(60, 150, 1))
        self.assertEqual(evidence["basis"], "configured defaults and tiers")


@unittest.skipUnless(sys.platform == "linux", "Linux backend")
class ResourceRetries(SchedulerCase):
    def test_retry_waits_for_memory_admission_and_preserves_both_trials(self) -> None:
        config = replace(
            fake_config(
                {"items": [{"name": "target", "allocate_mb": 40, "sleep": 0.5}], "limits": {"memory_mb": 42}},
                {"items": [{"name": "neighbor", "sleep": 2}], "limits": {"memory_mb": 50}},
                memory_budget_mb=100,
                workers=2,
            ),
            resources=ResourcePolicy(minimum_samples=1, retry_attempts=2, memory_ceiling_mb=100),
        )
        self.assertEqual(self.run_batch(config), {"ok": 2})
        record = self.latest()["fake/target"]
        self.assertLessEqual(set(record), set(Record.__annotations__))
        first, second = record["resource_attempts"]
        self.assertEqual([r["status"] for r in (first, second)], ["memory", "ok"])
        self.assertEqual([r["limits"]["memory_mb"] for r in (first, second)], [42, 63])
        self.assertNotEqual(first["trial_id"], second["trial_id"])
        self.assertEqual(first["attempt_id"], second["attempt_id"])
        self.assertEqual(first["decision"], "retry with larger reservation")
        self.assertIsNone(first["cgroup_memory_peak_bytes"])
        self.assertGreater(first["peak_sampled_bytes"], 42 * MIB)
        intervals = self.journal.lines()
        neighbor_end = next(
            when for word, _, when, task in intervals if (word, task) == ("end", "fake/neighbor")
        )
        retry_start = max(
            when for word, _, when, task in intervals if (word, task) == ("start", "fake/target")
        )
        self.assertGreaterEqual(retry_start, neighbor_end)
        self.assertEqual(self.run_batch(config), {})
        self.assertEqual(self.run_batch(config, retry={"ok"}), {"ok": 2})
        updated = self.latest()["fake/target"]
        self.assertEqual(updated["resource_estimate"]["basis"], "compatible successes")
        self.assertEqual(updated["resource_estimate"]["samples"], [record["record_id"]])

    def test_retry_stops_at_configured_ceiling(self) -> None:
        config = replace(
            fake_config([{"name": "limited", "allocate_mb": 80, "sleep": 0.5}], memory_mb=42),
            resources=ResourcePolicy(retry_attempts=4, memory_ceiling_mb=60),
        )
        self.assertEqual(self.run_batch(config), {"memory": 1})
        attempts = self.latest()["fake/limited"]["resource_attempts"]
        self.assertEqual([a["limits"]["memory_mb"] for a in attempts], [42, 60])
        self.assertEqual(attempts[-1]["decision"], "ceiling reached")
