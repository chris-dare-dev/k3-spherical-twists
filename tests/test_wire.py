"""Versioned file requests and replies at the process boundary."""

from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from pathlib import Path

from k3batch.runner import DEFAULT_RUNNER, RunnerError, RunnerInvocation, expand
from k3batch.wire import FileRequest, WireError, check_result


class FileProtocol(unittest.TestCase):
    def setUp(self) -> None:
        scratch = tempfile.TemporaryDirectory()
        self.addCleanup(scratch.cleanup)
        self.root = Path(scratch.name)
        task = {
            "id": "synthetic/1",
            "group": "synthetic",
            "kind": "synthetic",
            "set": 0,
            "cost": 0,
            "kind_version": 1,
            "requirements": [],
        }
        self.request = FileRequest.create(self.root, "run", task)
        self.response = self.request.directory / "response.json"
        self.value = {"large": 2**90 + 1, "decimal": 0.1501, "optional": None}
        self.payload = {
            "status": "ok",
            "value": self.value,
            "predicted": None,
            "agrees": None,
            "method": "synthetic",
            "setup_seconds": 0,
            "compute_seconds": 0.001,
        }
        self.envelope = {
            "version": 2,
            "operation_version": 1,
            "operation": "run",
            "request_id": self.request.request_id,
            "type": "result",
            "payload": self.payload,
            "outputs": [],
        }

    def test_reads_exact_integers_fractional_reals_and_nulls(self) -> None:
        self.response.write_text(json.dumps(self.envelope), encoding="utf-8")
        payload = self.request.read(0)
        self.assertIsNotNone(payload)
        assert payload is not None
        self.assertEqual(check_result(payload)["value"], self.value)

    def test_rejects_incompatible_incomplete_and_duplicate_replies(self) -> None:
        invalid = (
            (json.dumps(self.envelope | {"version": 3}), "protocol version"),
            (json.dumps(self.envelope | {"operation_version": 3}), "operation version"),
            (json.dumps(self.envelope | {"request_id": "unrelated"}), "request ID"),
            (json.dumps(self.envelope | {"type": "expansion"}), "expected a successful result"),
            (json.dumps(self.envelope)[:-1], "invalid response JSON"),
            (json.dumps(self.envelope) * 2, "invalid response JSON"),
            ('{"version": 1, "version": 2}', "duplicate field"),
        )
        for content, diagnostic in invalid:
            with self.subTest(diagnostic=diagnostic):
                self.response.write_text(content, encoding="utf-8")
                with self.assertRaisesRegex(WireError, diagnostic):
                    self.request.read(0)
        with self.assertRaisesRegex(WireError, "omitted"):
            check_result({key: value for key, value in self.payload.items() if key != "predicted"})

    def test_structured_failure_survives_a_nonzero_exit(self) -> None:
        failure = {"code": "invalid_request", "message": "unknown task kind"}
        envelope = self.envelope | {"type": "failure", "payload": failure}
        self.response.write_text(json.dumps(envelope), encoding="utf-8")
        with self.assertRaisesRegex(WireError, "invalid_request: unknown task kind"):
            self.request.read(2)

    def test_bundled_makefile_entrypoint_uses_a_file_for_large_input(self) -> None:
        runner = ("M2", "--script", "runners/task-runner.m2")
        large = "🧪" * 200_000
        invocation = RunnerInvocation.prepare(runner, "expand", {"fixture": large}, self.root)
        self.addCleanup(invocation.cleanup)
        self.assertEqual(invocation.command[-3], "protocol-v2")
        self.assertLess(sum(map(len, invocation.command)), 4_096)
        request = json.loads(Path(invocation.command[-2]).read_text(encoding="utf-8"))
        self.assertEqual(request["payload"]["fixture"], large)

    def test_expand_rejects_incomplete_results_through_backend_callback(self) -> None:
        def execute(command: list[str], timeout: float) -> subprocess.CompletedProcess[str]:
            self.assertEqual(timeout, 19)
            header = json.loads(Path(command[-2]).read_text(encoding="utf-8"))
            header["type"] = "expansion"
            header["payload"] = {"count": 1, "tasks": [], "versions": {}}
            header["outputs"] = []
            Path(command[-1]).write_text(json.dumps(header), encoding="utf-8")
            return subprocess.CompletedProcess(command, 0, "@task distracting diagnostics", "")

        with self.assertRaisesRegex(RunnerError, "incomplete expansion"):
            expand(DEFAULT_RUNNER, {}, timeout=19, execute=execute)


if __name__ == "__main__":
    unittest.main()
