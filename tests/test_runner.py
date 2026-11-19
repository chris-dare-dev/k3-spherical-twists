"""The protocol with the runner: reading its tasks and results, refusing what is incomplete."""

from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from collections.abc import Callable
from dataclasses import replace
from pathlib import Path
from typing import Any

from k3batch.model import Task, TaskError
from k3batch.runner import RunnerError, code_version, error_lines, expand, parse_result, run_command
from k3batch.wire import WireError, check_task

from .helpers import FAKE_RUNNER, FILE_VERSIONS, MARKER_VERSIONS, fake_runner

# a task as the file protocol carries it, and the changes that no protocol accepts
COMPLETE = {
    "id": "a",
    "kind": "k",
    "group": "g",
    "set": 0,
    "cost": 1.5,
    "kind_version": 1,
    "requirements": [],
}
MALFORMED = (
    ({"id": ""}, "id must be a nonempty string"),
    ({"id": 7}, "id must be a nonempty string"),
    ({"kind": None}, "kind must be a nonempty string"),
    ({"group": ""}, "group must be a nonempty string"),
    ({"set": -1}, "set must be an integer >= 0"),
    ({"set": 1.0}, "set must be an integer >= 0"),
    ({"cost": -1}, "cost must be a nonnegative number"),
    ({"cost": "3"}, "cost must be a nonnegative number"),
    ({"cost": True}, "cost must be a nonnegative number"),
)


def printing(*lines: str, status: int = 0) -> tuple[str, ...]:
    """A runner that prints the given lines whatever it is asked."""
    program = f"import sys\nfor line in {list(lines)!r}: print(line)\nsys.exit({status})"
    return (sys.executable, "-c", program)


def filing(task: dict[str, Any]) -> Callable[[list[str], float], subprocess.CompletedProcess[str]]:
    """In place of a file-protocol runner: answers an expansion request with the given task."""

    def execute(command: list[str], timeout: float) -> subprocess.CompletedProcess[str]:
        versions = {"m2_version": "none", "package": "none"}
        envelope = json.loads(Path(command[-2]).read_text(encoding="utf-8")) | {
            "type": "expansion",
            "payload": {"count": 1, "tasks": [task], "versions": versions},
            "outputs": [],
        }
        Path(command[-1]).write_text(json.dumps(envelope), encoding="utf-8")
        return subprocess.CompletedProcess(command, 0, "", "")

    return execute


class Expansion(unittest.TestCase):
    def test_tasks_and_versions_are_read(self) -> None:
        description = {"tasks": [{"items": [{"name": "a", "cost": 2}, {"name": "b"}]}]}
        tasks, versions = expand(fake_runner(markers=True), description)
        self.assertEqual([task.id for task in tasks], ["fake/a", "fake/b"])
        self.assertEqual((tasks[0].kind, tasks[0].cost, tasks[0].set, tasks[0].group), ("fake", 2, 0, "fake"))
        self.assertEqual(tasks[0].payload["name"], "a")
        self.assertEqual(versions, MARKER_VERSIONS)

    def test_marker_lines_and_files_carry_the_same_tasks(self) -> None:
        description = {
            "tasks": [{"items": [{"name": "a", "cost": 2}]}, {"group": "g", "items": [{"name": "b"}]}]
        }
        marked, _ = expand(fake_runner(markers=True), description)
        filed, versions = expand(fake_runner(), description)
        self.assertEqual(versions, FILE_VERSIONS)
        self.assertEqual([(t.id, t.kind, t.cost, t.set, t.group) for t in filed], [
            ("fake/a", "fake", 2, 0, "fake"), ("fake/b", "fake", 0, 1, "g"),
        ])  # fmt: skip
        self.assertEqual([task.payload for task in filed], [
            task.payload | {"kind_version": 1, "requirements": []} for task in marked
        ])  # fmt: skip
        self.assertEqual([replace(task, payload={}) for task in filed], [
            replace(task, payload={}) for task in marked
        ])  # fmt: skip

    def test_other_output_is_ignored(self) -> None:
        runner = printing(
            " -- setting random seed to 1", '@task {"id": "a", "kind": "k"}', '@meta {"tasks": 1}'
        )
        tasks, _ = expand(runner, {})
        self.assertEqual(
            tasks, [Task(id="a", kind="k", cost=0, set=0, group="k", payload={"id": "a", "kind": "k"})]
        )

    def test_an_incomplete_list_is_refused(self) -> None:
        one = '@task {"id": "a", "kind": "k"}'
        for runner in (
            printing(one),  # no closing line
            printing(one, '@meta {"tasks": 2}'),  # a task is missing
            printing(one, one, '@meta {"tasks": 2}'),  # the same task twice
            printing('@task {"kind": "k"}', '@meta {"tasks": 1}'),  # a task without an id
            printing("@task {not json", '@meta {"tasks": 1}'),
        ):
            with self.subTest(runner=runner[-1]), self.assertRaises(RunnerError):
                expand(runner, {})

    def test_a_failing_runner_is_reported_with_its_message(self) -> None:
        with self.assertRaisesRegex(RunnerError, "status 2"):
            expand((sys.executable, str(FAKE_RUNNER), "nonsense"), {})
        with self.assertRaisesRegex(RunnerError, "not found"):
            expand(("no-such-program-anywhere",), {})


class TaskEnvelope(unittest.TestCase):
    def test_one_rule_decides_what_a_task_is_in_both_protocols(self) -> None:
        self.assertEqual(Task.from_payload(COMPLETE), check_task(COMPLETE))
        self.assertEqual(check_task(COMPLETE), Task("a", "k", 1.5, 0, "g", COMPLETE))
        for change, message in MALFORMED:
            with self.subTest(change=change):
                with self.assertRaisesRegex(TaskError, message):
                    Task.from_payload(COMPLETE | change)
                with self.assertRaisesRegex(WireError, message):
                    check_task(COMPLETE | change)
        with self.assertRaisesRegex(TaskError, "task must be an object"):
            Task.from_payload(["a"])

    def test_only_marker_lines_may_leave_fields_out(self) -> None:
        for field in ("set", "cost", "group", "kind_version", "requirements"):
            partial = {key: value for key, value in COMPLETE.items() if key != field}
            with self.subTest(field=field):
                Task.from_payload(partial)
                with self.assertRaisesRegex(WireError, field):
                    check_task(partial)
        for change in ({"kind_version": 0}, {"requirements": "none"}, {"requirements": [1]}):
            with self.subTest(change=change), self.assertRaises(WireError):
                check_task(COMPLETE | change)
        for field in ("id", "kind"):
            with self.subTest(field=field), self.assertRaisesRegex(TaskError, field):
                Task.from_payload({key: value for key, value in COMPLETE.items() if key != field})

    def test_a_malformed_task_stops_the_expansion_of_either_protocol(self) -> None:
        for change, message in MALFORMED:
            task = COMPLETE | change
            marked = printing("@task " + json.dumps(task), '@meta {"tasks": 1}')
            with self.subTest(change=change, protocol="marks"), self.assertRaisesRegex(RunnerError, message):
                expand(marked, {})
            with self.subTest(change=change, protocol="files"), self.assertRaisesRegex(RunnerError, message):
                expand(fake_runner(), {}, execute=filing(task))
        tasks, _ = expand(fake_runner(), {}, execute=filing(COMPLETE))
        self.assertEqual(tasks, [Task("a", "k", 1.5, 0, "g", COMPLETE)])


class Results(unittest.TestCase):
    def test_the_command_hands_the_task_back_unchanged(self) -> None:
        payload = {"id": "a", "kind": "k", "source": "M_H^dual(1H)"}
        command = run_command(("M2", "--script", "runner.m2"), Task.from_payload(payload))
        self.assertEqual(command[:4], ["M2", "--script", "runner.m2", "run"])
        self.assertEqual(json.loads(command[4]), payload)

    def test_the_last_result_line_is_the_result(self) -> None:
        output = ' -- noise\n@result {"status": "ok", "value": 1}\n@result {"status": "ok", "value": 2}\n'
        self.assertEqual(parse_result(output), {"status": "ok", "value": 2})
        self.assertIsNone(parse_result("no result here\n"))
        self.assertIsNone(parse_result("@result {broken\n"))
        self.assertIsNone(parse_result("@result [1, 2]\n"))

    def test_error_messages_come_without_the_backtrace(self) -> None:
        output = (
            " -- setting random seed to 1\n"
            "K3Twists/tasks.m2:153:60:(2):[8]: error: no sheaf named X\n"
            "K3Twists/tasks.m2:173:29:(2):[7]: --back trace--\n"
        )
        self.assertEqual(error_lines(output), "K3Twists/tasks.m2:153:60:(2):[8]: error: no sheaf named X")
        self.assertEqual(error_lines("something odd\n"), "something odd")


class CodeVersion(unittest.TestCase):
    def test_a_checkout_has_a_commit(self) -> None:
        version = code_version()
        if version["commit"] is None:
            self.skipTest("the code is not in a git checkout")
        self.assertRegex(version["commit"], "^[0-9a-f]{40}$")
        self.assertIn(version["dirty"], (True, False))

    def test_outside_a_repository_the_commit_is_unknown(self) -> None:
        with tempfile.TemporaryDirectory() as scratch:
            self.assertEqual(code_version(Path(scratch)), {"commit": None, "dirty": None})


if __name__ == "__main__":
    unittest.main()
