"""A runner without mathematics, for testing the scheduler.

It follows the protocol of the Macaulay2 runner, in both of its forms: request and response files when
its last three arguments are `protocol-v2 REQUEST RESPONSE`, marker lines when they are `expand JSON` or
`run JSON`.  A batch description lists items; each becomes one task, and its keys say how the task
behaves:

    cost         the task's cost
    sleep        seconds to sleep
    allocate_mb  megabytes to hold while it sleeps
    exit         exit with this status and an error message instead of a result
    signal       end by this signal instead of giving a result
    silent       exit with status 0 without giving a result
    garbled      give a result that is not one (file protocol: a response that is not JSON)
    value, predicted   reported in the result; "mismatch" when both are given and differ
    read_source  read src/K3Twists.m2 relative to this script and the working directory
    edit_source  replace src/K3Twists.m2 in the named checkout; commit when commit_source is set

With `--journal FILE` every run appends "start <pid> <time> <id>" and "end <pid> <time> <id>" lines.
"""

from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from typing import Any

VERSIONS = {"fake_version": "1"}
# what the file protocol asks of every runner on top of the above
FILE_VERSIONS = {"m2_version": "none", "package": "fake 1"}
FILE_TASK = {"kind_version": 1, "requirements": []}


def expand(description: dict) -> list[dict]:
    return [
        dict(item)
        | {
            "id": f"fake/{item['name']}",
            "kind": "fake",
            "set": index,
            "group": task_set.get("group", "fake"),
            "cost": item.get("cost", 0),
        }
        for index, task_set in enumerate(description.get("tasks", []))
        for item in task_set.get("items", [])
    ]


def note(journal: str | None, word: str, task: dict) -> None:
    if journal:
        line = f"{word} {os.getpid()} {time.time():.6f} {task['id']}\n"
        fd = os.open(journal, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
        os.write(fd, line.encode())
        os.close(fd)


def run(task: dict, journal: str | None) -> dict | None:
    """The result of a task, or None for a task that gives none; a task that fails does not return."""
    note(journal, "start", task)
    held = bytearray(b"x") * (int(task.get("allocate_mb", 0)) << 20)
    time.sleep(float(task.get("sleep", 0)))
    note(journal, "end", task)
    if "exit" in task:
        print("fake_runner.py:1:1: error: asked to fail", file=sys.stderr)
        sys.exit(int(task["exit"]))
    if "signal" in task:
        os.kill(os.getpid(), getattr(signal, task["signal"]))
    if task.get("silent"):
        return None
    value = task.get("value", len(held))
    if task.get("read_source"):
        value = [
            (Path(__file__).resolve().parents[1] / "K3Twists.m2").read_text(),
            Path("src/K3Twists.m2").read_text(),
        ]
    if "edit_source" in task:
        checkout = Path(task["edit_source"])
        (checkout / "src" / "K3Twists.m2").write_text("after capture\n")
        if task.get("commit_source"):
            subprocess.run(
                ["git", "-C", str(checkout), "commit", "-am", "change the source during a run"],
                check=True,
            )
    predicted = task.get("predicted")
    agrees = None if predicted is None else value == predicted
    if task.get("unsupported"):
        status, value, agrees = "unsupported", None, None
    else:
        status = "mismatch" if agrees is False else "ok"
    result = {"status": status, "value": value, "predicted": predicted, "agrees": agrees, "method": "fake"}
    if "produce" in task:
        result["artifacts"] = task["produce"]
    if "inputs" in task:
        result["value"] = {name: source["digest"] for name, source in task["inputs"].items()}
    return result


def serve_files(source: str, destination: str, journal: str | None) -> None:
    """Protocol v2: one request object in a file, one response object in another."""
    request = json.loads(Path(source).read_text(encoding="utf-8"))
    header = {key: request[key] for key in ("version", "operation_version", "operation", "request_id")}
    payload = request["payload"]

    def respond(kind: str, content: dict[str, Any]) -> None:
        envelope = header | {"type": kind, "payload": content, "outputs": []}
        Path(destination).write_text(json.dumps(envelope), encoding="utf-8")

    if request["operation"] == "expand":
        tasks = [task | FILE_TASK for task in expand(payload)]
        respond("expansion", {"tasks": tasks, "count": len(tasks), "versions": VERSIONS | FILE_VERSIONS})
    elif payload.get("garbled"):
        Path(destination).write_text("{not json", encoding="utf-8")
    else:
        result = run(payload, journal)
        if result is not None:
            respond("result", result | {"setup_seconds": 0, "compute_seconds": 0})


def serve_markers(operation: str, request: dict, journal: str | None) -> None:
    """The legacy protocol: the request in the arguments, the reply in marked lines of the output."""
    if operation == "expand":
        tasks = expand(request)
        for task in tasks:
            print("@task " + json.dumps(task))
        print("@meta " + json.dumps(VERSIONS | {"tasks": len(tasks)}))
    elif request.get("garbled"):
        print("@result {not json")
    else:
        result = run(request, journal)
        if result is not None:
            print("@result " + json.dumps(result))


def main(argv: list[str]) -> int:
    journal = None
    if argv[:1] == ["--journal"]:
        journal, argv = argv[1], argv[2:]
    if len(argv) == 3 and argv[0] == "protocol-v2":
        serve_files(argv[1], argv[2], journal)
    elif len(argv) == 2 and argv[0] in {"expand", "run"}:
        serve_markers(argv[0], json.loads(argv[1]), journal)
    else:
        print(
            "usage: fake_runner.py [--journal FILE] (protocol-v2 REQUEST RESPONSE | (expand|run) JSON)",
            file=sys.stderr,
        )
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
