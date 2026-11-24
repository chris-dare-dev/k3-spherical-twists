"""File protocol for Macaulay2 requests and replies."""

from __future__ import annotations

import json
import math
import shutil
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Any
from uuid import uuid4

from ..tasks import RUNNER_STATUSES, Status, Task, TaskError

VERSION = 2
# the argument that asks a runner for this protocol; the request and response files follow it
MODE = "protocol-v2"
OPERATIONS = {"expand": 1, "run": 1}


class WireError(ValueError):
    """A request or reply violated the file protocol."""


def _object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise WireError(f"{label} must be an object")
    return value


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise WireError(f"duplicate field {key!r}")
        result[key] = value
    return result


def _finite_float(value: str) -> float:
    number = float(value)
    if not math.isfinite(number):
        raise WireError(f"nonfinite number {value}")
    return number


def _string(obj: dict[str, Any], key: str) -> str:
    value = obj.get(key)
    if not isinstance(value, str) or not value:
        raise WireError(f"{key} must be a nonempty string")
    return value


def _integer(obj: dict[str, Any], key: str, minimum: int = 0) -> int:
    value = obj.get(key)
    if type(value) is not int or value < minimum:
        raise WireError(f"{key} must be an integer >= {minimum}")
    return value


def _number(obj: dict[str, Any], key: str) -> None:
    value = obj.get(key)
    if not isinstance(value, (int, float)) or isinstance(value, bool) or value < 0:
        raise WireError(f"{key} must be a nonnegative number")


def check_task(obj: Any) -> Task:
    """A task as the file protocol carries it, in an expansion and in a run request."""
    try:
        return Task.from_payload(obj, complete=True)
    except TaskError as problem:
        raise WireError(str(problem)) from None


def check_expansion(payload: dict[str, Any]) -> tuple[list[Task], dict[str, Any]]:
    tasks = payload.get("tasks")
    if not isinstance(tasks, list) or _integer(payload, "count") != len(tasks):
        raise WireError("incomplete expansion")
    versions = _object(payload.get("versions"), "versions")
    for key in ("m2_version", "package"):
        _string(versions, key)
    return [check_task(task) for task in tasks], versions | {"protocol_version": VERSION}


def check_result(payload: dict[str, Any]) -> dict[str, Any]:
    status = _string(payload, "status")
    if status not in RUNNER_STATUSES:
        raise WireError(f"unrecognized result status {status!r}")
    for key in ("value", "predicted", "agrees"):
        if key not in payload:
            raise WireError(f"result omitted required field {key!r}")
    agrees = payload["agrees"]
    if agrees is not None and type(agrees) is not bool:
        raise WireError("agrees must be boolean or null")
    if status == Status.UNSUPPORTED and (payload["value"] is not None or agrees is not None):
        raise WireError("unsupported result must have null value and agrees")
    computed = status != Status.UNSUPPORTED
    if computed and (payload["value"] is None or (status == Status.MISMATCH) != (agrees is False)):
        raise WireError("result status disagrees with its fields")
    _string(payload, "method")
    for key in ("setup_seconds", "compute_seconds"):
        _number(payload, key)
    return payload


@dataclass(frozen=True)
class FileRequest:
    directory: Path
    operation: str
    request_id: str

    @classmethod
    def create(cls, directory: Path, operation: str, payload: dict[str, Any]) -> FileRequest:
        if operation == "run":
            check_task(payload)
        request_id = uuid4().hex
        header = {"version": VERSION, "operation_version": OPERATIONS[operation]}
        content = header | {"operation": operation, "request_id": request_id, "payload": payload}
        body = json.dumps(content, ensure_ascii=False, allow_nan=False)
        directory.mkdir(parents=True, exist_ok=True)
        path = Path(tempfile.mkdtemp(prefix=f"{operation}-", dir=directory.resolve()))
        request = cls(path, operation, request_id)
        try:
            (path / "request.json").write_text(body, encoding="utf-8")
        except BaseException:
            request.cleanup()
            raise
        return request

    @property
    def args(self) -> list[str]:
        return [MODE, str(self.directory / "request.json"), str(self.directory / "response.json")]

    def read(self, exit_code: int) -> dict[str, Any] | None:
        response = self.directory / "response.json"
        try:
            content = response.read_text(encoding="utf-8")
        except FileNotFoundError:
            if exit_code:
                return None
            raise WireError("runner exited successfully without a response") from None
        except UnicodeError as problem:
            raise WireError("response is not UTF-8") from problem
        try:
            envelope = _object(
                json.loads(
                    content,
                    object_pairs_hook=unique_object,
                    parse_float=_finite_float,
                    parse_constant=_finite_float,
                ),
                "response",
            )
        except (ValueError, RecursionError) as problem:
            raise WireError(f"invalid response JSON: {problem}") from problem
        if _integer(envelope, "version") != VERSION:
            raise WireError("unknown response protocol version")
        if _integer(envelope, "operation_version") != OPERATIONS[self.operation]:
            raise WireError("unknown response operation version")
        if envelope.get("request_id") != self.request_id or envelope.get("operation") != self.operation:
            raise WireError("response does not match request ID and operation")
        outcome = envelope.get("type")
        payload = _object(envelope.get("payload"), "response payload")
        if outcome == "failure":
            raise WireError(f"{_string(payload, 'code')}: {_string(payload, 'message')}")
        expected = "expansion" if self.operation == "expand" else "result"
        if exit_code or outcome != expected:
            raise WireError(f"expected a successful {expected} response")
        outputs = envelope.get("outputs")
        if not isinstance(outputs, list):
            raise WireError("outputs must be a list of artifact references")
        for output in outputs:
            reference = _object(output, "artifact reference")
            for field in ("name", "media_type", "digest"):
                _string(reference, field)
        return payload | ({"outputs": outputs} if outputs and self.operation == "run" else {})

    def cleanup(self) -> None:
        shutil.rmtree(self.directory)
