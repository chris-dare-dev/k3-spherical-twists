"""The claim tables, written from the registry, the batch files and the records.

Usage:  python3 -m batch.claims tables             write the generated parts of CLAIMS.md and GUIDE.md,
                                                  and data/claims/RECORDS.md (`make tables`)
        python3 -m batch.claims check              fail if they are not what `tables` writes, or if the
                                                  registry and the batch files do not fit together
        python3 -m batch.claims headline RUN_DIR   print the headline table from the records of one run
                                                  directory (for example results/smoke), and fail if
                                                  it is not the one in GUIDE.md
        python3 -m batch.claims adopt RUN_DIR ...  copy the records of finished runs (results/<batch>)
                                                  into data/records/<batch>

What is read:  data/claims/claims.toml (the claims and the tasks that compute them), data/batches/*.toml (which
tasks exist; the Macaulay2 runner expands them, so Macaulay2 is needed), data/records/<batch>/results.jsonl
(what was computed here).  A task without a record reads "not re-run".  A record of a task that has
changed since (another surface, another predicted value) reads "stale" and supports nothing.

`adopt` is adopt.py beside this file, which says what it copies and what it refuses.
"""

from __future__ import annotations

import fnmatch
import functools
import json
import re
import sys
import tomllib
from collections import Counter
from collections.abc import Mapping, Sequence
from pathlib import Path
from typing import Any, TypedDict

from ..records import ResultStore
from ..runner import DEFAULT_RUNNER, REPOSITORY, expand
from ..tasks import TASK_LABELS, load_config
from . import adopt

REGISTRY = REPOSITORY / "data" / "claims" / "claims.toml"
RECORDS = REPOSITORY / "data" / "records"
DETAIL = REPOSITORY / "data" / "claims" / "RECORDS.md"
HEADLINE_BATCH = "invariants"  # the batch `make smoke` runs; the headline table names tasks of it
NOT_RERUN = "not re-run"
STALE = "stale"
STATUSES = [
    "ok", "mismatch", "unsupported", "timeout", "memory", "blocked", "error", "crashed", STALE, NOT_RERUN,
]  # fmt: skip

Record = dict[str, Any]  # a record of the scheduler, with the name of its run directory under "batch"


class RegistryError(ValueError):
    """The registry, the batch files and the records do not fit together."""


class Listed(TypedDict):
    """One task of the batch files: its id, what the runner computes, and the batches that contain it.

    Two batches can use one id for different computations (each dependent batch has a task
    `quartic_prefix/realize`, each for another object), so a task is its id together with its payload.
    """

    id: str
    payload: dict[str, Any]
    batches: list[str]


# ---------------------------------------------------------------------------------------------------
# reading


def load_registry() -> dict[str, Any]:
    with REGISTRY.open("rb") as handle:
        registry: dict[str, Any] = tomllib.load(handle)
    return registry


def essential(payload: Mapping[str, Any]) -> str:
    """What a task computes and compares, without its place in a batch (id, set, group, cost)."""
    kept = {key: value for key, value in payload.items() if key not in TASK_LABELS and value is not None}
    return json.dumps(kept, sort_keys=True)


def answers(record: Mapping[str, Any], payload: Mapping[str, Any]) -> bool:
    """Whether a record was computed for the task as it is now.

    This asks less than the scheduler does before it reuses a record: the scheduler also wants the code
    unchanged.  A committed record stays the record of its task when the code moves on; it names the
    commit that computed it.
    """
    task = record.get("task")
    return isinstance(task, dict) and essential(task) == essential(payload)


def list_tasks(expansions: Mapping[str, Sequence[Mapping[str, Any]]]) -> list[Listed]:
    """The tasks of every batch, from the expansion of each: one entry per id and computation."""
    tasks: dict[tuple[str, str], Listed] = {}
    for batch in sorted(expansions):
        for payload in expansions[batch]:
            key = (str(payload["id"]), essential(payload))
            listed = tasks.setdefault(key, {"id": key[0], "payload": dict(payload), "batches": []})
            listed["batches"].append(batch)
    return list(tasks.values())


@functools.cache
def batch_tasks() -> list[Listed]:
    """Every task of every batch file, as the Macaulay2 runner expands it."""
    expansions = {}
    for path in sorted((REPOSITORY / "data" / "batches").glob("*.toml")):
        expanded, _ = expand(DEFAULT_RUNNER, load_config(path).description)
        expansions[path.stem] = [task.payload for task in expanded]
    return list_tasks(expansions)


def run_records(run_dirs: Sequence[Path]) -> dict[str, list[Record]]:
    """The latest record of each task in each run directory, by task id."""
    found: dict[str, list[Record]] = {}
    for run_dir in run_dirs:
        for task_id, record in ResultStore(run_dir / adopt.RESULTS).latest().items():
            found.setdefault(task_id, []).append(dict(record) | {"batch": run_dir.name})
    return found


def committed_records(root: Path = RECORDS) -> dict[str, list[Record]]:
    if not root.is_dir():
        return {}
    return run_records(sorted(path for path in root.iterdir() if (path / adopt.RESULTS).is_file()))


def standing(task: Listed, records: Mapping[str, Sequence[Record]]) -> tuple[str, Record | None]:
    """Where a task stands in the tables, and the record that says so.

    The latest record computed for the task as it is now gives its status.  Without one, a record of
    its id in one of its batches was computed for the task as it was earlier: stale.
    """

    def latest(found: Sequence[Record]) -> Record:
        return max(found, key=lambda record: str(record.get("started_at", "")))

    candidates = records.get(task["id"], [])
    answering = [record for record in candidates if answers(record, task["payload"])]
    if answering:
        record = latest(answering)
        return str(record["status"]), record
    earlier = [record for record in candidates if record["batch"] in task["batches"]]
    if earlier:
        return STALE, latest(earlier)
    return NOT_RERUN, None


def _natural(text: str) -> list[Any]:
    return [int(part) if part.isdigit() else part for part in re.split(r"(\d+)", text)]


def counts_for_claim(task: Listed) -> bool:
    """Whether a task can support a claim."""
    return task["payload"].get("kind") != "synthetic" and not task["id"].endswith("!control")


def claim_tasks(claim: Mapping[str, Any], tasks: Sequence[Listed]) -> list[Listed]:
    """The tasks of a claim: those an id pattern takes, in the batches the claim names if it names any."""
    batches = claim.get("batches")
    chosen = [
        task
        for task in tasks
        if counts_for_claim(task)
        and any(fnmatch.fnmatchcase(task["id"], pattern) for pattern in claim["tasks"])
        and (batches is None or set(batches) & set(task["batches"]))
    ]
    return sorted(chosen, key=lambda task: (_natural(task["id"]), task["batches"]))


def validate(registry: Mapping[str, Any], tasks: Sequence[Listed]) -> None:
    problems = []
    ids = [claim["id"] for claim in registry["claim"]]
    problems += [f"two claims have the id {i}" for i in sorted({i for i in ids if ids.count(i) > 1})]
    known_batches = {batch for task in tasks for batch in task["batches"]}
    claimed: set[tuple[str, str]] = set()
    for claim in registry["claim"]:
        table = registry["table"].get(claim["table"])
        if table is None:
            problems.append(f"{claim['id']}: no table {claim['table']!r}")
        elif len(claim["cells"]) != len(table["columns"]):
            problems.append(f"{claim['id']}: {len(claim['cells'])} cells for {len(table['columns'])} columns")
        if bool(claim["tasks"]) == ("no_task" in claim):
            problems.append(f"{claim['id']}: a claim has either tasks or a reason under no_task")
        for batch in claim.get("batches", []):
            if batch not in known_batches:
                problems.append(f"{claim['id']}: no batch file {batch!r}")
        for pattern in claim["tasks"]:
            if re.search(r"\d\*", pattern):
                problems.append(
                    f"{claim['id']}: in {pattern!r} the * follows a digit and also matches longer numbers"
                )
            if not claim_tasks(claim | {"tasks": [pattern]}, tasks):
                problems.append(f"{claim['id']}: no task of its batches matches {pattern!r}")
        claimed.update((task["id"], essential(task["payload"])) for task in claim_tasks(claim, tasks))
    for task in tasks:
        if counts_for_claim(task) and (task["id"], essential(task["payload"])) not in claimed:
            problems.append(f"the task {task['id']} ({', '.join(task['batches'])}) belongs to no claim")
    for row in registry["headline"]:
        if len(headline_tasks(row, tasks)) != 1:
            problems.append(f"headline: {row['task']} is not one task of data/batches/{HEADLINE_BATCH}.toml")
    if problems:
        raise RegistryError("\n".join(problems))


def headline_tasks(row: Mapping[str, Any], tasks: Sequence[Listed]) -> list[Listed]:
    return [task for task in tasks if task["id"] == row["task"] and HEADLINE_BATCH in task["batches"]]


# ---------------------------------------------------------------------------------------------------
# writing


def cell(value: Any, limit: int = 160) -> str:
    """A value as it appears in a table cell."""
    if value is None:
        text = ""
    elif isinstance(value, bool):
        text = "yes" if value else "no"
    elif isinstance(value, dict):
        text = ", ".join(f"{key} {cell(item, 10**9)}" for key, item in value.items())
    elif isinstance(value, list):
        text = "(" + ", ".join(cell(item, 10**9) for item in value) + ")"
    elif isinstance(value, int):
        text = f"{value:,}"
    else:
        text = str(value)
    text = text.replace("|", "\\|")
    return text if len(text) <= limit else text[: limit - 1] + "…"


def table(header: list[str], rows: list[list[str]]) -> list[str]:
    return [
        "| " + " | ".join(header) + " |",
        "|" + "---|" * len(header),
        *("| " + " | ".join(row) + " |" for row in rows),
    ]


def anchor(claim_id: str) -> str:
    return "claim-" + re.sub(r"[^a-z0-9]+", "-", claim_id.lower()).strip("-")


def commit_of(record: Mapping[str, Any]) -> str:
    return str((record.get("code") or {}).get("commit") or "unknown commit")


def stamp(records: Sequence[Mapping[str, Any]]) -> str:
    """When and from which commits a set of records comes."""
    days = sorted({str(record["started_at"])[:10] for record in records})
    commits = sorted({commit_of(record) for record in records})
    when = days[0] if len(days) == 1 else f"{days[0]} to {days[-1]}"
    return f"{when}, " + ", ".join(f"`{commit[:7]}`" for commit in commits)


def summary(
    claim: Mapping[str, Any], tasks: Sequence[Listed], records: Mapping[str, Sequence[Record]]
) -> str:
    """The last cell of a claim's row: what the scheduler's records say about it."""
    chosen = claim_tasks(claim, tasks)
    if not chosen:
        return f"no task: {claim['no_task']}"
    found = [standing(task, records) for task in chosen]
    counts = Counter(status for status, _ in found)
    recorded = [record for status, record in found if record is not None and status != STALE]
    link = f"[tasks](data/claims/RECORDS.md#{anchor(claim['id'])})"
    if counts[NOT_RERUN] == len(chosen):
        named = claim.get("batches")
        batches = sorted(
            {batch for task in chosen for batch in task["batches"] if named is None or batch in named}
        )
        where = ", ".join(f"`{batch}`" for batch in batches)
        return f"**{NOT_RERUN}**: {len(chosen)} {_plural(len(chosen), 'task')} in {where}, no record; {link}"
    parts = [f"{status} {counts[status]}" for status in STATUSES if counts[status]]
    if counts["ok"] == len(chosen):
        lead = f"all {len(chosen)} tasks **ok**" if len(chosen) > 1 else "its task is **ok**"
    else:
        lead = "tasks: " + "; ".join(parts) + f" (of {len(chosen)})"
    when = f"{stamp(recorded)}; " if recorded else ""
    return f"{lead}; {when}{link}"


def _plural(count: int, word: str) -> str:
    return word if count == 1 else word + "s"


def claims_table(
    slug: str, registry: Mapping[str, Any], tasks: Sequence[Listed], records: Mapping[str, Sequence[Record]]
) -> list[str]:
    spec = registry["table"][slug]
    rows = [
        [*claim["cells"], summary(claim, tasks, records)]
        for claim in registry["claim"]
        if claim["table"] == slug
    ]
    return table([*spec["columns"], "Run under the scheduler"], rows)


def detail(
    registry: Mapping[str, Any], tasks: Sequence[Listed], records: Mapping[str, Sequence[Record]]
) -> str:
    """data/claims/RECORDS.md: every claim with its tasks, one row per task."""
    lines = [
        "# Tasks and records, claim by claim",
        "",
        "Generated by `make tables`; do not edit. For every claim of [CLAIMS.md](../../CLAIMS.md) that has "
        "tasks: each task with the batches that contain it, its predicted value, and the latest record of the task "
        f'in [data/records/](../records/), if there is one. A task without a record reads "{NOT_RERUN}": nothing in this '
        f'repository then says what it computes to. A record reads "{STALE}" when its task has changed since it was '
        "computed (another surface, another object, another predicted value): it supports nothing until the task is "
        "run again.",
        "",
        'A predicted value comes from the package or, for the realized twists, from the batch file. "Computed" is '
        "what the task found; the status is `ok` when the two agree, or when nothing is predicted and the task gave a "
        "value. A record names the day it was computed, the commit of the code and the wall time. Tasks of the "
        "dependent batches share ids: the Batches column says which computation a row is.",
        "",
    ]
    for claim in registry["claim"]:
        chosen = claim_tasks(claim, tasks)
        if not chosen:
            continue
        lines += [f'<a name="{anchor(claim["id"])}"></a>', "", f"## {claim['id']}", "", claim["cells"][0], ""]
        rows = []
        for task in chosen:
            status, record = standing(task, records)
            if record is None:
                state, computed = NOT_RERUN, ""
            else:
                day, commit = str(record["started_at"])[:10], commit_of(record)[:7]
                if status == STALE:
                    state, computed = f"{STALE}: recorded {day} at `{commit}` for the task as it was then", ""
                else:
                    state = f"{status}, {day}, `{commit}`, {record['wall_seconds']:g} s"
                    computed = cell(record.get("value"))
            rows.append([
                f"`{task['id']}`", ", ".join(task["batches"]), cell(task["payload"].get("predicted")), state, computed,
            ])  # fmt: skip
        lines += table(["Task", "Batches", "Predicted", "Record", "Computed"], rows)
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def headline(
    registry: Mapping[str, Any], tasks: Sequence[Listed], records: Mapping[str, Sequence[Record]]
) -> list[str]:
    rows = []
    for row in registry["headline"]:
        (task,) = headline_tasks(row, tasks)
        status, record = standing(task, records)
        rows.append([
            row["label"], cell(task["payload"].get("predicted")),
            "" if record is None or status == STALE else cell(record.get("value")),
            status, f"`{row['task']}`",
        ])  # fmt: skip
    return table(["Quantity", "Predicted", "Computed", "Status", "Task"], rows)


def blocks(
    registry: Mapping[str, Any], tasks: Sequence[Listed], records: Mapping[str, Sequence[Record]]
) -> dict[Path, dict[str, list[str]]]:
    """The generated parts of the hand-written files, by file and name."""
    return {
        REPOSITORY / "CLAIMS.md": {
            slug: claims_table(slug, registry, tasks, records) for slug in registry["table"]
        },
        REPOSITORY / "GUIDE.md": {"headline": headline(registry, tasks, records)},
    }


def splice(text: str, name: str, lines: list[str], path: Path) -> str:
    begin, end = (
        f"<!-- BEGIN GENERATED {name}: make tables -->",
        f"<!-- END GENERATED {name} -->",
    )
    if text.count(begin) != 1 or text.count(end) != 1:
        raise RegistryError(f"{path.name} needs exactly one pair of markers for the generated part {name!r}")
    head, rest = text.split(begin)
    _, tail = rest.split(end)
    return head + begin + "\n" + "\n".join(lines) + "\n" + end + tail


def outputs() -> dict[Path, str]:
    registry, tasks, records = load_registry(), batch_tasks(), committed_records()
    validate(registry, tasks)
    written = {DETAIL: detail(registry, tasks, records)}
    for path, parts in blocks(registry, tasks, records).items():
        text = path.read_text(encoding="utf-8")
        for name, lines in parts.items():
            text = splice(text, name, lines, path)
        written[path] = text
    return written


# ---------------------------------------------------------------------------------------------------
# commands


def command_tables() -> int:
    for path, text in outputs().items():
        if not path.exists() or path.read_text(encoding="utf-8") != text:
            path.write_text(text, encoding="utf-8")
            print(f"wrote {path.relative_to(REPOSITORY)}")
    return 0


def command_check() -> int:
    stale = [
        path
        for path, text in outputs().items()
        if not path.exists() or path.read_text(encoding="utf-8") != text
    ]
    for path in stale:
        print(
            f"{path.relative_to(REPOSITORY)} is not what the registry and the records give: run `make tables`",
            file=sys.stderr,
        )
    if not stale:
        print("the generated tables agree with the registry, the batch files and the records")
    return 1 if stale else 0


def command_headline(run_dir: Path) -> int:
    registry, tasks = load_registry(), batch_tasks()
    lines = headline(registry, tasks, run_records([run_dir]))
    print("\n".join(lines))
    readme = (REPOSITORY / "GUIDE.md").read_text(encoding="utf-8")
    if splice(readme, "headline", lines, REPOSITORY / "GUIDE.md") != readme:
        print("\nthis is NOT the headline table of GUIDE.md", file=sys.stderr)
        return 1
    print("\nthis is the headline table of GUIDE.md")
    return 0


def command_adopt(run_dirs: list[Path]) -> int:
    for run_dir in run_dirs:
        done = adopt.adopt(run_dir, RECORDS, REPOSITORY)
        print(f"data/records/{run_dir.name}: {len(done.records)} records, {stamp(done.records)}")
        for (old, now), count in sorted(done.moved.items()):
            print(f"   {count} records: commit {old[:7]} is {now[:7]} in the present history (same tree)")
    return 0


def main(arguments: list[str]) -> int:
    try:
        if arguments == ["tables"]:
            return command_tables()
        if arguments == ["check"]:
            return command_check()
        if len(arguments) == 2 and arguments[0] == "headline":
            return command_headline(Path(arguments[1]))
        if len(arguments) >= 2 and arguments[0] == "adopt":
            return command_adopt([Path(argument) for argument in arguments[1:]])
    except (RegistryError, ValueError, OSError, RuntimeError) as problem:
        print(f"batch.claims: {problem}", file=sys.stderr)
        return 1
    print((__doc__ or "").split("\n\n")[1], file=sys.stderr)
    return 2
