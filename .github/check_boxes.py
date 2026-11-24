"""The boxes of src/batch import each other in one direction, and only through their interfaces.

Invariant: a box imports only boxes on lower layers of LAYERS, and only what the box's __init__.py
exports (`from ..records import Record`, never `from ..records.store import Record`). Boxes on one
layer are independent of each other. The watchdog runs as a process of its own and imports nothing
from the package. A new box needs a layer here, with its job beside it.

Usage: python3 .github/check_boxes.py
Standard library only, so CI needs no install. Reads the source; imports nothing from it.
"""

from __future__ import annotations

import ast
import sys
from pathlib import Path

PACKAGE = Path(__file__).resolve().parents[1] / "src" / "batch"

# Lowest first.
LAYERS = (
    {"tasks"},  # the batch file, the tasks it expands to, the limits they run under
    {"jobs", "runner"},  # one process under limits on Linux; the Macaulay2 end and its protocol
    {"records"},  # the record of an attempt, the stores that keep records, artifacts
    {"scheduler", "reports", "claims"},  # running a batch; reading a run; committing records and tables
    {"cli"},  # the command line: cli.py, with __main__.py and __init__.py beside it
)
LAYER = {box: rank for rank, boxes in enumerate(LAYERS) for box in boxes}
STANDALONE = {PACKAGE / "jobs" / "watchdog.py"}


def package_of(path: Path) -> list[str]:
    """The dotted package a file's relative imports start from, as parts."""
    inner = list(path.relative_to(PACKAGE.parent).parts)
    inner[-1] = inner[-1].removesuffix(".py")
    return inner[:-1]


def targets(path: Path) -> list[tuple[int, list[str]]]:
    """Each module of the package that the file imports, as parts, with its line."""
    found = []
    base = package_of(path)
    for node in ast.walk(ast.parse(path.read_text(encoding="utf-8"), str(path))):
        if isinstance(node, ast.ImportFrom):
            if node.level:
                start = base[: len(base) - node.level + 1]
                module = [*start, *(node.module.split(".") if node.module else [])]
            else:
                module = (node.module or "").split(".")
            if module[0] != PACKAGE.name:
                continue
            if node.module is None or len(module) == 1:
                # `from . import x`: each name is a box or a module of this box
                found += [(node.lineno, [*module, alias.name]) for alias in node.names]
            else:
                found.append((node.lineno, module))
        elif isinstance(node, ast.Import):
            found += [
                (node.lineno, a.name.split(".")) for a in node.names if a.name.split(".")[0] == PACKAGE.name
            ]
    return found


def main() -> int:
    problems = []
    for path in sorted(PACKAGE.rglob("*.py")):
        where = path.relative_to(PACKAGE.parents[1])
        own = path.relative_to(PACKAGE).parts[0].removesuffix(".py")
        if own in {"__main__", "__init__"}:
            own = "cli"
        if own not in LAYER:
            problems.append(f"{where}: the box {own!r} has no layer in LAYERS")
            continue
        for line, module in targets(path):
            if path in STANDALONE:
                problems.append(
                    f"{where}:{line}: runs as its own process and may not import {'.'.join(module)}"
                )
                continue
            box = module[1] if len(module) > 1 else None
            if box is None or box == own or box == "__version__":
                continue
            if box not in LAYER:
                problems.append(f"{where}:{line}: imports {'.'.join(module)}, which is not a box")
            elif LAYER[box] >= LAYER[own]:
                problems.append(f"{where}:{line}: {own} may not import {box}: it is not on a lower layer")
            elif len(module) > 2:
                problems.append(
                    f"{where}:{line}: imports {'.'.join(module)}; import from {'.'.join(module[:2])} instead "
                    "(add the name to its __init__.py)"
                )
    if problems:
        print("Imports between the boxes of src/batch that break the layers:")
        print("\n".join(f"  {problem}" for problem in problems))
        return 1
    print("The boxes of src/batch import downward, through their interfaces.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
