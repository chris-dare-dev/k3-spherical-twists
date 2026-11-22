"""Capture the repository implementation used for one batch."""

from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import tempfile
from collections.abc import Iterator
from contextlib import contextmanager
from dataclasses import dataclass
from functools import partial
from pathlib import Path
from typing import Any

from .execution import LocalBackend
from .identity import file_digest, implementation_files
from .model import Task
from .runner import RUNNER_SCRIPT, RunnerError, bundled_script, code_version, expand


@dataclass(frozen=True)
class SourceSnapshot:
    root: Path
    command: tuple[str, ...]
    files: dict[str, dict[str, Path]]
    code: dict[str, Any]

    @property
    def watchdog(self) -> Path:
        return self.root / "src" / "k3batch" / "_job.py"

    def expand(self, description: dict[str, Any], backend: LocalBackend) -> tuple[list[Task], dict[str, Any]]:
        return expand(
            self.command,
            description,
            repository=self.root,
            execute=partial(backend.execute, cwd=self.root, watchdog=self.watchdog),
            scratch_root=backend.workspace,
        )


@contextmanager
def source_snapshot(runner: tuple[str, ...], repository: Path) -> Iterator[SourceSnapshot]:
    """Stage a private copy before any subprocess can use the repository code."""
    with tempfile.TemporaryDirectory(prefix="k3batch-source-") as folder:
        root = Path(folder)
        code = code_version(repository)
        launcher, originals = implementation_files(runner, repository)
        bundled = bundled_script(runner, repository) is not None
        copies: dict[Path, Path] = {}
        for paths in originals.values():
            for path in paths.values():
                local = Path(os.path.abspath(path))
                if local in copies or not local.is_relative_to(repository):
                    continue
                target = root / local.relative_to(repository)
                target.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(local, target)
                target.chmod(target.stat().st_mode & ~0o222)
                copies[local] = target

        if (
            implementation_files(runner, repository) != (launcher, originals)
            or (bundled_script(runner, repository) is not None) != bundled
            or any(file_digest(path) != file_digest(copy) for path, copy in copies.items())
            or code_version(repository) != code
        ):
            raise RunnerError("repository source changed during snapshot capture; start the run again")

        if code["dirty"] is False and not _matches_commit(repository, code["commit"], copies):
            code["dirty"] = True

        files = {
            kind: {key: copies.get(Path(os.path.abspath(path)), path) for key, path in paths.items()}
            for kind, paths in originals.items()
        }
        runtime = files["runner_files"]
        command = (
            str(copies.get(launcher, launcher)),
            *(str(runtime.get(str(repository / arg), arg)) for arg in runner[1:]),
        )
        if bundled:
            command = (*command[:-1], str(root / RUNNER_SCRIPT))
        yield SourceSnapshot(root, command, files, code)


def _matches_commit(repository: Path, commit: str, copies: dict[Path, Path]) -> bool:
    """Check clean provenance against immutable Git blobs, even if the live checkout moved."""
    try:
        tree = subprocess.check_output(["git", "-C", str(repository), "ls-tree", "-rz", commit], timeout=30)
    except (subprocess.CalledProcessError, subprocess.TimeoutExpired) as problem:
        raise RunnerError(f"cannot verify the snapshot against commit {commit}") from problem
    blobs = {}
    for entry in tree.split(b"\0")[:-1]:
        info, name = entry.split(b"\t", 1)
        blobs[name] = info.split()[-1].decode()
    algorithm = "sha256" if len(commit) == 64 else "sha1"
    for path, copy in copies.items():
        content = copy.read_bytes()
        digest = hashlib.new(algorithm, f"blob {len(content)}\0".encode(), usedforsecurity=False)
        digest.update(content)
        if digest.hexdigest() != blobs.get(os.fsencode(path.relative_to(repository))):
            return False
    return True
