"""Verify a kernel-bounded Linux filesystem for the transient run workspace."""

from __future__ import annotations

import os
import re
from pathlib import Path

_ESCAPE = re.compile(r"\\([0-7]{3})")


def tmpfs_capacity(root: Path) -> int:
    root = root.resolve(strict=True)
    if not root.is_dir():
        raise ValueError("scratch root must be a directory")
    covering = []
    for record in Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines():
        fields, details = record.split(" - ", 1)
        columns = fields.split()
        mount = Path(_ESCAPE.sub(lambda m: chr(int(m[1], 8)), columns[4]))
        if root.is_relative_to(mount):
            covering.append((len(mount.parts), int(columns[0]), details.split()[0]))
    if not covering or max(covering)[2] != "tmpfs":
        raise ValueError("enforced scratch capacity requires a size-limited tmpfs mount")
    stat = os.statvfs(root)
    capacity = stat.f_frsize * stat.f_blocks
    if capacity <= 0:
        raise ValueError("scratch mount has no verifiable positive capacity")
    return capacity
