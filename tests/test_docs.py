"""What the README and the guide name exists: make targets, files and folders, Macaulay2 functions."""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import unittest
from pathlib import Path

REPOSITORY = Path(__file__).resolve().parents[1]
DOCUMENTS = ("README.md", "GUIDE.md")
# folders git does not hold: hidden ones but .github/, caches, and results/, where runs write
UNTRACKED = re.compile(r"\.(?!github$).*|__pycache__|results")

FENCE = re.compile(r"^```(\w*)\n(.*?)^```", re.M | re.S)
SPAN = re.compile(r"`([^`\n]+)`")
LINK = re.compile(r"\]\(([^)\s]+)\)")
MAKE = re.compile(r"\bmake +([a-z][a-z0-9-]*)")
RULE = re.compile(r"^([^\s#.=:][^#=:]*):(?!=)", re.M)
# a path from the root, which ends where a placeholder such as <batch> begins
ROOTED = re.compile(r"(?<![\w/.$-])(?:data|src|tests)/[\w./-]*")
# a file or folder named without the folders above it, such as quartic-sample.toml or scripts/
NAMED = re.compile(r"[\w.-]+(?:/[\w.-]+)*(?:\.(?:toml|m2|py|md|lean)|/)")
# in a Macaulay2 example every name it does not assign is defined; strings and comments are not code
M2_STRING = re.compile(r'"(?:[^"\\]|\\.)*"')
M2_COMMENT = re.compile(r"--.*$|-\*.*?\*-", re.M | re.S)
M2_NAME = re.compile(r"(?<![\w'])[A-Za-z][A-Za-z0-9']*")
M2_ASSIGNED = re.compile(r"^\s*([A-Za-z][A-Za-z0-9']*)\s*:?=(?!=)", re.M)
# in a span of the text, a function is written in camel case (k3Surface), an option before =>
FUNCTION = re.compile(r"\b[a-z][a-z0-9]*[A-Z][A-Za-z0-9]*\b")
OPTION = re.compile(r"\b([A-Za-z][A-Za-z0-9]*) =>")


class Document:
    """The code of one document: its spans, its shell and Macaulay2 blocks, and its links."""

    def __init__(self, name: str) -> None:
        self.name = name
        text = (REPOSITORY / name).read_text(encoding="utf-8")
        blocks = FENCE.findall(text)
        prose = FENCE.sub("", text)
        self.spans = SPAN.findall(prose)
        self.shell = [re.sub(r"(^|\s)#.*$", "", body, flags=re.M) for kind, body in blocks if kind == "bash"]
        self.macaulay2 = [body for kind, body in blocks if kind in {"m2", "macaulay2"}]
        self.links = [link for link in LINK.findall(prose) if not re.match(r"[a-z]+:|#", link)]

    def make_targets(self) -> set[str]:
        return {target for code in self.spans + self.shell for target in MAKE.findall(code)}

    def rooted_paths(self) -> set[str]:
        return {path for code in self.spans + self.shell + self.links for path in ROOTED.findall(code)}

    def named_paths(self) -> set[str]:
        return {
            span
            for span in self.spans
            if NAMED.fullmatch(span)
            and not ROOTED.fullmatch(span)
            and not UNTRACKED.fullmatch(span.split("/")[0])
        }

    def macaulay2_names(self) -> set[str]:
        names: set[str] = set()
        for body in self.macaulay2:
            code = M2_STRING.sub('""', M2_COMMENT.sub("", body))
            names |= set(M2_NAME.findall(code)) - set(M2_ASSIGNED.findall(code))
        for span in self.spans:
            code = M2_STRING.sub('""', span)
            names |= set(FUNCTION.findall(code)) | set(OPTION.findall(code))
        return names


def checkout() -> list[str]:
    """Every file and folder of the checkout, as a path from the root; a folder ends in a slash."""
    paths = []
    for folder, folders, files in os.walk(REPOSITORY):
        folders[:] = [name for name in folders if not UNTRACKED.fullmatch(name)]
        relative = Path(folder).relative_to(REPOSITORY).as_posix()
        prefix = "" if relative == "." else f"{relative}/"
        paths += [f"{prefix}{name}/" for name in folders] + [f"{prefix}{name}" for name in files]
    return paths


class NamesInTheDocuments(unittest.TestCase):
    """Each test also counts what it found, since a pattern that matched nothing would pass any text."""

    def setUp(self) -> None:
        self.documents = [Document(name) for name in DOCUMENTS]

    def test_every_make_target_they_name_is_in_the_makefile(self) -> None:
        rules = RULE.findall((REPOSITORY / "Makefile").read_text(encoding="utf-8"))
        targets = {target for rule in rules for target in rule.split()}
        named = {(document.name, target) for document in self.documents for target in document.make_targets()}
        self.assertGreater(len(named), 5)
        missing = [
            f"{document}: make {target}" for document, target in sorted(named) if target not in targets
        ]
        self.assertEqual(missing, [])

    def test_every_file_and_folder_they_name_is_in_the_repository(self) -> None:
        paths = checkout()
        missing = []
        found = 0
        for document in self.documents:
            rooted = document.rooted_paths() | {link.partition("#")[0] for link in document.links}
            named = document.named_paths()
            found += len(rooted | named)
            missing += [
                f"{document.name}: {path}" for path in sorted(rooted) if not (REPOSITORY / path).exists()
            ]
            missing += [
                f"{document.name}: {name}"
                for name in sorted(named)
                if not any(path == name or path.endswith(f"/{name}") for path in paths)
            ]
        self.assertGreater(found, 20)
        self.assertEqual(missing, [])

    @unittest.skipUnless(shutil.which("M2"), "Macaulay2 is not installed")
    def test_every_macaulay2_function_they_name_is_defined(self) -> None:
        named = {(document.name, name) for document in self.documents for name in document.macaulay2_names()}
        self.assertGreater(len(named), 20)
        # the guide has the reader load JSON for toJSON and fromJSON
        program = (
            'path = prepend("src/macaulay2/", path); needsPackage "K3Twists"; needsPackage "JSON"; '
            f"scan({{{', '.join(json.dumps(name) for name in sorted({name for _, name in named}))}}}, "
            'name -> if not isGlobalSymbol name then print("undefined: " | name)); exit 0'
        )
        done = subprocess.run(
            ["M2", "-q", "--silent", "--stop", "-e", program],
            capture_output=True,
            text=True,
            cwd=REPOSITORY,
            timeout=300,
        )
        self.assertEqual(done.returncode, 0, done.stdout[-2000:] + done.stderr[-2000:])
        lines = done.stdout.splitlines()
        undefined = {line.removeprefix("undefined: ") for line in lines if line.startswith("undefined: ")}
        missing = [f"{document}: {name}" for document, name in sorted(named) if name in undefined]
        self.assertEqual(missing, [])


if __name__ == "__main__":
    unittest.main()
