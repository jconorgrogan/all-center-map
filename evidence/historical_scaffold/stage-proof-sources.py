#!/usr/bin/env python3
"""Copy the exact transitive local Lean closure from a committed proof tree."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import shutil
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
IMPORT = re.compile(r"^\s*import\s+(.+?)\s*$")
SHA40 = re.compile(r"^[0-9a-f]{40}$")
ENDPOINT_DECL = re.compile(
    r"\btheorem\s+zero_argument_map_two_fifteenths\s*:"
)


def run_git(source: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(source), *args], stderr=subprocess.STDOUT, text=True
    ).strip()


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def local_imports(path: Path) -> list[str]:
    modules: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = IMPORT.match(line)
        if not match:
            continue
        code = match.group(1).split("--", 1)[0]
        modules.extend(code.split())
    return modules


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path, help="committed directory containing Lean modules")
    parser.add_argument("--entry", default="MAPReleaseEndpoint")
    args = parser.parse_args()
    source = args.source.resolve()

    try:
        repository = Path(run_git(source, "rev-parse", "--show-toplevel")).resolve()
        commit = run_git(source, "rev-parse", "HEAD")
        dirty = run_git(source, "status", "--porcelain")
        remote = run_git(source, "remote", "get-url", "origin")
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        print(f"BLOCKED: source is not a readable Git checkout: {exc}", file=sys.stderr)
        return 1
    if dirty:
        print("BLOCKED: source checkout is not clean", file=sys.stderr)
        return 1
    if not SHA40.fullmatch(commit):
        print("BLOCKED: source has no full commit SHA", file=sys.stderr)
        return 1

    entry = source / f"{args.entry.replace('.', '/')}.lean"
    if not entry.is_file():
        print(f"BLOCKED: missing zero-argument endpoint module {entry}", file=sys.stderr)
        return 1
    if not ENDPOINT_DECL.search(entry.read_text(encoding="utf-8")):
        print(
            "BLOCKED: endpoint module lacks theorem zero_argument_map_two_fifteenths",
            file=sys.stderr,
        )
        return 1

    pending = [args.entry]
    seen: set[str] = set()
    files: dict[str, Path] = {}
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        candidate = source / f"{module.replace('.', '/')}.lean"
        if not candidate.is_file():
            continue
        if candidate.is_symlink():
            print(f"BLOCKED: source module is a symlink: {candidate}", file=sys.stderr)
            return 1
        files[module] = candidate
        pending.extend(local_imports(candidate))

    destination = ROOT / "Proof"
    for old in destination.rglob("*.lean"):
        old.unlink()
    records = []
    for module, original in sorted(files.items()):
        relative = Path(*module.split(".")).with_suffix(".lean")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(original, target)
        records.append({"module": module, "path": str(relative), "sha256": digest(target)})

    source_subdir = source.relative_to(repository).as_posix()
    snapshot = {
        "schema_version": 1,
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "source_repository": remote,
        "source_commit": commit,
        "source_subdirectory": source_subdir,
        "entry_module": args.entry,
        "files": records,
    }
    (ROOT / "proof-snapshot.json").write_text(
        json.dumps(snapshot, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"staged {len(records)} Lean modules from {remote}@{commit}")
    return 0


if __name__ == "__main__":
    sys.exit(main())

