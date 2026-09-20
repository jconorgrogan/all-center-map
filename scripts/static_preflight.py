#!/usr/bin/env python3
"""Fast local checks before running Palomar's authoritative verifier.

This script intentionally checks only repository properties visible without
executing untrusted project code.  A pass is necessary, not sufficient: the
official Comparator/NanoDa/Landrun and metadata validators remain controlling.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from pathlib import Path


SHA40 = re.compile(r"^[0-9a-f]{40}$")
GITHUB = re.compile(
    r"^https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?$"
)
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*$")
COMPILED_SUFFIXES = {
    ".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj",
    ".so", ".trace",
}
ALLOWED_AX = {"propext", "Quot.sound", "Classical.choice"}
COMPARATOR_KEYS = {
    "challenge_module", "solution_module", "theorem_names",
    "definition_names", "permitted_axioms", "enable_nanoda",
}


class Audit:
    def __init__(self) -> None:
        self.errors: list[str] = []
        self.warnings: list[str] = []

    def require(self, condition: bool, message: str) -> None:
        if not condition:
            self.errors.append(message)

    def warn(self, condition: bool, message: str) -> None:
        if not condition:
            self.warnings.append(message)


def regular_file(audit: Audit, path: Path) -> None:
    audit.require(path.is_file() and not path.is_symlink(),
                  f"required regular file missing: {path.name}")


def walk_source(root: Path):
    for base, dirs, files in os.walk(root, followlinks=False):
        base_path = Path(base)
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        for name in files:
            yield base_path / name


def check_tree(audit: Audit, root: Path) -> None:
    total = 0
    for path in walk_source(root):
        try:
            if path.is_symlink():
                audit.errors.append(f"symbolic link is not submission-safe: {path.relative_to(root)}")
                continue
            total += path.stat().st_size
            if path.suffix.lower() in COMPILED_SUFFIXES:
                audit.errors.append(f"compiled artifact committed: {path.relative_to(root)}")
            if path.stat().st_size >= 120:
                with path.open("rb") as handle:
                    first = handle.read(120)
                if first.startswith(b"version https://git-lfs.github.com/spec/v1"):
                    audit.errors.append(f"Git LFS pointer present: {path.relative_to(root)}")
        except OSError as exc:
            audit.errors.append(f"cannot inspect {path}: {exc}")
    audit.require(total <= 500 * 1024 * 1024,
                  f"repository source size {total} exceeds 500 MiB")
    audit.require(not (root / ".gitmodules").exists(), "Git submodules are not allowed")


def check_lake(audit: Audit, root: Path) -> None:
    lakefiles = [p for p in (root / "lakefile.toml", root / "lakefile.lean") if p.exists()]
    audit.require(len(lakefiles) == 1, "root must contain exactly one Lakefile")
    if lakefiles:
        regular_file(audit, lakefiles[0])
        audit.require(lakefiles[0].stat().st_size <= 1024 * 1024,
                      "Lakefile exceeds 1 MiB")
    for name in ["lean-toolchain", "lake-manifest.json"]:
        regular_file(audit, root / name)
    toolchain = root / "lean-toolchain"
    if toolchain.is_file():
        value = toolchain.read_text(encoding="utf-8").strip()
        audit.require(bool(re.fullmatch(r"leanprover/lean4:v\d+\.\d+\.\d+(?:-rc\d+)?", value)),
                      f"toolchain is not a released or RC Lean version: {value!r}")
    manifest = root / "lake-manifest.json"
    if manifest.is_file():
        try:
            data = json.loads(manifest.read_text(encoding="utf-8"))
            packages = data.get("packages")
            audit.require(isinstance(packages, list), "manifest packages must be an array")
            if isinstance(packages, list):
                for package in packages:
                    if package.get("type") != "git":
                        audit.errors.append(
                            f"manifest package {package.get('name')!r} is not a Git dependency"
                        )
                        continue
                    url, rev = package.get("url", ""), package.get("rev", "")
                    audit.require(bool(GITHUB.fullmatch(url)),
                                  f"non-public/noncanonical GitHub URL: {url!r}")
                    audit.require(bool(SHA40.fullmatch(rev)),
                                  f"dependency {package.get('name')!r} lacks full lowercase SHA: {rev!r}")
        except (OSError, json.JSONDecodeError) as exc:
            audit.errors.append(f"invalid lake-manifest.json: {exc}")


def check_challenge(audit: Audit, root: Path) -> None:
    challenge = root / "Challenge.lean"
    solution = root / "Solution.lean"
    regular_file(audit, challenge)
    regular_file(audit, solution)
    if challenge.is_file():
        size = challenge.stat().st_size
        lines = challenge.read_text(encoding="utf-8").count("\n") + 1
        audit.require(size <= 100 * 1024, f"Challenge is {size} bytes, over 100 KiB")
        audit.require(lines <= 1000, f"Challenge is {lines} lines, over 1,000")
        audit.warn(size <= 32 * 1024, f"Challenge is {size} bytes, over 32 KiB warning threshold")
        audit.warn(lines <= 300, f"Challenge is {lines} lines, over 300-line warning threshold")


def nonempty_strings(value) -> bool:
    return isinstance(value, list) and bool(value) and all(isinstance(x, str) and x for x in value)


def check_comparator(audit: Audit, root: Path) -> None:
    path = root / "comparator.json"
    regular_file(audit, path)
    if not path.is_file():
        return
    audit.require(path.stat().st_size <= 1024 * 1024, "comparator.json exceeds 1 MiB")
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        audit.errors.append(f"invalid comparator.json: {exc}")
        return
    audit.require(isinstance(data, dict), "comparator.json must contain one object")
    if not isinstance(data, dict):
        return
    audit.require(not (set(data) - COMPARATOR_KEYS),
                  f"unknown Comparator keys: {sorted(set(data) - COMPARATOR_KEYS)}")
    for key in ["challenge_module", "solution_module"]:
        audit.require(isinstance(data.get(key), str) and bool(MODULE.fullmatch(data.get(key, ""))),
                      f"invalid {key}")
    audit.require(data.get("challenge_module") != data.get("solution_module"),
                  "Challenge and Solution modules must be distinct")
    audit.require(nonempty_strings(data.get("theorem_names")),
                  "theorem_names must be a nonempty array of nonempty strings")
    definitions = data.get("definition_names", [])
    audit.require(isinstance(definitions, list) and all(isinstance(x, str) and x for x in definitions),
                  "definition_names must be an array of nonempty strings")
    axioms = data.get("permitted_axioms")
    audit.require(isinstance(axioms, list) and set(axioms) <= ALLOWED_AX,
                  f"permitted_axioms must be a subset of {sorted(ALLOWED_AX)}")
    audit.warn(data.get("enable_nanoda", True) is True,
               "enable_nanoda is false; Palomar overrides it, but the local config should be honest")


def check_metadata(audit: Audit, root: Path, allow_template: bool) -> None:
    for name in ["formalization.yaml", "README.md", "LICENSE"]:
        regular_file(audit, root / name)
    meta = root / "formalization.yaml"
    if meta.is_file() and not allow_template:
        text = meta.read_text(encoding="utf-8")
        audit.require("TEMPLATE:" not in text, "formalization.yaml still contains TEMPLATE sentinels")
        audit.require('version: "v0.4"' in text or "version: v0.4" in text,
                      "formalization.yaml must use v0.4")
    licence_candidates = [
        p for p in root.iterdir() if p.is_file() and
        re.fullmatch(r"(?i)(license|licence|copying|unlicense|ofl)(\.(md|markdown|txt))?", p.name)
    ]
    audit.require(len(licence_candidates) == 1,
                  f"expected exactly one conventional licence file, found {len(licence_candidates)}")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("root", type=Path)
    parser.add_argument("--allow-template", action="store_true",
                        help="permit TEMPLATE metadata only when testing the official starter")
    args = parser.parse_args()
    root = args.root.resolve()
    audit = Audit()
    audit.require(root.is_dir(), f"not a directory: {root}")
    if root.is_dir():
        check_tree(audit, root)
        check_lake(audit, root)
        check_challenge(audit, root)
        check_comparator(audit, root)
        check_metadata(audit, root, args.allow_template)
    for message in audit.warnings:
        print(f"WARNING: {message}")
    for message in audit.errors:
        print(f"ERROR: {message}")
    if audit.errors:
        print(f"FAIL: {len(audit.errors)} error(s), {len(audit.warnings)} warning(s)")
        return 1
    print(f"PASS: static preflight ({len(audit.warnings)} warning(s)); run official full verifier next")
    return 0


if __name__ == "__main__":
    sys.exit(main())
