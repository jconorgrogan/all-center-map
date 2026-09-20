#!/usr/bin/env python3
"""Check the MAP Palomar release locally, or check its publication prerequisites."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

from lean_source_scan import code_only


ROOT = Path(__file__).resolve().parent.parent
SHA40 = re.compile(r"^[0-9a-f]{40}$")
SHA256 = re.compile(r"^[0-9a-f]{64}$")
GITHUB_REMOTE = re.compile(
    r"^(?:https://github\.com/|git@github\.com:)"
    r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+(?:\.git)?$"
)
BLOCK_MARKER = "MAP_RELEASE_BLOCKED"
TARGET = "AllCenterMAP.map_two_fifteenths"
ENDPOINT = ROOT / "Proof" / "MAPReleaseEndpoint.lean"
SNAPSHOT = ROOT / "proof-snapshot.json"
ALLOWED_AXIOMS = ["propext", "Quot.sound", "Classical.choice"]
OUT_OF_SCOPE = (
    "AllCenterMAP.prime_pair",
    "AllCenterMAP.q4",
    "AllCenterMAP.density_one",
    "AllCenterMAP.goldbach",
    "AllCenterMAP.decoder",
)
SORRY_TOKEN = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
SOLUTION_HOLE = re.compile(
    r"(?i)(?:\b(?:sorry|admit|hole)\b|\b(?:by|exact|apply|refine|simp|aesop)\s*\?)"
)


def read_text(path: Path, errors: list[str], label: str) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as exc:
        errors.append(f"{label} cannot be read: {exc}")
        return None


def load_json(path: Path, errors: list[str], label: str) -> Any | None:
    text = read_text(path, errors, label)
    if text is None:
        return None
    try:
        return json.loads(text)
    except json.JSONDecodeError as exc:
        errors.append(f"{label} is invalid JSON: {exc}")
        return None


def validate_config(config: Any, metadata: str, readme: str, errors: list[str]) -> None:
    if not isinstance(config, dict):
        errors.append("comparator.json must contain an object")
        return
    if config.get("challenge_module") != "Challenge":
        errors.append("Comparator challenge_module must be Challenge")
    if config.get("solution_module") != "Solution":
        errors.append("Comparator solution_module must be Solution")
    if config.get("theorem_names") != [TARGET]:
        errors.append(f"Comparator must select exactly {TARGET}")
    if config.get("definition_names", []) != []:
        errors.append("this theorem-only entry must not advertise definition holes")
    if config.get("permitted_axioms") != ALLOWED_AXIOMS:
        errors.append("Comparator permitted_axioms must be the three Palomar axioms")
    if config.get("enable_nanoda") is not True:
        errors.append("Comparator NanoDa checking must remain enabled")

    for document, text in (("formalization.yaml", metadata), ("README.md", readme)):
        if BLOCK_MARKER in text:
            errors.append(f"{document} contains the explicit release blocker marker")
        for declaration in OUT_OF_SCOPE:
            if declaration in text:
                errors.append(f"{document} advertises out-of-scope declaration {declaration}")
    current_claim_markers = (
        "not a Palomar submission",
        "does not export a zero-argument theorem",
        "no zero-argument proof of this statement exists",
    )
    for marker in current_claim_markers:
        if marker in readme or marker in metadata:
            errors.append(f"release prose still records the active blocker: {marker!r}")
    if "BLOCKED:" in metadata:
        errors.append("formalization.yaml still contains unresolved BLOCKED fields")
    if TARGET not in metadata:
        errors.append("formalization.yaml does not identify the sole release theorem")
    if 'authors: ["Conor Grogan"]' not in metadata:
        errors.append("formalization.yaml does not record the confirmed author")
    if 'responsible_maintainers: ["Conor Grogan"]' not in metadata:
        errors.append("formalization.yaml does not record the confirmed maintainer")
    if 'license: "Apache-2.0"' not in metadata:
        errors.append("formalization.yaml does not record the confirmed license")


def validate_sources(
    challenge: str,
    solution: str,
    endpoint: str | None,
    errors: list[str],
) -> None:
    if BLOCK_MARKER in challenge or BLOCK_MARKER in solution:
        errors.append("Challenge/Solution still contain the explicit missing-endpoint marker")

    challenge = code_only(challenge)
    solution = code_only(solution)
    endpoint = None if endpoint is None else code_only(endpoint)
    sorry_matches = list(SORRY_TOKEN.finditer(challenge))
    if len(sorry_matches) != 1:
        errors.append(
            "Challenge must contain exactly one protocol sorry"
            f" (found {len(sorry_matches)})"
        )
    else:
        theorem = re.search(r"\btheorem\s+map_two_fifteenths\b", challenge)
        if theorem is None or sorry_matches[0].start() < theorem.end():
            errors.append("Challenge's sole sorry is not inside map_two_fifteenths")
    if re.search(r"(?m)^\s*axiom\s+", challenge):
        errors.append("Challenge must not add an axiom beside its protocol sorry")

    solution_holes = list(SOLUTION_HOLE.finditer(solution))
    if solution_holes:
        errors.append("Solution.lean contains a proof-side sorry/hole")

    if endpoint is None:
        errors.append("Proof/MAPReleaseEndpoint.lean is absent")
    else:
        if not re.search(r"\btheorem\s+zero_argument_map_two_fifteenths\s*:", endpoint):
            errors.append(
                "MAPReleaseEndpoint.lean does not declare the required zero-argument theorem"
            )
        if BLOCK_MARKER in endpoint or SOLUTION_HOLE.search(endpoint):
            errors.append("MAPReleaseEndpoint.lean contains a release blocker or proof hole")


def validate_snapshot(data: Any, errors: list[str]) -> None:
    if not isinstance(data, dict):
        errors.append("proof-snapshot.json must contain an object")
        return
    if data.get("schema_version") != 2:
        errors.append("proof-snapshot.json must use schema_version 2")
    if data.get("entry_module") != "MAPReleaseEndpoint":
        errors.append("proof-snapshot.json entry_module must be MAPReleaseEndpoint")
    if data.get("source_kind") != "isolated verified content snapshot":
        errors.append("proof-snapshot.json source_kind is not an isolated verified snapshot")
    # The source is deliberately an isolated snapshot. A made-up source commit
    # or remote would turn this local manifest into false provenance.
    if data.get("source_commit") is not None:
        errors.append("proof-snapshot.json source_commit must remain null for this snapshot")
    if data.get("source_repository") is not None:
        errors.append("proof-snapshot.json source_repository must remain null for this snapshot")

    records = data.get("files")
    if not isinstance(records, list) or not records:
        errors.append("proof-snapshot.json files must be a non-empty array")
        return

    seen: set[str] = set()
    manifest_paths: set[str] = set()
    for index, record in enumerate(records):
        prefix = f"proof-snapshot.json files[{index}]"
        if not isinstance(record, dict):
            errors.append(f"{prefix} must be an object")
            continue
        module = record.get("module")
        relative = record.get("path")
        digest = record.get("sha256")
        byte_count = record.get("bytes")
        if not isinstance(module, str) or not module:
            errors.append(f"{prefix}.module must be a non-empty string")
        if not isinstance(relative, str) or not relative:
            errors.append(f"{prefix}.path must be a non-empty relative path")
            continue
        candidate = Path(relative)
        if (
            candidate.is_absolute()
            or candidate.as_posix() != relative
            or ".." in candidate.parts
            or not relative.startswith("Proof/")
            or candidate.suffix != ".lean"
        ):
            errors.append(f"{prefix}.path is not a safe Proof/*.lean path: {relative!r}")
            continue
        if relative in seen:
            errors.append(f"{prefix}.path is duplicated: {relative}")
            continue
        seen.add(relative)
        manifest_paths.add(relative)
        if isinstance(module, str) and module and module != candidate.relative_to("Proof").with_suffix("").as_posix().replace("/", "."):
            errors.append(f"{prefix}.module does not match its path stem")
        if not isinstance(digest, str) or not SHA256.fullmatch(digest):
            errors.append(f"{prefix}.sha256 must be a lowercase SHA-256 digest")
        if isinstance(byte_count, bool) or not isinstance(byte_count, int) or byte_count < 0:
            errors.append(f"{prefix}.bytes must be a non-negative integer")

        path = ROOT / candidate
        if path.is_symlink() or not path.resolve().is_relative_to((ROOT / "Proof").resolve()):
            errors.append(f"{relative} is not an in-tree regular proof source")
            continue
        try:
            raw = path.read_bytes()
        except OSError as exc:
            errors.append(f"{prefix} target cannot be read: {exc}")
            continue
        if isinstance(byte_count, int) and not isinstance(byte_count, bool) and len(raw) != byte_count:
            errors.append(f"{relative} byte count does not match proof-snapshot.json")
        actual_digest = hashlib.sha256(raw).hexdigest()
        if isinstance(digest, str) and actual_digest != digest:
            errors.append(f"{relative} SHA-256 does not match proof-snapshot.json")

    actual_paths = {
        path.relative_to(ROOT).as_posix() for path in (ROOT / "Proof").rglob("*.lean")
    }
    missing = sorted(actual_paths - manifest_paths)
    untracked = sorted(manifest_paths - actual_paths)
    if missing:
        errors.append(f"proof-snapshot.json omits Proof source(s): {', '.join(missing[:3])}")
        if len(missing) > 3:
            errors.append(f"proof-snapshot.json omits {len(missing) - 3} additional Proof source(s)")
    if untracked:
        errors.append(f"proof-snapshot.json names absent Proof source(s): {', '.join(untracked[:3])}")
        if len(untracked) > 3:
            errors.append(f"proof-snapshot.json names {len(untracked) - 3} additional absent source(s)")


def local_errors() -> list[str]:
    errors: list[str] = []
    challenge = read_text(ROOT / "Challenge.lean", errors, "Challenge.lean")
    solution = read_text(ROOT / "Solution.lean", errors, "Solution.lean")
    metadata = read_text(ROOT / "formalization.yaml", errors, "formalization.yaml")
    readme = read_text(ROOT / "README.md", errors, "README.md")
    endpoint = read_text(ENDPOINT, errors, "Proof/MAPReleaseEndpoint.lean")
    config = load_json(ROOT / "comparator.json", errors, "comparator.json")
    snapshot = load_json(SNAPSHOT, errors, "proof-snapshot.json")

    if challenge is not None and solution is not None and endpoint is not None:
        validate_sources(challenge, solution, endpoint, errors)
    if metadata is not None and readme is not None:
        validate_config(config, metadata, readme, errors)
    if snapshot is not None:
        validate_snapshot(snapshot, errors)
    return errors


def git(*args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(ROOT), *args], stderr=subprocess.DEVNULL, text=True
    ).strip()


def publication_errors() -> list[str]:
    errors: list[str] = []
    try:
        top = Path(git("rev-parse", "--show-toplevel")).resolve()
        if top != ROOT:
            errors.append("release candidate must be the root of its own Git repository")
        head = git("rev-parse", "HEAD")
        if not SHA40.fullmatch(head):
            errors.append("release HEAD is not a full 40-character commit SHA")
        porcelain = git("status", "--porcelain")
        if porcelain:
            preview = ", ".join(line[3:] for line in porcelain.splitlines()[:8])
            errors.append(f"release worktree is not clean ({preview})")
            print(porcelain, file=sys.stderr)
        remote = git("remote", "get-url", "origin")
        if not GITHUB_REMOTE.fullmatch(remote):
            errors.append("origin is not a real GitHub repository URL")
    except (subprocess.CalledProcessError, FileNotFoundError):
        errors.append("release candidate is not a committed Git repository with origin")
    return errors


def report(errors: list[str], label: str) -> int:
    if errors:
        for error in errors:
            print(f"BLOCKED: {error}")
        print(f"{label} BLOCKED ({len(errors)} condition(s))")
        return 1
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--local",
        action="store_true",
        help="validate the isolated release snapshot without requiring Git publication provenance",
    )
    args = parser.parse_args()

    errors = local_errors()
    if args.local:
        if report(errors, "LOCAL CHECK"):
            return 1
        print("LOCAL STRUCTURAL CHECK PASS: snapshot hashes and release shape validated")
        return 0

    errors.extend(publication_errors())
    if report(errors, "PUBLICATION GATE"):
        return 1
    print("PUBLICATION PREREQUISITES PASS: local checks and Git provenance pass")
    return 0


if __name__ == "__main__":
    sys.exit(main())
