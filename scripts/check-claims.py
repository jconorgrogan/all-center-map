#!/usr/bin/env python3
"""Keep public claims narrow and, in verified mode, tie them to checker logs."""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
TARGET = "AllCenterMAP.map_two_fifteenths"
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}
OUT_OF_SCOPE = [
    "AllCenterMAP.prime_pair",
    "AllCenterMAP.q4",
    "AllCenterMAP.density_one",
    "AllCenterMAP.goldbach",
    "AllCenterMAP.decoder",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--verified", action="store_true")
    parser.add_argument("--axiom-log", type=Path)
    parser.add_argument("--comparator-log", type=Path)
    args = parser.parse_args()
    errors: list[str] = []

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    metadata = (ROOT / "formalization.yaml").read_text(encoding="utf-8")
    readme = (ROOT / "README.md").read_text(encoding="utf-8")
    alignment = (ROOT / "MANUSCRIPT_ALIGNMENT.md").read_text(encoding="utf-8")

    if config.get("theorem_names") != [TARGET]:
        errors.append(f"Comparator must advertise exactly {TARGET}")
    for document, text in [
        ("README.md", readme),
        ("formalization.yaml", metadata),
        ("MANUSCRIPT_ALIGNMENT.md", alignment),
    ]:
        if TARGET not in text:
            errors.append(f"{document} does not name the sole release theorem {TARGET}")
        for declaration in OUT_OF_SCOPE:
            if declaration in text:
                errors.append(f"{document} advertises out-of-scope declaration {declaration}")
    if "Theorem 1.1" not in metadata or "Theorem 1.1" not in alignment:
        errors.append("metadata/manuscript alignment does not identify Theorem 1.1")
    aligned = re.findall(r'^\s*lean:\s*"([^"]+)"\s*$', metadata, re.MULTILINE)
    if aligned != [TARGET]:
        errors.append(f"metadata alignment must contain exactly [{TARGET!r}], found {aligned}")

    if args.verified:
        if not args.axiom_log or not args.comparator_log:
            errors.append("verified claim check requires axiom and Comparator logs")
        else:
            try:
                axiom_text = args.axiom_log.read_text(encoding="utf-8")
                comparator_text = args.comparator_log.read_text(encoding="utf-8")
            except OSError as exc:
                errors.append(f"cannot read verification evidence: {exc}")
            else:
                if TARGET not in axiom_text:
                    errors.append("axiom log does not identify the release theorem")
                if "sorryAx" in axiom_text or "Lean.ofReduceBool" in axiom_text:
                    errors.append("axiom log contains a forbidden dependency")
                bracketed = re.findall(r"\[([^\]]*)\]", axiom_text)
                if not bracketed:
                    errors.append("axiom log has no parseable dependency list")
                else:
                    reported = {
                        item.strip()
                        for item in bracketed[-1].split(",")
                        if item.strip()
                    }
                    if reported - ALLOWED:
                        errors.append(
                            f"axiom log contains non-Palomar dependencies: {sorted(reported - ALLOWED)}"
                        )
                comparator_lines = set(comparator_text.splitlines())
                if "Your solution is okay!" not in comparator_lines:
                    errors.append("Comparator success marker is absent")
                for marker in ["nanoda kernel accepts the solution", "con-ron kernel accepts the solution",
                               "Lean default kernel accepts the solution"]:
                    if marker not in comparator_lines:
                        errors.append(f"independent-checker log is missing: {marker}")

    if errors:
        for error in errors:
            print(f"CLAIM ERROR: {error}")
        return 1
    mode = "verified" if args.verified else "structural"
    print(f"CLAIM CHECK PASS ({mode}): one MAP theorem, aligned with Theorem 1.1")
    return 0


if __name__ == "__main__":
    sys.exit(main())
