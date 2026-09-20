#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
cd "$root"
mkdir -p .cache

if [ "$(uname -s)" != Linux ]; then
  echo "error: authoritative release verification requires Linux/Landlock" >&2
  exit 1
fi

gate_args=()
if [ "${1:-}" = "--local" ] && [ "$#" -eq 1 ]; then
  gate_args=(--local)
elif [ "$#" -ne 0 ]; then
  echo "usage: verify-linux.sh [--local]" >&2
  exit 2
fi
python3 scripts/check-release-gate.py "${gate_args[@]}"
python3 scripts/check-claims.py
python3 scripts/static_preflight.py .
ruby scripts/validate-formalization.rb
./test/landrun_wrapper_test.sh
python3 test/source_scan_test.py

bundle exec licensee detect LICENSE --json --no-packages --no-readme \
  > .cache/license.json
ruby -rjson -e '
  report = JSON.parse(File.read(ARGV.fetch(0)))
  identifiers = report.fetch("licenses").map { |item| item.fetch("spdx_id") }
  abort "LICENSE is not detected exactly as Apache-2.0" unless identifiers == ["Apache-2.0"]
' .cache/license.json

lake exe cache get
lake build Challenge Solution SolutionAxiomAudit

python3 scripts/lean_source_scan.py

lake env lean SolutionAxiomAudit.lean | tee .cache/solution-axioms.log
python3 - <<'PY'
from pathlib import Path

text = Path(".cache/solution-axioms.log").read_text(encoding="utf-8")
for forbidden in ["sorryAx", "Lean.ofReduceBool"]:
    if forbidden in text:
        raise SystemExit(f"forbidden axiom dependency: {forbidden}")
allowed = {"propext", "Quot.sound", "Classical.choice"}
start = text.rfind("[")
end = text.find("]", start)
if start < 0 or end < 0:
    raise SystemExit("could not parse axiom audit output")
reported = {item.strip() for item in text[start + 1:end].split(",") if item.strip()}
extra = reported - allowed
if extra:
    raise SystemExit(f"non-Palomar axiom dependencies: {sorted(extra)}")
PY

./scripts/verify-comparator.sh 2>&1 | tee .cache/comparator.log
python3 scripts/check-claims.py --verified \
  --axiom-log .cache/solution-axioms.log \
  --comparator-log .cache/comparator.log

if [ "${1:-}" = "--local" ]; then
  if [ "${GITHUB_ACTIONS:-}" = "true" ]; then
    echo "PUBLIC LINUX CHECKS PASSED: pinned-commit GitHub Actions replay completed."
  else
    echo "PRIVATE LINUX CHECKS PASSED: publication provenance and final submitter approval remain separate."
  fi
fi
