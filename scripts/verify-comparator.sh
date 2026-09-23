#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in lake python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required for sandboxed Comparator verification" >&2
    exit 1
  fi
done

sandbox_command=${COMPARATOR_BWRAP:-bwrap}
if ! command -v "$sandbox_command" >/dev/null 2>&1; then
  echo "error: $sandbox_command is required for sandboxed Comparator verification" >&2
  exit 1
fi

# Exporter and kernels must come from the same toolchain as the compiled proof.
# Palomar's hosted workflow additionally freezes and protects the Challenge.
toolchain_prefix=$(lake env lean --print-prefix)
for tool in leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$toolchain_prefix/bin/$tool" ]; then
    echo "error: the selected Lean toolchain does not bundle $tool" >&2
    exit 1
  fi
done

verification_config=$(mktemp "${TMPDIR:-/tmp}/map-comparator.XXXXXXXX.json")
trap 'rm -f "$verification_config"' EXIT

python3 - "$repository_root/comparator.json" "$verification_config" "$toolchain_prefix" <<'PY'
import json
import pathlib
import sys

source, destination, toolchain = map(pathlib.Path, sys.argv[1:])
config = json.loads(source.read_text(encoding="utf-8"))
if not isinstance(config, dict) or config.get("enable_nanoda") is not True:
    raise SystemExit("error: the release configuration must require NanoDa")
if "external_kernels" in config:
    raise SystemExit("error: submitted configuration must not supply external_kernels")
config.pop("enable_nanoda")
config["external_kernels"] = {
    "nanoda": [str(toolchain / "bin" / "nanoda_bin")],
    "con-ron": [str(toolchain / "bin" / "con-ron")],
}
destination.write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

# Keep the sandbox enabled; the bundled comparator invokes Lean's kernel too.
lake comparator --config "$verification_config"
