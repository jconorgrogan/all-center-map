# Release status — 30 August 2026

**Status: blocked; not submission-ready; not published or submitted.**

Target: `AllCenterMAP.map_two_fifteenths` only, aligned to manuscript Theorem
1.1. Toolchain target: stable Lean `v4.32.0`, Mathlib commit
`81a5d257c8e410db227a6665ed08f64fea08e997`.

## Preflight results

| Command | Result |
|---|---|
| JSON/TOML parse for Comparator, manifest, provenance state, and Lakefile | PASS |
| Ruby YAML parse for metadata and workflow | PASS |
| `python3 -m py_compile scripts/*.py` and `bash -n` on shell entrypoints | PASS |
| `python3 scripts/static_preflight.py .` | PASS, 0 warnings |
| `ruby scripts/validate-formalization.rb` | PASS, no template sentinel |
| `python3 scripts/check-claims.py` | PASS, one theorem aligned to Theorem 1.1 |
| `./test/landrun_wrapper_test.sh` | PASS |
| candidate Lean-source forbidden-token scan | PASS |
| symlink and compiled-artifact scan | PASS |
| byte comparison with frozen official verifier, wrapper, validator, licence, and Gem lock | PASS |
| stable `lake build Challenge` using the existing `v4.32.0` cache | EXPECTED FAIL at `MAP_RELEASE_BLOCKED_missing_zero_argument_endpoint`; statement elaboration reached the release gate |
| `python3 scripts/stage-proof-sources.py ../map` | EXPECTED FAIL because the source tree has no Git commit |
| local Licensee detection | NOT RUN: macOS system Ruby lacks locked Bundler `2.7.2`; pinned Linux workflow owns this check |
| `./scripts/verify-linux.sh` | NOT RUN: requires the endpoint and Linux/Landlock |

## Six active release-gate blockers

`python3 scripts/check-release-gate.py` exits 1 and reports exactly:

1. Challenge/Solution still contain the explicit missing-endpoint marker.
2. `formalization.yaml` still contains unresolved `BLOCKED:` fields.
3. Release prose still records that no zero-argument proof exists.
4. `Proof/MAPReleaseEndpoint.lean` is absent.
5. `proof-snapshot.json` is absent, so source commit provenance is unrecorded.
6. The release candidate is not a clean committed Git repository with a
   public-style GitHub `origin`.

After these six are closed, the final check is still not presumed: a clean
Linux run must pass the stable build, licence detection, proof-side source scan,
axiom audit, Comparator, toolchain-matched lean4export, Lean kernel, NanoDa, and
Landrun. `scripts/verify-linux.sh` is the sole entrypoint and gates the final
README/metadata claim check on the actual axiom and Comparator logs.

