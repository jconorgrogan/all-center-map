# Release-candidate verification record

Run on 30 August 2026 from macOS. This is packaging verification, not a proof or
Palomar mechanical report.

## Passed

- `python3 scripts/static_preflight.py .` — passed with zero warnings.
- `ruby scripts/validate-formalization.rb` — parsed the metadata and found no
  retained official-template sentinel.
- `python3 scripts/check-claims.py` — confirmed that Comparator, README,
  metadata, and the manuscript alignment record identify one declaration only:
  `AllCenterMAP.map_two_fifteenths`, corresponding to Theorem 1.1.
- Python compilation and `bash -n` passed for the custom release scripts and
  copied verifier wrappers.
- The official-template Landrun wrapper test passed.
- With the existing stable `v4.32.0` Mathlib cache temporarily exposed,
  `lake build Challenge` parsed the candidate Lakefile and the complete
  Challenge statement, then failed at exactly
  `AllCenterMAP.MAP_RELEASE_BLOCKED_missing_zero_argument_endpoint`.
- `scripts/stage-proof-sources.py ../map` refused to copy because the current
  substantive tree is not a Git checkout.
- No release-candidate command wrote canonical `map/lakefile.lean` or
  `map/CertificationAxiomAudit.lean`. Both files changed concurrently elsewhere
  after the initial evidence snapshot, so the recorded hashes are explicitly
  time-bounded and must not be mistaken for the current source state.

## Expected fail-closed result

`python3 scripts/check-release-gate.py` reports:

1. explicit missing-endpoint marker remains;
2. unresolved metadata fields remain;
3. release prose still says the zero-argument proof is absent;
4. `Proof/MAPReleaseEndpoint.lean` is absent;
5. `proof-snapshot.json` and a source commit are absent;
6. the release candidate is not a committed Git repository with a public-style
   origin.

## Not run and not claimed

- current-tree stable `lake build`;
- solution axiom audit for the absent endpoint;
- a clean Linux rebuild;
- SPDX detection through the pinned Licensee/Bundler environment (the local
  macOS system Ruby does not provide the locked Bundler version);
- Comparator statement comparison;
- toolchain-matched lean4export;
- Lean default-kernel and NanoDa acceptance under Landrun;
- publication, Palomar submission, or registration.

`./scripts/verify-linux.sh` is the single final entrypoint for those checks. It
refuses non-Linux systems, executes the axiom audit before Comparator, captures
both logs, and only then runs the verified claim-alignment gate.
