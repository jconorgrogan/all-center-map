# Provenance record

## Current substantive source state

The inspected source directory is not a Git checkout. Accordingly there is no
source commit SHA to claim. `evidence/CURRENT_SOURCE_CONTENT.sha256` records a
content-addressed snapshot of the 558 top-level `map/*.lean` files observed on
30 August 2026. The SHA-256 of that canonicalized manifest is
`c0e72b588e4a36d008004501594cd99c2a6573d807c2475e7ccbec6da4dded59`.

Selected source hashes at inspection time:

| Artifact | SHA-256 |
|---|---|
| `map/lean-toolchain` | `ce4c4e3d87434b9663f46de25ce34b48a0cf0d392e0a320a0787b4674a2d7b61` |
| `map/lakefile.lean` | `913101bf97551dcd5937687578ef9a3aaf07eb4948660f40881a3e6f0cd00937` |
| `map/lake-manifest.json` | `1da2045427aaf72813e9f44025da97ca481cf75d6932f520c67072e37787b2da` |
| `map/CertificationAxiomAudit.lean` | `5692b60572414b08b1471c79daf68541fc28ef4f297b78558e615b2e32a5765d` |
| `map/FULL_BUILD_2026-08-30.log` | `8d61a2542fc4b0d70b07cbf4510a37d08baa33e9d7ea3a51a86eaffe569107f8` |
| `map/FULL_AXIOM_AUDIT_2026-08-30.log` | `5e11b90cabc9e2e176cccd2a316609259384efc90cc19f8e062347c92474b9f8` |
| manuscript TeX | `a941b349c89e7d8e014c47e25a0ba4c3a3dbdd48b7e0257b4bed8b78764e7f81` |

These hashes prove file identity only. They do not prove a clean checkout,
authorship, a dependency graph, or the source state from which a future release
commit was made.

## Required commit chain

1. Commit the substantive proof tree after the zero-argument endpoint exists.
2. Run `scripts/stage-proof-sources.py` from that clean revision. The generated
   `proof-snapshot.json` records its public-style remote, full commit SHA,
   source subdirectory, transitive module list, and per-file hashes.
3. Commit the staged release repository. Rebuild from a clean Linux clone.
4. If verification changes any committed file, commit again and repeat. The
   final submission identifier is the release repository's full 40-character
   `HEAD`, never a tag or branch.
5. Preserve the generated Palomar mechanical report, which independently
   records file hashes and exact Comparator/exporter/NanoDa revisions.

The release candidate itself has not been initialized, committed, published,
or submitted.
