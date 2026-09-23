# Release verification

The release theorem is
[`AllCenterMAP.map_two_fifteenths`](Challenge.lean): uniform local minor-arc
cancellation at the `2/15` scale. Author and maintainer: Conor Grogan.
License: Apache-2.0.

The current source pins Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.
`lake build Challenge Solution SolutionAxiomAudit` passed on macOS ARM,
completing a 10,797-job build graph. The endpoint audit reports only
`propext`, `Classical.choice` and `Quot.sound`.
The [current verification record](evidence/lean435-macos-verification.json)
documents this author build.

The [release gates](BLOCKERS.md) bind the public source commit to its official
full mechanical report.

The September 20, 2026 Lean `v4.30.0-rc2` release passed the 10,255-job Linux
build, Comparator, NanoDa and Lean kernel checks. Its recorded kernel closures
contain 100,596 declarations for MAP and 75,874 for Guth–Maynard. These are
historical results, preserved with their original toolchain and source hashes
in [the verification records](VERIFICATION.md).

Current public runs appear in
[Palomar release checks](https://github.com/jconorgrogan/prime-minor-arcs-2-15/actions/workflows/release.yml).
The hosted report and Palomar submission are separate from the completed
author build.
