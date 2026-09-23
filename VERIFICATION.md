# Verification

The formal theorem is [`AllCenterMAP.map_two_fifteenths`](Challenge.lean).
Its proof permits only `propext`, `Quot.sound` and `Classical.choice`.

## Lean 4.35 build

`lake build Challenge Solution SolutionAxiomAudit` completed successfully on
macOS ARM with Lean `v4.35.0-rc2`: **10,797 jobs** in the completed build graph.
The axiom audit for `AllCenterMAP.map_two_fifteenths` reports exactly
`propext`, `Classical.choice` and `Quot.sound`.

- [Build log](evidence/lean435-macos-build.log)
- [Axiom audit](evidence/lean435-macos-axioms.log)
- [Machine-readable verification record](evidence/lean435-macos-verification.json)

This is the current author build. Linux Comparator and independent-kernel
results are recorded separately by the public workflow below.

## Reproducible toolchain

The current project pins Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Build the statement, proof and
axiom audit with:

```sh
lake build Challenge Solution SolutionAxiomAudit
```

On Linux, [`scripts/verify-linux.sh`](scripts/verify-linux.sh) adds source,
metadata and license checks, then runs the toolchain's bundled Comparator.
Comparator compares the Solution with the Challenge and checks the exported
proof with Lean's kernel, NanoDa and con-ron. The wrapper keeps bubblewrap
enabled and uses the exporter and kernels from the selected Lean installation.

Use `bash scripts/verify-linux.sh --local` for an author run, or
`bash scripts/verify-linux.sh` on a clean clone to include GitHub origin
provenance. The required sandbox installation is documented in the
[workflow](.github/workflows/release.yml).

## Public mechanical verification

[Palomar release checks](https://github.com/jconorgrogan/prime-minor-arcs-2-15/actions/workflows/release.yml)
runs two jobs on the public commit: the repository's Linux checks and the
official full Palomar verifier. The latter is pinned to PalomarSubmission
`1703d7babd984ccc3831cdf89c28221abe34808f` and uses its approved GitHub-hosted
`palomar-standard-v1` execution profile.

The official verifier separately compiles the Challenge against frozen
canonical dependencies, protects that statement from the candidate build,
and checks the Solution with Comparator and all three kernels. It produces
the `mechanical-report-map435verify` artifact. The report must identify the
exact source SHA and configuration and report `status: pass` and
`stage: complete`.

[RELEASE_STATUS.md](RELEASE_STATUS.md) identifies the current release evidence.
A hosted preflight report and a Palomar submission have separate run records.
Mathematical editorial review is a separate stage.

## September 20, 2026 verification records

The Lean `v4.30.0-rc2` release passed a fresh Linux source build of
**10,255 jobs**, Comparator statement identity, independent NanoDa replay,
Lean kernel checks, source/dependency scanning and the standard-axiom audit.

The MAP proof closure contained **100,596 declarations** across **1,861
modules**. The Guth–Maynard large-value closure contained **75,874
declarations**. Both replayed into empty Lean kernel environments: MAP in
334.25 seconds and Guth–Maynard in 161.36 seconds. The
[MAP record](evidence/kernel-replay/map/result.json) and
[Guth–Maynard record](evidence/kernel-replay/guth-maynard/result.json) preserve
their original toolchain, source hashes and results.

The Linux run also compiled the algebraically optimized proof module in
6.0 seconds; [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md) records that change.
These counts and timings describe the September 20 sources and toolchain.

## Reproduce the closure checks

After the build above, run:

```sh
mkdir -p .cache
lake env lean --run scripts/ReplayProofClosure.lean MAPReleaseEndpoint \
  MAPReleaseEndpoint.zero_argument_map_two_fifteenths .cache/map-declarations.txt
lake env lean --run scripts/ReplayProofClosure.lean GuthMaynardActualEndpointWeakTheta \
  GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11 .cache/gm-declarations.txt
```

The verification utility replays the selected type/proof closure into an empty
Lean kernel environment and rejects unsafe or partial declarations.
Its `unsafe` entry point enables Lean's replay API; the mathematical development
does not import it. A replay records its own declaration counts rather than
assuming those of an earlier toolchain.
