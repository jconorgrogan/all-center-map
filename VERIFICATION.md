# Verification scope

## Completed

The authoring baseline MAP endpoint passed its pinned Lean build, statement/quantifier review,
standard-axiom audit, and trust-zero source elaboration. Its full **100,596**
declaration type/proof closure passed fresh replay into an empty Lean kernel
environment in 334.25 seconds. The standalone Guth–Maynard Theorem 1.1 wrapper
passed the same check for **75,874** declarations in 161.36 seconds.
Both replays checked exact theorem name, type, proof term, and universe parameters;
only `propext`, `Classical.choice`, and `Quot.sound` were permitted as axioms.
These use Lean's own kernel, not an independent kernel implementation.

Original run records, declaration manifests, and output are retained under
[evidence/kernel-replay](evidence/kernel-replay). Source hashes and checker hash
are recorded there. The original authoring paths identify the recorded runs;
they are not paths required for reproduction.

The independent Mathlib-only Challenge and the release Solution compiled in
separate surface checks. The Solution axiom audit reported only the three
standard axioms. These surface checks used hash-matched existing proof oleans;
they were not a fresh Linux source build.

## Reproduce the closure checks

After `lake build Challenge Solution SolutionAxiomAudit`, run:

```sh
mkdir -p .cache
lake env lean --run scripts/ReplayProofClosure.lean MAPReleaseEndpoint \
  MAPReleaseEndpoint.zero_argument_map_two_fifteenths .cache/map-declarations.txt
lake env lean --run scripts/ReplayProofClosure.lean GuthMaynardActualEndpointWeakTheta \
  GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11 .cache/gm-declarations.txt
```

The `unsafe` entry point in this verification utility enables Lean's replay API;
it is not imported by the mathematical development. The utility refuses unsafe
or partial declarations in the selected proof closure.

## Proof-term optimization

One release module now uses direct algebraic identities instead of two expansive
`ring` proofs. Its statements are unchanged and its candidate compilation passed;
see [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md). The recorded MAP replay above
is the authoring-baseline replay. The optimized module then compiled from source
in the Linux build in 6.0 seconds. The Guth–Maynard proof closure does not
depend on the changed BHP declarations.

## Release checks

The optimized release passed a fresh Linux source build (10,255 jobs),
Comparator statement identity, independent NanoDa replay, Lean kernel checks,
source/dependency scanning, and an axiom audit. See
[RELEASE_STATUS.md](RELEASE_STATUS.md).

Run `bash scripts/verify-linux.sh --local` for the private release check, or
omit `--local` for the additional clean Git/public-origin provenance gate.
