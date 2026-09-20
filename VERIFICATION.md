# Verification

The optimized release passed:

- a fresh Linux source build: **10,255** jobs
- Comparator statement identity
- independent NanoDa replay
- Lean kernel checks
- source and dependency scanning
- an axiom audit: only `propext`, `Quot.sound`, and `Classical.choice`

See [RELEASE_STATUS.md](RELEASE_STATUS.md).

The MAP endpoint proof closure is **100,596** declarations across **1,861**
modules. The Guth–Maynard large-value closure is **75,874** declarations.
Both closures replayed into an empty Lean kernel environment; the MAP replay
took 334.25 seconds and the Guth–Maynard replay took 161.36 seconds. Records
are under [evidence/kernel-replay](evidence/kernel-replay).

The authoring-baseline MAP replay used Lean's kernel. The release then passed
independent NanoDa replay of the exported proof.

One module has a checked algebraic proof-term optimization with unchanged
statements; see [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md). That module
compiled from source in the Linux build in 6.0 seconds. The Guth–Maynard
closure does not depend on it.

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

The public replay is the GitHub Actions workflow `Palomar release checks` on
this repository. Earlier public runs stopped at the publication gate because
Bundler wrote `vendor/bundle` into the checkout before the script ran; that is
an environment failure, not a mathematical one. The workflow now confirms the
clean pinned commit first, then runs `bash scripts/verify-linux.sh --local`.

Locally, run `bash scripts/verify-linux.sh --local` for the release check, or
omit `--local` for the additional clean Git/public-origin provenance gate.
