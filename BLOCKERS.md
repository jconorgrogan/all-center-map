# Release gates

The Lean `v4.35.0-rc2` author build and axiom gate is complete:
`lake build Challenge Solution SolutionAxiomAudit` passed on macOS ARM
(10,797 jobs), with only the standard permitted axioms.

For each submission, verify the public commit against these release gates:

1. The finalized source hashes and verification metadata identify the source
   committed and published on `origin/main`.
2. The official full [Palomar preflight](.github/workflows/release.yml) reports
   `status: pass` and `stage: complete` for that exact public commit and
   `comparator.json`.

[RELEASE_STATUS.md](RELEASE_STATUS.md) identifies the versioned evidence;
[VERIFICATION.md](VERIFICATION.md) gives the reproduction procedure.
