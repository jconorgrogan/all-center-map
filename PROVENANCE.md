# Provenance

`proof-snapshot.json` records the 1,861 source modules and their SHA-256 hashes.
The development originated in an isolated verified snapshot. The current
sources include compatibility changes for Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`, together with an earlier algebraic
proof-term optimization; see [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md).
Historical verification records retain the source hashes and toolchain of
the run they document. The release Git commit identifies the submitted source.

The current Lean 4.35 sources passed the `Challenge`, `Solution` and
`SolutionAxiomAudit` build on macOS ARM. The
[verification record](evidence/lean435-macos-verification.json) identifies that
run; [VERIFICATION.md](VERIFICATION.md) separates it from the earlier Lean 4.30
Linux and proof-closure records.

The original release scaffold is under `evidence/historical_scaffold`.
Author, maintainer, and Apache-2.0 licensing were confirmed on 2026-09-20.

## Manuscript and formalization

Conor Grogan’s manuscript first presented the all-center MAP result. The Lean
development subsequently formalized its Theorem 1.1. The author confirmed this
order on 2026-09-24. The source is included as
[the manuscript](paper/prime-pairs-pnt-threshold.tex), and `formalization.yaml`
records it as a paper with the relationship `formalizes`. Both the manuscript
and the formalization are by Conor Grogan.

## Mathematical source map

The closed release theorem has no unproved source premise. The development
also contains source-facing adapters; inspect their hypotheses before reuse.

| Source family | Credited work | Role in this repository |
|---|---|---|
| Guth–Maynard | [Annals 203 (2026), 623–675](https://annals.math.princeton.edu/2026/203-2/p06) | Internal epsilon-form large-value theorem; see GUTH_MAYNARD.md |
| Matomäki–Radziwiłł–Tao | [Correlations of the von Mangoldt and higher divisor functions I](https://arxiv.org/abs/1707.01315v3) | Supporting short-interval/correlation argument source family |
| Ford | [Vinogradov's integral and bounds for the Riemann zeta function](https://doi.org/10.1112/S0024611502013655) | Supporting exponential-sum and zero-free estimates |
| Chen–Gupta–Li | [Character large values and zero density](https://arxiv.org/abs/2507.08296v2) | Supporting character/zero-density source family |

Other headers name Jutila, Huxley, Khale, Koukoulopoulos, McCurley,
Montgomery, Shiu, Ramachandra, Goldfeld, and Heath–Brown. The adapters in
`CGLMeshFormalization.lean`, `MRTCorollary53SourceBridge.lean`, and
`GuthMaynardHeathBrownInterface.lean` are interfaces; inspect their
hypotheses before reuse.

## Citation erratum in a preserved source header

`Proof/MRTCorollary53SourceBridge.lean` names “functions II” while referring to
Corollary 5.3, PDF page 53, and region (69). The primary source for those exact
references is **Part I**, [arXiv:1707.01315v3, page 53](https://arxiv.org/pdf/1707.01315v3#page=53).
Part II, [arXiv:1712.08840v2](https://arxiv.org/abs/1712.08840v2), instead cites
Part I's Corollary 5.3. The release metadata uses the corrected Part I citation.
The historical source comment is retained byte-for-byte to preserve the proof
snapshot hashes; it does not alter a declaration or proof term.
