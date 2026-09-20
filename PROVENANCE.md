# Provenance

This repository contains the substantive proof, not a thin wrapper around an
unidentified upstream project. `proof-snapshot.json` records the 1,861 source
modules and their SHA-256 hashes. The release preserves 1,860 modules from the
isolated verified development byte-for-byte. One algebraic proof has a recorded,
checked optimization with the same statement; see [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md).
The baseline MAP proof-closure replay is retained and labeled as baseline evidence.

The old development was not maintained as a clean upstream Git repository. No
upstream repository or commit is invented: those fields are explicitly null.
The prepared release's own eventual Git commit will identify all submitted
source bytes. That commit and its actual public GitHub repository must be
recorded before submission.

The original release scaffold is preserved under `evidence/historical_scaffold`.
Its missing-endpoint status is historical, not the status of the current proof.
The old upstream-staging utility is retained under that historical directory;
it is not the generator
of this snapshot. The actual preparation script and immutable proof hashes are
recorded in the isolated preparation workspace.

Conor Grogan confirmed author/responsible-maintainer attribution and Apache-2.0
licensing on 2026-09-20. GitHub publication under `jconorgrogan` is authorized once ready. Palomar form
preparation must stop before final submission; registration is not authorized.
Automation, missing model/cost records, and limits of review are disclosed in
`formalization.yaml`. Human expert review is not claimed.

## Mathematical source map

The development contains both internally proved supporting results and
source-facing proposition interfaces/adapters. A named interface does not by
itself prove its published source. The closed release theorem has no such
unproved source premise; its actual proof dependency closure controls this
claim. Previously published supporting mathematics is not claimed as new.

| Source family | Credited work | Role in this repository |
|---|---|---|
| Guth–Maynard | [Annals 203 (2026), 623–675](https://annals.math.princeton.edu/2026/203-2/p06) | Internal epsilon-form large-value theorem; see GUTH_MAYNARD.md |
| Matomäki–Radziwiłł–Tao | [Correlations of the von Mangoldt and higher divisor functions I](https://arxiv.org/abs/1707.01315v3) | Supporting short-interval/correlation argument source family |
| Ford | [Vinogradov's integral and bounds for the Riemann zeta function](https://doi.org/10.1112/S0024611502013655) | Supporting exponential-sum and zero-free estimates |
| Chen–Gupta–Li | [Character large values and zero density](https://arxiv.org/abs/2507.08296v2) | Supporting character/zero-density source family |

Other historical headers and source-facing interfaces/adapters name Jutila,
Huxley, Khale, Koukoulopoulos, McCurley, Montgomery, Shiu, Ramachandra, Goldfeld,
and Heath–Brown. These references are not separate claims that their published
inputs or entire papers have been formalized. In particular, proposition
interfaces in `CGLMeshFormalization.lean`, `MRTCorollary53SourceBridge.lean`, and
`GuthMaynardHeathBrownInterface.lean` are not independently proved merely by
being defined. Their actual hypotheses must be inspected before reuse.

## Citation erratum in a preserved source header

`Proof/MRTCorollary53SourceBridge.lean` names “functions II” while referring to
Corollary 5.3, PDF page 53, and region (69). The primary source for those exact
references is **Part I**, [arXiv:1707.01315v3, page 53](https://arxiv.org/pdf/1707.01315v3#page=53).
Part II, [arXiv:1712.08840v2](https://arxiv.org/abs/1712.08840v2), instead cites
Part I's Corollary 5.3. The release metadata uses the corrected Part I citation.
The historical source comment is retained byte-for-byte to preserve the proof
snapshot hashes; it does not alter a declaration or proof term.
