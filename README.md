# All-center MAP at exponent 2/15

This prepared release proves `AllCenterMAP.map_two_fifteenths`, the all-center
local minor-arc estimate in manuscript Theorem 1.1. It is not yet submission-ready:
Linux Comparator/NanoDa verification and a public immutable release commit remain
outstanding. Nothing has been published or submitted.

For every positive logarithmic saving A and positive epsilon, fixed positive
integer major-arc cutoffs and constants control the normalized Haar integral of
the squared von Mangoldt exponential sum on the minor-arc portion of every circle
arc of radius 1/(2H), whenever H >= X^(2/15+epsilon) and X is sufficiently large.
The cutoffs and constants are chosen before X, H, and the arc center.
See [the precise mathematical statement](STATEMENT.md).

`Challenge.lean` is the independent, Mathlib-only statement surface. Its single
intentional `sorry` is the Comparator challenge hole; it is not used by the
Solution. `Solution.lean` supplies the exact zero-argument proof from the
substantive development in `Proof/`. Proof-side admissions and custom axioms are
not permitted. The only allowed axioms are `propext`, `Quot.sound`, and
`Classical.choice`.

The 1,861 proof modules form the MAP endpoint's content-hashed import closure.
Of these, 1,860 preserve the verified authoring snapshot byte-for-byte; one has
[a checked algebraic proof-term optimization](PROOF_OPTIMIZATION.md) with all
statements unchanged. The authoring baseline's 100,596-declaration closure
passed fresh replay into an empty Lean kernel environment. Fresh checks of the
optimized release are pending; the baseline result is not a NanoDa check.

## Research audience

The MAP statement gives local minor-arc control with arbitrary logarithmic
saving, uniformly over every circle center at the stated power scale. The
quantifier order matters: no new cutoffs are chosen to accommodate an individual
center. This is relevant to analytic number theorists studying minor arcs and
shifted-prime correlations. The release records this estimate itself, without
claiming that the separate prime-pair applications have been certified here.

For researchers in formalized analytic number theory, the internally proved
Guth–Maynard large-value theorem is a second substantial point of entry.

## Internal Guth–Maynard formalization

A substantial part of the development is an internal proof of the epsilon-form
of Guth–Maynard's Theorem 1.1 on large values of Dirichlet polynomials. The closed
declaration
[`GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11`](Proof/GuthMaynardActualEndpointWeakTheta.lean)
is derived from the proved local estimate
[`GuthMaynardProp31Actual.actual_fixedWeightProp31`](Proof/GuthMaynardProp31Actual.lean),
not from a Guth–Maynard axiom or an unproved Guth–Maynard premise. This is a
reusable mathematical component in its own right, beyond the MAP exponent.

For bounded complex coefficients and a one-separated finite set of large-value
times in [0,T], the formal statement bounds its cardinality by
C T^eta (N^2/V^2 + N^(18/5)/V^4 + T N^(12/5)/V^4), with constants chosen before
the polynomial and the large-value set. The exact definition is
[`CGLProofDAG.GuthMaynardTheorem11`](Proof/CGLProofDAG.lean).

Its own 75,874-declaration dependency closure passed fresh replay into an empty
Lean kernel environment with only the three standard axioms.

This names a specific theorem, not a claim that every result in the Guth–Maynard
paper has been formalized. MAP remains the sole theorem selected by this
Comparator configuration. The supporting formalization and its verification
record are described in `GUTH_MAYNARD.md`.

## Scope

This entry contains only the MAP theorem. Prime-pair consequences, Q4,
density-one, Goldbach, and the direct mesoscopic decoder are not advertised by
this Comparator configuration. No claim of novelty, external human review, or
Palomar registration is made.

## Reproduction

The exact proof environment is Lean `v4.30.0-rc2` and Mathlib commit
`0f9072dd907c6e2e4264ab241a049cab50137f7c`. Palomar accepts eligible RC toolchains;
the matching lean4export tag resolves to
`12581a6b680d8478175596338eb2d53383a323e3`.

Local structural checks do not require a public repository:

```sh
python3 scripts/static_preflight.py .
ruby scripts/validate-formalization.rb
python3 scripts/check-claims.py
```

The final Linux check must include Comparator statement identity, Lean kernel
acceptance, independent NanoDa replay under Landrun, and permitted-axiom audit.
The publication/submission gate additionally requires a clean committed Git tree
and the actual public GitHub origin. Do not invent a repository or source history.

Conor Grogan confirmed authorship, responsible maintenance, and Apache-2.0
licensing for this prepared release on 2026-09-20. Publication to `jconorgrogan` on GitHub is authorized once the release is ready.
Palomar preparation must stop before the final submission button. See `RELEASE_STATUS.md` for checked versus pending work.
