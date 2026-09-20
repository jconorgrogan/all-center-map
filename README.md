# Lean Proof of Uniform Minor-Arc Cancellation at the `2/15` Threshold

## Prime-weighted exponential sums and short frequency windows

Prime numbers leave a signal in the exponential sum
`Λ(n) exp(2πi nα)` over `X < n ≤ 2X`, where `Λ(n)` is the von Mangoldt weight.
That signal is strongest near rational frequencies. For any center on the
circle—whether the center itself is near a rational frequency or not—the
theorem integrates only the minor-arc portion inside the centered interval. It
proves that this portion has total squared signal at most
`C X (log X)^(-A)` whenever `H ≥ X^(2/15+ε)` and `X` is large enough.

Here `A` and `ε` can be any positive numbers. The constants and the rational
frequency cutoffs are chosen once, before the center and the scale are known.
The exponent `2/15` is therefore a uniform threshold for local minor-arc
cancellation, which is the estimate needed in arguments about primes in short

This estimate is part of the analytic machinery behind work of
Matomäki–Radziwiłł–Tao on correlations of the von Mangoldt function and divisor
functions. Their earlier `8/33` scale for averaged prime-pair information gives
context for why a uniform local estimate at `2/15` is useful: it controls the
short frequency windows that arise when studying primes with a prescribed shift.

The constants `C` and `X₀` are ineffective. The proof uses Siegel's theorem, so
it establishes their existence without giving an algorithm that computes them.

Its formal name is `AllCenterMAP.map_two_fifteenths`.

For every positive logarithmic saving A and positive epsilon, fixed positive
integer major-arc cutoffs and constants control the normalized Haar integral of
the squared von Mangoldt exponential sum on the minor-arc portion of every circle
arc of radius 1/(2H), whenever H >= X^(2/15+epsilon) and X is sufficiently large.
The cutoffs and constants are chosen before X, H, and the arc center.
See [the precise mathematical statement](STATEMENT.md).

## Resources

- [Overview and exact statement](STATEMENT.md)
- [Formal statement](Challenge.lean)
- [Proof entry point](Solution.lean)
- [Guth–Maynard formalization](GUTH_MAYNARD.md)
- [Verification record](VERIFICATION.md)
- [Source and citation map](PROVENANCE.md)
- [Reproducibility and proof optimization notes](PROOF_OPTIMIZATION.md)

`Challenge.lean` gives the compact mathematical statement, and `Solution.lean`
supplies its proof from the substantive development in `Proof/`. The proof uses
Lean's standard axioms `propext`, `Quot.sound`, and `Classical.choice`.

The 1,861 proof modules form the MAP endpoint's content-hashed import closure.
Of these, 1,860 preserve the verified authoring snapshot byte-for-byte; one has
[a checked algebraic proof-term optimization](PROOF_OPTIMIZATION.md) with all
statements unchanged. The complete 100,596-declaration proof closure replays
exactly into an empty Lean kernel environment.

## A second theorem in the development

A substantial part of the development is an internal proof of the epsilon-form
of Guth–Maynard's large-value estimate for Dirichlet polynomials. The closed
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

The complete formal environment and reproducibility material are collected in
the linked resources above. The project uses Lean `v4.30.0-rc2` with Mathlib
commit `0f9072dd907c6e2e4264ab241a049cab50137f7c` and is released under the
Apache-2.0 license.
