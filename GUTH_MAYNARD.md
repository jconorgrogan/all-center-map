# Guth–Maynard large values: an internal proved component

The reusable supporting theorem is
`GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11`.
It has no Guth–Maynard, Proposition 3.1, or other analytic-source hypothesis.
Its conclusion is `CGLProofDAG.GuthMaynardTheorem11`.

## Exact mathematical scope

For every $\eta>0$, there are constants $C>0$ and $T_0\ge2$ such that the
following holds uniformly for $T\ge T_0$, $V>0$, a natural number $N\ge1$,
and complex coefficients $b_n$ satisfying $|b_n|\le1$.

If $W\subset[0,T]$ is finite, distinct points of $W$ are at least one apart,
and every $t\in W$ satisfies

$$\left|\sum_{N<n\le2N} b_n e^{it\log n}\right|\ge V,$$

then

$$|W|\le C T^\eta\left(\frac{N^2}{V^2}
 +\frac{N^{18/5}}{V^4}+\frac{T N^{12/5}}{V^4}\right).$$

The constants are chosen before the polynomial, its length, the threshold,
and the set of large-value times.

The proof combines the internally established fixed-weight Proposition 3.1
estimate with critical and complementary ranges. See
`Proof/GuthMaynardProp31Actual.lean`,
`Proof/GuthMaynardTheorem11FinalGlue.lean`, and
`Proof/GuthMaynardActualEndpointWeakTheta.lean`.

The mathematical source is Larry Guth and James Maynard,
[New large value estimates for Dirichlet polynomials](https://annals.math.princeton.edu/2026/203-2/p06),
Annals of Mathematics 203 (2026), 623–675, Theorem 1.1. This release claims the displayed
epsilon-form, not every theorem or application in that paper.

## Verification

The declaration compiled with only `propext`, `Classical.choice`, and `Quot.sound`.
On 2026-09-20 its own complete type/proof dependency closure of **75,874
declarations** passed a fresh replay into an empty Lean kernel environment.
The replay rejected nonstandard axioms and unsafe/partial dependencies and
compared the resulting theorem's name, type, proof term, and universe parameters
to the original. It completed in 161.36 seconds.

The [record](evidence/kernel-replay/guth-maynard/result.json),
[declaration manifest](evidence/kernel-replay/guth-maynard/declarations.txt), and
[output](evidence/kernel-replay/guth-maynard/output.txt) are retained.
This is Lean's own kernel replay, **not independent NanoDa verification**.
The current Comparator entry selects MAP only; it does not separately register
this supporting theorem. See [verification and reproduction](VERIFICATION.md).
