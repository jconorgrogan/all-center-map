# Manuscript and Lean alignment

The sole entry is `AllCenterMAP.map_two_fifteenths`, manuscript Theorem 1.1.
The exact statement uses the finite von Mangoldt sum over floor(X)<n<=floor(2X),
reduced rational major arcs with logarithmic denominator and radius cutoffs,
their complement, normalized Haar measure on UnitAddCircle, and every centered
closed circle ball of radius 1/(2H). The threshold is H>=X^(2/15+epsilon).
Positive A and epsilon precede positive natural B,D and positive C and X0>=2;
these precede X,H,center. No RH or unproved analytic source hypothesis is added.

The release proof is the zero-argument theorem
`MAPReleaseEndpoint.zero_argument_map_two_fifteenths`. The public Solution
restates the definitions directly; Comparator must verify exact statement
identity against the independently compiled Mathlib-only Challenge.

The source manuscript is
[paper/prime-pairs-pnt-threshold.tex](paper/prime-pairs-pnt-threshold.tex),
with the compiled paper at
[paper/prime-pairs-pnt-threshold.pdf](paper/prime-pairs-pnt-threshold.pdf).
The reader-facing statement is [STATEMENT.md](STATEMENT.md).
