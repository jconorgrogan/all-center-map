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

The source manuscript artifact is
`AllCenterMAP_2_15_Package/paper/all_center_map_2_15.tex`, historically hashed
as a941b349c89e7d8e014c47e25a0ba4c3a3dbdd48b7e0257b4bed8b78764e7f81.
The reader-facing statement is [STATEMENT.md](STATEMENT.md).
