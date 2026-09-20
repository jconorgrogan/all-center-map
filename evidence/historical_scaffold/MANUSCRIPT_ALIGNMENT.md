# Manuscript, Challenge, and metadata alignment

The source manuscript is
`AllCenterMAP_2_15_Package/paper/all_center_map_2_15.tex`, SHA-256
`a941b349c89e7d8e014c47e25a0ba4c3a3dbdd48b7e0257b4bed8b78764e7f81`.
The relevant source is Theorem 1.1, lines 101–120. The manuscript's scope
paragraph at lines 858–888 already says the endpoint declaration is awaiting a
proof.

| Mathematical item | Manuscript Theorem 1.1 | `Challenge.lean` | Status |
|---|---|---|---|
| Advertised result | Uniform local minor-arc estimate | `AllCenterMAP.map_two_fifteenths` | Same sole entry |
| Exponential sum | `sum_{X<n<=2X} Lambda(n)e(n alpha)` | `primeExponentialSum` with `Finset.Ioc floor(X) floor(2X)` | Same finite support |
| Major arcs | Reduced `a mod q`, `q<=log(X)^B`, radius `log(X)^D/X` | `majorArcs` with `a<q`, coprimality, circle distance | Same |
| Measure | Lebesgue/Haar measure on the circle | normalized `AddCircle.haarAddCircle` | Same normalization |
| Local set | Every circle arc of length `1/H` | every centered closed ball of radius `1/(2H)` | Equivalent in the legal range; keep this identification explicit in review prose |
| Scale | `H>=X^(2/15+epsilon)` | identical lower bound | Same |
| Choice order | `A,epsilon -> B,D,C,X0 -> X,H,J` | identical order before `X,H,center` | Same |
| Cutoff domains | positive integers `B,D` | natural numbers plus `1<=B`, `1<=D` | Manuscript-faithful; stronger than current internal Prop |
| Consequences | Separate Theorems 1.2 and Goldbach theorem | excluded | Deliberate one-entry scope |

## Required final manuscript edit

Only after the zero-argument theorem and independent verifier succeed, replace
the current “statement awaiting proof” paragraph with a bounded claim naming:

- `AllCenterMAP.map_two_fifteenths` as the only compared theorem;
- the exact release commit and `comparator.json` path;
- successful stable Lean build, Comparator statement identity, permitted-axiom
  check, Lean kernel acceptance, and NanoDa replay under Linux/Landrun;
- the fact that these checks do not establish novelty, peer review, or fidelity
  beyond the audited statement.

Do not broaden that paragraph to the prime-pair, Q4, density-one, Goldbach, or
decoder results unless each is later packaged as its own honest declaration.

