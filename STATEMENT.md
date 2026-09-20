# All-center local minor-arc estimate

This is the mathematical statement selected for this release. The authoritative
formal surface is [Challenge.lean](Challenge.lean); its independent proof is
[Solution.lean](Solution.lean). This document does not assert the separate
prime-pair consequences discussed in the historical manuscript.

Write the circle as $\mathbb T=\mathbb R/\mathbb Z$, with its usual quotient
metric and Haar measure of total mass one. Define

$$S_X(\alpha)=\sum_{\lfloor X\rfloor<n\le\lfloor2X\rfloor}
\Lambda(n)e^{2\pi i n\alpha}.$$

For positive integers $B,D$, let

$$\mathfrak M_{B,D}(X)=\bigcup_{\substack{1\le q\le(\log X)^B\\
0\le a<q,\ (a,q)=1}}
\left\{\alpha\in\mathbb T:\operatorname{dist}(\alpha,a/q)
\le\frac{(\log X)^D}{X}\right\},
\qquad \mathfrak m_{B,D}(X)=\mathbb T\setminus\mathfrak M_{B,D}(X).$$

**Theorem (MAP at exponent $2/15$).** For every $A>0$ and $\varepsilon>0$
there exist integers $B,D\ge1$ and real constants $C>0$, $X_0\ge2$ such that,
for every real $X\ge X_0$, every real $H\ge X^{2/15+\varepsilon}$, and
**every** center $\alpha_0\in\mathbb T$,

$$\int_{\overline B(\alpha_0,1/(2H))\cap\mathfrak m_{B,D}(X)}
|S_X(\alpha)|^2\,d\alpha\le C X(\log X)^{-A}.$$

The measure is not rescaled by the length of the integration arc. All cutoffs
and constants are fixed before $X$, $H$, and $\alpha_0$ are chosen. There is no
upper bound on $H$ in this statement and no exceptional set of centers.

## Source and scope

This is Theorem 1.1 (Uniform local minor-arc estimate) of the local manuscript
*Prime Pairs at the Prime Number Theorem Threshold: Hardy–Littlewood for Almost
Every Shift in Every Interval of Length X^(2/15+epsilon)*, attributed to Conor
Grogan. The historical TeX source has SHA-256
`a941b349c89e7d8e014c47e25a0ba4c3a3dbdd48b7e0257b4bed8b78764e7f81`.
No public version of that historical manuscript is asserted here. This release
provides the explicit MAP statement and substantive Lean proof directly.

The independent Challenge contains one protocol `sorry`. The Solution does not
import Challenge and has no admission. Release verification status is recorded
in [VERIFICATION.md](VERIFICATION.md); source-to-statement alignment is recorded
in [MANUSCRIPT_ALIGNMENT.md](MANUSCRIPT_ALIGNMENT.md).
