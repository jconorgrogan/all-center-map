# Uniform minor-arc cancellation for prime-weighted exponential sums

## Why it matters

Prime numbers leave a structured signal in exponential sums. Near simple
rational frequencies that signal can be large, so analytic number theory treats
those frequencies separately as the major arcs. This theorem controls the rest:
on the minor arcs, even a short frequency window cannot collect much total
prime-weighted energy. The estimate works around every center with one common
choice of parameters, which is what makes it useful for local and shifted-prime
questions.

The analytic context is the study of correlations of the von Mangoldt function
with divisor functions and of prime pairs in short shift ranges. The `8/33`
scale in Matomäki–Radziwiłł–Tao's averaged results gives a useful comparison for
the local `2/15` threshold here. The constants in this theorem are ineffective:
Siegel's theorem supplies existence without an effective procedure for computing
them.

The formal statement is [Challenge.lean](Challenge.lean); the proof is
[Solution.lean](Solution.lean).

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

This is Theorem 1.1 (Uniform local minor-arc estimate) of
[Prime Pairs at the Prime Number Theorem Threshold](paper/prime-pairs-pnt-threshold.pdf).

The Challenge contains one protocol `sorry`. The Solution does not import
Challenge. Verification is recorded in [VERIFICATION.md](VERIFICATION.md);
alignment is recorded in [MANUSCRIPT_ALIGNMENT.md](MANUSCRIPT_ALIGNMENT.md).
