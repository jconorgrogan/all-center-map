# Uniform Minor-Arc Cancellation for Primes at the `X^(2/15+ε)` Scale

A formally verified improvement from the `8/33` local Fourier scale to `2/15`.

We prove a uniform local minor-arc $L^2$ estimate for the von Mangoldt exponential sum on every frequency interval of length $1/H$, valid for $H\ge X^{2/15+\varepsilon}$. This improves the $8/33$ scale in the Matomäki–Radziwiłł–Tao machinery for averaged shifted-prime correlations. The integral covers the minor-arc portion of each interval, and its center may lie anywhere on the circle.

**Paper:** [Prime Pairs at the Prime Number Theorem Threshold](paper/prime-pairs-pnt-threshold.pdf) ([TeX](paper/prime-pairs-pnt-threshold.tex)). This repository formalizes Theorem 1.1 of that paper.

- **Previous relevant scale:** `8/33 ≈ 0.2424`
- **New scale:** `2/15 ≈ 0.1333`
- **Verification:** Lean `v4.35.0-rc2` build and standard-axiom audit passed for [`AllCenterMAP.map_two_fifteenths`](Challenge.lean). [Records](VERIFICATION.md) · [Public checks](https://github.com/jconorgrogan/prime-minor-arcs-2-15/actions/workflows/release.yml).

## The estimate

This repository contains a complete Lean proof of a uniform local minor-arc $L^{2}$ estimate for

```math
S_X(\alpha)=\sum_{\lfloor X\rfloor\lt n\le\lfloor 2X\rfloor}\Lambda(n)e^{2\pi i n\alpha}.
```

Write $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ with normalized Haar measure. For positive integers $B,D$, let $\mathfrak{M}\_{B,D}(X)$ be the union of the neighborhoods $\mathrm{dist}(\alpha,a/q)\le(\log X)^{D}/X$ over reduced fractions $a/q$ with $1\le q\le(\log X)^{B}$, and write $\mathfrak{m}\_{B,D}(X)=\mathbb{T}\setminus\mathfrak{M}\_{B,D}(X)$.

### Theorem

For every $A\gt 0$ and $\varepsilon\gt 0$, there exist integers $B,D\ge 1$ and constants $C\gt 0$, $X\_{0}\ge 2$ such that for every $X\ge X\_{0}$, every

```math
H\ge X^{2/15+\varepsilon},
```

and **every** center $\alpha\_{0}\in\mathbb{T}$,

```math
\int_{\overline{B}(\alpha_0,\,1/(2H))\cap\mathfrak{m}_{B,D}(X)}
|S_X(\alpha)|^2\,d\alpha
\le C X(\log X)^{-A}.
```

The parameters $B,D,C,X\_{0}$ are chosen before $X$, $H$, and $\alpha\_{0}$. There is no exceptional set of centers. The measure is not rescaled by the length of the local arc. The constants are ineffective because the proof uses Siegel's theorem.

The formal statement is [`AllCenterMAP.map_two_fifteenths`](Challenge.lean). The fully expanded major-arc definition is in [STATEMENT.md](STATEMENT.md).

## Why `2/15` matters

Local minor-arc estimates of this type are a Fourier-analytic input in the study of shifted correlations of primes.

The Matomäki–Radziwiłł–Tao machinery obtains the corresponding local minor-arc control at the scale

```math
H\ge X^{8/33+\varepsilon},\qquad \frac{8}{33}\approx 0.2424.
```

The theorem proved here reaches

```math
H\ge X^{2/15+\varepsilon},\qquad \frac{2}{15}\approx 0.1333.
```

The frequency-window length is $1/H$. A smaller admissible $H$ therefore reaches substantially wider frequency windows, and shorter shift-averaging intervals.

The $2/15$ threshold is the local scale that the Guth–Maynard large-value estimates for Dirichlet polynomials make available for this argument. The main step in the development is carrying that strength through to an **all-center local minor-arc $L^{2}$ estimate for the von Mangoldt exponential sum**.

## Formal verification

The development contains 1,861 Lean modules. The current Lean `v4.35.0-rc2` build of `Challenge`, `Solution` and `SolutionAxiomAudit` passed on macOS ARM, completing a 10,797-job build graph. The [build and axiom evidence](VERIFICATION.md#lean-435-build) records the exact toolchain and result.

The Linux verification pipeline compares the proof with the independently stated [Challenge](Challenge.lean), then checks the exported proof with Lean's kernel and the independent NanoDa and con-ron kernels. The official Palomar preflight also compiles the Challenge against protected, canonical dependencies.

The proof uses only Lean's standard axioms: `propext`, `Quot.sound`, and `Classical.choice`.

The September 20, 2026 Lean 4.30 release passed a fresh Linux build, Comparator and NanoDa checks. Its MAP closure of 100,596 declarations passed a fresh Lean kernel replay. Those records retain their original toolchain and source hashes in [VERIFICATION.md](VERIFICATION.md). The current Lean 4.35 checks run at each public commit in [Palomar release checks](https://github.com/jconorgrogan/prime-minor-arcs-2-15/actions/workflows/release.yml); [RELEASE_STATUS.md](RELEASE_STATUS.md) identifies the release evidence.

## Guth–Maynard large-value theorem

A substantial component of the development is an internal proof of the epsilon-form of Guth and Maynard's large-value estimate for Dirichlet polynomials. The closed theorem [`GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11`](Proof/GuthMaynardActualEndpointWeakTheta.lean) is derived from the proved local estimate [`GuthMaynardProp31Actual.actual_fixedWeightProp31`](Proof/GuthMaynardProp31Actual.lean), not from a Guth–Maynard axiom.

For every $\eta\gt 0$, there are constants $C\gt 0$ and $T\_{0}\ge 2$ such that the following holds uniformly for $T\ge T\_{0}$, $V\gt 0$, $N\ge 1$, coefficients $|b\_{n}|\le 1$, and any one-separated finite set $W\subset[0,T]$ on which

```math
\Bigl|\sum_{N\lt n\le 2N} b_n e^{it\log n}\Bigr|\ge V:
```

```math
|W|
\le
C T^\eta
\Bigl(
\frac{N^2}{V^2}
+\frac{N^{18/5}}{V^4}
+\frac{T N^{12/5}}{V^4}
\Bigr).
```

Its September 20, 2026 Lean 4.30 dependency closure of 75,874 declarations passed the same kernel replay with the same three axioms. Details are in [GUTH_MAYNARD.md](GUTH_MAYNARD.md).

## Mathematical context

The main source families are:

- **Guth–Maynard** — large-value estimates for Dirichlet polynomials, proved internally here
- **Matomäki–Radziwiłł–Tao** — short-interval and shifted-correlation machinery
- **Ford** — exponential-sum and zeta-function estimates
- **Chen–Gupta–Li** — character large values and zero-density estimates

See [PROVENANCE.md](PROVENANCE.md) for the source map.

## Repository map

- [paper/prime-pairs-pnt-threshold.pdf](paper/prime-pairs-pnt-threshold.pdf) — companion paper
- [STATEMENT.md](STATEMENT.md) — precise mathematical statement
- [Challenge.lean](Challenge.lean) — compact formal theorem
- [Solution.lean](Solution.lean) — proof entry point
- [Proof/](Proof/) — substantive Lean development
- [GUTH_MAYNARD.md](GUTH_MAYNARD.md) — internal Guth–Maynard theorem
- [VERIFICATION.md](VERIFICATION.md) — verification procedure and records
- [RELEASE_STATUS.md](RELEASE_STATUS.md) — current release status
- [PROVENANCE.md](PROVENANCE.md) — source and citation map
- [MANUSCRIPT_ALIGNMENT.md](MANUSCRIPT_ALIGNMENT.md) — statement/manuscript alignment
- [PROOF_OPTIMIZATION.md](PROOF_OPTIMIZATION.md) — proof-term optimization record

## Reproducibility

The project uses Lean `v4.35.0-rc2` and Mathlib commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`. Verification artifacts are under `evidence/`. Released under Apache-2.0.
