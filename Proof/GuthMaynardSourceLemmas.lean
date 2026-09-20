import CGLProofDAG

/-!
# Source-faithful elementary leaves for Guth--Maynard Theorem 1.1

This file does not postulate Theorem 1.1.  It proves two pieces that occur on
the literal source path:

* the displayed theorem uses `N <= n <= 2N`, whereas the paper's background
  convention and the project use `N < n <= 2N`; the project polynomial is the
  exact endpoint-zero specialization, and its local coefficient can then be
  extended by zero to the globally bounded coefficient interface currently
  used by `CGLProofDAG.GuthMaynardTheorem11`;
* after the source's equation (12.1) is specialized to `T = N^(6/5)` and
  `k = 4`, every one of its seven displayed powers is bounded by the exponent
  in Proposition 3.1 for `7/10 <= sigma <= 4/5`.

Thus the first remaining input in this branch is the analytic inequality
(12.1), not another proposition-valued spelling of Theorem 1.1.
-/

namespace GuthMaynardSource

open scoped BigOperators
open CGLProofDAG

noncomputable section

/-! ## Exact endpoint and localization of the coefficient hypothesis -/

/-- The displayed sum in Guth--Maynard Theorem 1.1 includes both endpoints.
This intentionally differs from `CGLProofDAG.dirichletPolynomial`, which uses
the paper's background convention `N < n <= 2N`. -/
noncomputable def displayedDirichletPolynomial
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc N (2 * N),
    b n * Complex.exp (Complex.I * (t * Real.log n))

/-- Set the displayed theorem's lower endpoint coefficient to zero. -/
def lowerEndpointZero (N : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n = N then 0 else b n

/-- The project polynomial is exactly the endpoint-zero specialization of the
displayed Theorem 1.1 polynomial. -/
theorem displayedDirichletPolynomial_lowerEndpointZero
    (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    displayedDirichletPolynomial (lowerEndpointZero N b) N t =
      dirichletPolynomial b N t := by
  unfold displayedDirichletPolynomial dirichletPolynomial
  rw [Finset.Icc_eq_cons_Ioc (show N ≤ 2 * N by omega)]
  simp only [Finset.sum_cons, lowerEndpointZero, if_pos, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro n hn
  have hnN : n ≠ N := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  simp [hnN]

/-- Extend a coefficient sequence on the project range `N < n <= 2N` by zero. -/
def dyadicRestriction (N : ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ Finset.Ioc N (2 * N) then b n else 0

/-- The source's local `l-infinity` coefficient condition becomes the global
condition required by the existing Lean interface after zero extension. -/
theorem norm_dyadicRestriction_le_one
    {N : ℕ} {b : ℕ → ℂ}
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) (n : ℕ) :
    ‖dyadicRestriction N b n‖ ≤ 1 := by
  unfold dyadicRestriction
  split_ifs with hn
  · exact hb n hn
  · simp

/-- Zero extension is value preserving for the exact Dirichlet polynomial;
no coefficient outside the source range is observed. -/
theorem dirichletPolynomial_dyadicRestriction
    (N : ℕ) (b : ℕ → ℂ) (t : ℝ) :
    dirichletPolynomial (dyadicRestriction N b) N t =
      dirichletPolynomial b N t := by
  unfold dirichletPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  simp [dyadicRestriction, hn]

/-! ## Fixed-character specialization is formally free, but not stronger -/

/-- Absorb one fixed Dirichlet character into the arbitrary coefficient
sequence, exactly as required by the powered Type-I branch. -/
def fixedCharacterCoefficient {q : ℕ} (χ : DirichletCharacter ℂ q)
    (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  χ n * b n

/-- A fixed character preserves the unit coefficient ball.  This is the whole
source-level specialization: Theorem 1.1 is already uniform over arbitrary
complex coefficients, so fixed-character structure yields no cheaper analytic
claim in the paper. -/
theorem norm_fixedCharacterCoefficient_le_one
    {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℕ → ℂ}
    (hb : ∀ n, ‖b n‖ ≤ 1) (n : ℕ) :
    ‖fixedCharacterCoefficient χ b n‖ ≤ 1 := by
  rw [fixedCharacterCoefficient, norm_mul]
  simpa using
    (mul_le_mul (χ.norm_le_one n) (hb n) (norm_nonneg _) (by norm_num))

/-! ## The seven literal powers after (12.1) -/

/-- Exponents of the seven terms displayed after substituting `T = N^(6/5)`
and choosing `k = 4` in Guth--Maynard equation (12.1), in source order. -/
def equation12_1Exponent (σ : ℝ) : Fin 7 → ℝ
  | 0 => 6 / 5 + (4 - 10 * σ) / 5
  | 1 => (19 - 30 * σ) / 5
  | 2 => (74 - 120 * σ) / 25
  | 3 => (298 - 480 * σ) / 95
  | 4 => (12 - 20 * σ) / 5
  | 5 => (9 - 14 * σ) / 2
  | 6 => (354 - 560 * σ) / 95

/-- Exponent of the Proposition 3.1 target after `T = N^(6/5)` is absorbed. -/
def proposition31Exponent (σ : ℝ) : ℝ :=
  (18 - 20 * σ) / 5

/-- Every literal post-(12.1) term is dominated by the Proposition 3.1 target
throughout the exact source range.  This certifies the source's phrase "the
first and third terms can be dropped" without silently losing the other four
terms. -/
theorem equation12_1Exponent_le_proposition31Exponent
    {σ : ℝ} (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) (i : Fin 7) :
    equation12_1Exponent σ i ≤ proposition31Exponent σ := by
  fin_cases i <;>
    simp [equation12_1Exponent, proposition31Exponent] <;>
    nlinarith

/-- Consequently the sum of the seven source powers costs only the explicit
factor `7`.  This is the finite, constant-sensitive version of the last
exponent comparison in the proof of Proposition 3.1. -/
theorem equation12_1_rpow_sum_le
    {N : ℝ} {σ : ℝ} (hN : 1 ≤ N)
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5) :
    (∑ i : Fin 7, Real.rpow N (equation12_1Exponent σ i)) ≤
      7 * Real.rpow N (proposition31Exponent σ) := by
  calc
    (∑ i : Fin 7, Real.rpow N (equation12_1Exponent σ i)) ≤
        ∑ _i : Fin 7, Real.rpow N (proposition31Exponent σ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow_of_exponent_le hN
        (equation12_1Exponent_le_proposition31Exponent hσlow hσhigh i)
    _ = 7 * Real.rpow N (proposition31Exponent σ) := by simp

/-- The absorbed target exponent is exactly the source expression
`T * N^((12-20*sigma)/5)` when `T = N^(6/5)`. -/
theorem proposition31_scale_identity
    {N σ : ℝ} (hN : 0 < N) :
    Real.rpow N (proposition31Exponent σ) =
      Real.rpow N (6 / 5 : ℝ) * Real.rpow N ((12 - 20 * σ) / 5) := by
  calc
    Real.rpow N (proposition31Exponent σ) =
        Real.rpow N ((6 / 5 : ℝ) + (12 - 20 * σ) / 5) := by
      congr 1
      unfold proposition31Exponent
      ring
    _ = Real.rpow N (6 / 5 : ℝ) *
        Real.rpow N ((12 - 20 * σ) / 5) := Real.rpow_add hN _ _

/-- Exact deterministic assembly after the deep analytic estimate (12.1).
The hypotheses retain the source epsilon loss and its constant. -/
theorem proposition31_bound_of_equation12_1
    {C T η N σ R : ℝ}
    (hC : 0 ≤ C) (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (h12_1 : R ≤ C * Real.rpow T η *
      (∑ i : Fin 7, Real.rpow N (equation12_1Exponent σ i))) :
    R ≤ 7 * C * Real.rpow T η *
      Real.rpow N (proposition31Exponent σ) := by
  calc
    R ≤ C * Real.rpow T η *
        (∑ i : Fin 7, Real.rpow N (equation12_1Exponent σ i)) := h12_1
    _ ≤ C * Real.rpow T η *
        (7 * Real.rpow N (proposition31Exponent σ)) := by
      apply mul_le_mul_of_nonneg_left
        (equation12_1_rpow_sum_le hN hσlow hσhigh)
      exact mul_nonneg hC (Real.rpow_nonneg hT η)
    _ = 7 * C * Real.rpow T η *
        Real.rpow N (proposition31Exponent σ) := by ring

end

end GuthMaynardSource

#print axioms GuthMaynardSource.norm_dyadicRestriction_le_one
#print axioms GuthMaynardSource.displayedDirichletPolynomial_lowerEndpointZero
#print axioms GuthMaynardSource.dirichletPolynomial_dyadicRestriction
#print axioms GuthMaynardSource.norm_fixedCharacterCoefficient_le_one
#print axioms GuthMaynardSource.equation12_1Exponent_le_proposition31Exponent
#print axioms GuthMaynardSource.equation12_1_rpow_sum_le
#print axioms GuthMaynardSource.proposition31_scale_identity
#print axioms GuthMaynardSource.proposition31_bound_of_equation12_1
