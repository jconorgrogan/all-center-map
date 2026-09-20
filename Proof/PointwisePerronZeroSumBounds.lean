import PrimitiveTruncatedExplicitFormulaBridge

/-!
# Pointwise bounds for the Perron zero sum

The pointwise Siegel--Walfisz consumer uses the literal Perron residue sum,
whereas the AP endpoint consumer uses an endpoint/Perron mismatch.  This file
keeps those routes separate and proves the exact pointwise finite-sum bounds.
-/

namespace PointwisePerronZeroSumBounds

open Set
open scoped BigOperators
open DirichletZeros PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- Triangle inequality for the literal multiplicity-weighted Perron zero
sum, preserving each zero's real part and its exact denominator. -/
theorem norm_multiplicityWeightedPerronZeroSum_le_weighted
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T x : ℝ} (hx : 0 < x) :
    ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
      ∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℝ) *
          x ^ rho.re / ‖rho‖ := by
  unfold multiplicityWeightedPerronZeroSum
  calc
    ‖∑ rho ∈ zeroSupport chi sigma T,
        (zeroMultiplicity chi sigma T rho : ℂ) *
          (x : ℂ) ^ rho / rho‖
        ≤ ∑ rho ∈ zeroSupport chi sigma T,
            ‖(zeroMultiplicity chi sigma T rho : ℂ) *
              (x : ℂ) ^ rho / rho‖ := norm_sum_le _ _
    _ = ∑ rho ∈ zeroSupport chi sigma T,
          (zeroMultiplicity chi sigma T rho : ℝ) *
            x ^ rho.re / ‖rho‖ := by
      apply Finset.sum_congr rfl
      intro rho hrho
      rw [norm_div, norm_mul, norm_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]

/-- The support condition `Re rho ≥ sigma` controls every Perron
denominator by the literal positive left edge. -/
theorem norm_multiplicityWeightedPerronZeroSum_le_weighted_div_sigma
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T x : ℝ} (hx : 0 < x) (hsigma : 0 < sigma) :
    ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
      ∑ rho ∈ zeroSupport chi sigma T,
        ((zeroMultiplicity chi sigma T rho : ℝ) * x ^ rho.re) / sigma := by
  refine (norm_multiplicityWeightedPerronZeroSum_le_weighted chi hx).trans ?_
  apply Finset.sum_le_sum
  intro rho hrho
  have hre : sigma ≤ rho.re :=
    (mem_zeroRectangle_of_mem_zeroSupport chi sigma T hrho).1.1
  have hden : sigma ≤ ‖rho‖ := by
    calc
      sigma ≤ |rho.re| := by
        rw [abs_of_nonneg (hsigma.le.trans hre)]
        exact hre
      _ ≤ ‖rho‖ := Complex.abs_re_le_norm rho
  exact div_le_div_of_nonneg_left
    (mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx.le _))
    hsigma hden

/-- A pointwise zero-free gap turns the exact Perron zero sum into the
standard `x^(1-omega)` zero-count majorant.  The height `T` remains quantified
for this one character and endpoint; no family-wide height is asserted. -/
theorem norm_multiplicityWeightedPerronZeroSum_le_of_gap
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T x omega : ℝ} (hx : 1 ≤ x) (hsigma : 0 < sigma)
    (hgap : ∀ rho ∈ zeroSupport chi sigma T,
      rho.re ≤ 1 - omega) :
    ‖multiplicityWeightedPerronZeroSum chi sigma T x‖ ≤
      ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
        x ^ (1 - omega) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  refine
    (norm_multiplicityWeightedPerronZeroSum_le_weighted_div_sigma
      chi hx0 hsigma).trans ?_
  calc
    ∑ rho ∈ zeroSupport chi sigma T,
        ((zeroMultiplicity chi sigma T rho : ℝ) * x ^ rho.re) / sigma
        ≤ ∑ rho ∈ zeroSupport chi sigma T,
          ((zeroMultiplicity chi sigma T rho : ℝ) *
            x ^ (1 - omega)) / sigma := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply div_le_div_of_nonneg_right _ hsigma.le
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx (hgap rho hrho))
        (Nat.cast_nonneg _)
    _ = ((dirichletZeroCount chi sigma T : ℝ) / sigma) *
          x ^ (1 - omega) := by
      rw [show (∑ rho ∈ zeroSupport chi sigma T,
            ((zeroMultiplicity chi sigma T rho : ℝ) *
              x ^ (1 - omega)) / sigma) =
          ((∑ rho ∈ zeroSupport chi sigma T,
              (zeroMultiplicity chi sigma T rho : ℝ)) / sigma) *
            x ^ (1 - omega) by
        calc
          (∑ rho ∈ zeroSupport chi sigma T,
              ((zeroMultiplicity chi sigma T rho : ℝ) *
                x ^ (1 - omega)) / sigma) =
              ∑ rho ∈ zeroSupport chi sigma T,
                ((zeroMultiplicity chi sigma T rho : ℝ) / sigma) *
                  x ^ (1 - omega) := by
                    apply Finset.sum_congr rfl
                    intro rho hrho
                    ring
          _ = (∑ rho ∈ zeroSupport chi sigma T,
                (zeroMultiplicity chi sigma T rho : ℝ) / sigma) *
                  x ^ (1 - omega) := by rw [Finset.sum_mul]
          _ = ((∑ rho ∈ zeroSupport chi sigma T,
                (zeroMultiplicity chi sigma T rho : ℝ)) / sigma) *
                  x ^ (1 - omega) := by rw [Finset.sum_div]]
      rw [← Nat.cast_sum, sum_zeroMultiplicity_eq_dirichletZeroCount]

end

end PointwisePerronZeroSumBounds
