import GuthMaynardS2ShortGapKernel
import GuthMaynardS2DyadicAssembly

/-! # All-integer short-gap summation for the literal S2 kernel -/

namespace GuthMaynardS2ShortGapMass

open scoped BigOperators
open GuthMaynardS2ShortGapKernel GuthMaynardSectorFactorization
open GuthMaynardS2DyadicAssembly GuthMaynardS1Tail GuthMaynardJIteration

noncomputable section

theorem kernelConstant_nonneg : 0 ≤ kernelConstant := by
  have h := norm_sourceHhat_le (t := 0) (xi := 1) (by norm_num) (by norm_num)
  exact (norm_nonneg _).trans (by simpa using h)

def shortGapMassConstant : ℝ := kernelConstant * integerQuadraticMass

theorem shortGapMassConstant_nonneg : 0 ≤ shortGapMassConstant := by
  apply mul_nonneg kernelConstant_nonneg
  exact tsum_nonneg fun m => by unfold integerQuadraticEnvelope; split_ifs <;> positivity

/-- Both frequency signs are summed absolutely, while m=0 remains omitted. -/
theorem norm_sourceNonzeroFourier_le_short
    {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : |t| ≤ (N : ℝ)) :
    ‖sourceNonzeroFourier N t‖ ≤ shortGapMassConstant / (N : ℝ) ^ 2 := by
  let f : ℤ → ℂ := fun m => if m ≠ 0 then
    GuthMaynardS1Source.sourceHhat t ((m : ℝ) * N) else 0
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hC : 0 ≤ kernelConstant / (N : ℝ) ^ 2 := div_nonneg kernelConstant_nonneg (sq_nonneg _)
  have hmajor : ∀ m : ℤ, ‖f m‖ ≤
      (kernelConstant / (N : ℝ) ^ 2) * integerQuadraticEnvelope m := by
    intro m
    by_cases hm : m = 0
    · simp [f, hm, integerQuadraticEnvelope, hC]
    · have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
      have habs : 1 ≤ |(m : ℝ)| := one_le_abs_intCast hm
      have hscale : (N : ℝ) ≤ |(m : ℝ) * N| := by
        rw [abs_mul, abs_of_pos hNreal]
        nlinarith
      have h := norm_sourceHhat_le (mul_ne_zero hmreal hNreal.ne') (ht.trans hscale)
      simp only [f, if_pos hm]
      apply h.trans_eq
      have he : integerQuadraticEnvelope m = 1 / |(m : ℝ)| ^ 2 := by
        rw [integerQuadraticEnvelope, if_neg hm]
        change |(m : ℝ)| ^ (-2 : ℝ) = 1 / |(m : ℝ)| ^ (2 : ℕ)
        rw [Real.rpow_neg (abs_nonneg _) (2 : ℝ)]
        norm_num
      rw [he, abs_mul, abs_of_pos hNreal, mul_pow]
      ring
  have hsum := summable_integerQuadraticEnvelope.mul_left (kernelConstant / (N : ℝ) ^ 2)
  have hnorm : Summable fun m => ‖f m‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajor hsum
  calc
    _ ≤ ∑' m, ‖f m‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m, (kernelConstant / (N : ℝ) ^ 2) * integerQuadraticEnvelope m :=
      hnorm.tsum_le_tsum hmajor hsum
    _ = _ := by rw [tsum_mul_left]; unfold shortGapMassConstant integerQuadraticMass; ring

/-- The complete sub-N pair sector, including the diagonal, is negligible. -/
theorem sourceShortGapPairMoment_le
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceShortGapPairMoment N W (N : ℝ) ≤
      (W.card : ℝ) ^ 2 * (shortGapMassConstant / (N : ℝ) ^ 2) ^ 2 := by
  unfold sourceShortGapPairMoment
  calc
    _ ≤ ∑ t ∈ W, ∑ u ∈ W, (shortGapMassConstant / (N : ℝ) ^ 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      by_cases h : |t - u| < (N : ℝ)
      · rw [if_pos h]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sourceNonzeroFourier_le_short hN h.le) 2
      · rw [if_neg h]
        positivity
    _ = _ := by simp; ring

end
end GuthMaynardS2ShortGapMass

#print axioms GuthMaynardS2ShortGapMass.norm_sourceNonzeroFourier_le_short
#print axioms GuthMaynardS2ShortGapMass.sourceShortGapPairMoment_le
