import MRTProposition61TypeIIGlobalFilteredAnalyticV3
import FixedCharacterPoweredBridge

/-! # Subpower control of the exact modulus-divisor normalization -/

namespace MRTProposition61TypeIIDivisorNormalizationV3

open MAPMRTCorollary53Source RamachandraShiftedCoefficientEnergy
open FixedCharacterPoweredBridge

noncomputable section

/-- The fourth power of the literal Corollary-5.3 divisor factor is
subpower in the modulus.  This avoids the fatal crude estimate `d(q) ≤ q`. -/
theorem exists_divisorCount_four_subpower
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      (divisorCount q : ℝ) ^ 4 ≤
        (C * Real.rpow q e) ^ 4 := by
  obtain ⟨C, hC, hbound⟩ :=
    orderedDivisorCount_subpolynomial 2 (by omega) e he
  refine ⟨C, hC, ?_⟩
  intro q hq
  have hq0 : q ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_of_lt hq)
  have hid : divisorCount q = CGLProofDAG.orderedDivisorCount 2 q := by
    unfold divisorCount
    exact (orderedDivisorCount_two_eq_card_divisors hq0).symm
  rw [hid]
  exact pow_le_pow_left₀ (by positivity) (hbound q (Nat.zero_lt_of_lt hq)) 4

/-- The exponent here applies to the complete fourth-power divisor loss,
not to a fourth root.  The constant is chosen before the modulus. -/
theorem exists_divisorCount_four_le_subpower
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 1 ≤ q →
      (divisorCount q : ℝ) ^ 4 ≤ C * Real.rpow q e := by
  obtain ⟨C, hC, hbound⟩ := exists_divisorCount_four_subpower
    (e / 4) (by positivity)
  refine ⟨C ^ 4, by positivity, ?_⟩
  intro q hq
  have hrpow : (Real.rpow (q : ℝ) (e / 4)) ^ 4 =
      Real.rpow (q : ℝ) e := by
    calc
      _ = Real.rpow (Real.rpow (q : ℝ) (e / 4)) (4 : ℝ) :=
        (Real.rpow_natCast _ 4).symm
      _ = Real.rpow (q : ℝ) ((e / 4) * 4) :=
        (Real.rpow_mul (by positivity : 0 ≤ (q : ℝ)) _ _).symm
      _ = Real.rpow (q : ℝ) e := by congr 1; ring
  simpa only [mul_pow, hrpow] using hbound q hq

/-- A uniform modulus range preserves the same subpower constant. -/
theorem exists_divisorCount_four_le_range_subpower
    (e : ℝ) (he : 0 < e) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) (Q : ℝ), 1 ≤ q → (q : ℝ) ≤ Q →
      (divisorCount q : ℝ) ^ 4 ≤ C * Real.rpow Q e := by
  obtain ⟨C, hC, hbound⟩ := exists_divisorCount_four_le_subpower e he
  refine ⟨C, hC, ?_⟩
  intro q Q hq hqQ
  exact (hbound q hq).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hqQ he.le) hC.le)

end
end MRTProposition61TypeIIDivisorNormalizationV3

#print axioms MRTProposition61TypeIIDivisorNormalizationV3.exists_divisorCount_four_subpower

#print axioms MRTProposition61TypeIIDivisorNormalizationV3.exists_divisorCount_four_le_subpower
#print axioms MRTProposition61TypeIIDivisorNormalizationV3.exists_divisorCount_four_le_range_subpower
