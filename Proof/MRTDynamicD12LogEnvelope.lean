import MRTProposition61HighEnvelopeSplitV3

namespace MRTDynamicD12LogEnvelope

open MAPHBPerronSourceData MAPMRTCorollary25Minkowski
open MRTProposition61HighEnvelopeSplitV3

noncomputable section

/-- The moment logarithm costs a fixed constant raised to the fixed moment
exponent; it introduces no dependence on the later logarithmic parameter B. -/
theorem moment_log_pow_le {X : ℝ} (hX : 3 ≤ X)
    (hlog : 1 ≤ Real.log X) (E : ℕ) :
    (1 + Real.log (8 * X)) ^ E ≤ 5 ^ E * Real.log X ^ E := by
  have hXpos : 0 < X := by linarith
  have hlog8 : Real.log (8 : ℝ) ≤ 3 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
      norm_num
    linarith
  have hbase : 1 + Real.log (8 * X) ≤ 5 * Real.log X := by
    rw [Real.log_mul (by norm_num) hXpos.ne']
    linarith
  have hbase0 : 0 ≤ 1 + Real.log (8 * X) := by
    have hl := Real.log_nonneg (show (1 : ℝ) ≤ 8 * X by linarith)
    linarith
  calc
    _ ≤ (5 * Real.log X) ^ E := pow_le_pow_left₀ hbase0 hbase E
    _ = _ := mul_pow _ _ _

/-- Both literal Perron logarithms are bounded at once, before choosing B. -/
theorem perron_logs_sq_le {X P : ℝ} (hX : 3 ≤ X)
    (hlog : 1 ≤ Real.log X) (hP : 0 ≤ P) (hPX : P ≤ X) :
    (∫ u in (-P)..P, perronWeight u) ^ 2 ≤ 36 * Real.log X ^ 2 ∧
      Real.log (2 + P) ^ 2 ≤ 9 * Real.log X ^ 2 := by
  obtain ⟨h1nonneg, h1⟩ := log_one_add_truncation_le hX hlog hP hPX
  obtain ⟨h2nonneg, h2⟩ := log_two_add_truncation_le hX hlog hP hPX
  have hs1 := pow_le_pow_left₀ h1nonneg h1 2
  have hs2 := pow_le_pow_left₀ h2nonneg h2 2
  rw [integral_perronWeight hP]
  constructor <;> nlinarith

end
end MRTDynamicD12LogEnvelope

#print axioms MRTDynamicD12LogEnvelope.moment_log_pow_le
#print axioms MRTDynamicD12LogEnvelope.perron_logs_sq_le
