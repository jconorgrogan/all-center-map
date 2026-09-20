import MRTProposition61TypeIIParameterAbsorptionV3
import MRTProposition61HighTruncationParametersV3

/-! # The free Perron shift retains the actual outer annulus -/

namespace MRTProposition61HighAnnulusPreservationV3

open Filter
open MRTProposition61TypeIIParameterAbsorptionV3

noncomputable section

/-- The threshold precedes the frequency parameter `lambda`, including
frequencies at the bottom of the far range. -/
theorem eventually_freeTruncation_le_quarter_innerRadius
    (B : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) :
    ∀ᶠ X : ℝ in atTop, ∀ lambda : ℝ, 0 ≤ lambda →
      lambda * Real.rpow X (1 - sigma) ≤
        lambda * X / (4 * Real.sqrt ((Real.log X) ^ B)) := by
  have hsmall := eventually_const_polylog_mul_neg_rpow_le_log_decay
    4 ((B : ℝ) / 2) 0 sigma (by norm_num) hsigma
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with X hb hX
  intro lambda hlambda
  have hX0 : 0 < X := by linarith
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hsqrt : Real.sqrt ((Real.log X) ^ B) =
      Real.rpow (Real.log X) ((B : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [Real.rpow_eq_pow, div_eq_mul_inv, one_mul] using
      (Real.rpow_natCast_mul hlog.le B (1 / 2 : ℝ)).symm
  have hs : 0 < Real.sqrt ((Real.log X) ^ B) := Real.sqrt_pos.2 (pow_pos hlog _)
  have hb' : Real.rpow X (-sigma) ≤ 1 / (4 * Real.sqrt ((Real.log X) ^ B)) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hs)).2
    rw [hsqrt]
    have hb1 : 4 * Real.rpow (Real.log X) ((B : ℝ) / 2) * Real.rpow X (-sigma) ≤ 1 := by
      simpa only [Real.rpow_eq_pow, neg_zero, Real.rpow_zero] using hb
    nlinarith only [hb1]
  calc
    _ = (lambda * X) * Real.rpow X (-sigma) := by
      have he := Real.rpow_add hX0 (1 : ℝ) (-sigma)
      simp only [Real.rpow_one] at he
      have he' : Real.rpow X (1 - sigma) = X * Real.rpow X (-sigma) := by
        simpa only [sub_eq_add_neg, Real.rpow_eq_pow] using he
      rw [he']
      ring
    _ ≤ (lambda * X) * (1 / (4 * Real.sqrt ((Real.log X) ^ B))) :=
      mul_le_mul_of_nonneg_left hb' (mul_nonneg hlambda hX0.le)
    _ = _ := by ring

/-- Both shifts, Perron `T` and stationary `U`, together consume at most
half of the actual inner annular radius. -/
theorem eventually_freeTruncation_add_width_le_half_innerRadius
    (B : ℕ) (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaUpper : sigma ≤ 1 / 24) :
    ∀ᶠ X : ℝ in atTop, ∀ (lambda reserve : ℝ),
      0 ≤ lambda → reserve ≤ 1 / 1200 →
      lambda * Real.rpow X (1 - sigma) +
          lambda * ((1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve)) ≤
        lambda * X / (2 * Real.sqrt ((Real.log X) ^ B)) := by
  filter_upwards [eventually_freeTruncation_le_quarter_innerRadius B sigma hsigma,
    eventually_ge_atTop (1 : ℝ)] with X hT hX
  intro lambda reserve hlambda hr
  have hX0 : 0 < X := by linarith
  have hH : (1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve) ≤ Real.rpow X (1 - sigma) := by
    have hp := Real.rpow_le_rpow_of_exponent_le hX
      (show 2 / 15 + reserve ≤ 1 - sigma by linarith)
    have hp0 : 0 ≤ Real.rpow X (2 / 15 + reserve) := Real.rpow_nonneg hX0.le _
    have hp' : Real.rpow X (2 / 15 + reserve) ≤ Real.rpow X (1 - sigma) := hp
    linarith
  have hU := mul_le_mul_of_nonneg_left hH hlambda
  have hquarter := hT lambda hlambda
  calc
    _ ≤ 2 * (lambda * X / (4 * Real.sqrt ((Real.log X) ^ B))) := by linarith
    _ = _ := by ring

end
end MRTProposition61HighAnnulusPreservationV3

#print axioms MRTProposition61HighAnnulusPreservationV3.eventually_freeTruncation_add_width_le_half_innerRadius
