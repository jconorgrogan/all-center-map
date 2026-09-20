import MRTProposition61TypeIIParameterAbsorptionV3

/-! # Uniform logarithmic budget for the three high-packet losses -/

namespace MRTProposition61HighPolylogBudgetV3

open Filter Asymptotics
open MRTProposition61TypeIIParameterAbsorptionV3

noncomputable section

set_option maxHeartbeats 1200000

theorem eventually_const_log_power_le_decay
    (C k A : ℝ) (hk : k < -A) :
    ∀ᶠ X : ℝ in atTop,
      C * Real.rpow (Real.log X) k ≤ Real.rpow (Real.log X) (-A) := by
  have hgap : 0 < -A - k := by linarith
  have hscale := ((tendsto_rpow_atTop hgap).comp Real.tendsto_log_atTop).eventually
    (eventually_ge_atTop C)
  filter_upwards [hscale, eventually_gt_atTop (1 : ℝ)] with X hscale hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  calc
    _ ≤ Real.rpow (Real.log X) (-A - k) * Real.rpow (Real.log X) k :=
      mul_le_mul_of_nonneg_right hscale (Real.rpow_nonneg hlog.le _)
    _ = Real.rpow (Real.log X) (-A) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hlog]
      congr 1
      ring

/-- Increasing `B` or the far exponent is permitted, so these choices can
be shared with the other source budgets.  The constant and logarithmic
exponent are fixed before all uniform input variables. -/
theorem eventually_four_high_log_terms_le_thirtieth
    (C P A delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop,
          C * (Real.rpow (Real.log X) (P + 9 * (B : ℝ) / 8) *
              Real.rpow X (-delta) +
            Real.rpow (Real.log X) (P - 3 * (B : ℝ) / 8) +
            Real.rpow (Real.log X) (P + 9 * (B : ℝ) / 8 - Cc) +
            Real.rpow (Real.log X) (P + 13 * (B : ℝ) / 8) *
              Real.rpow X (-(1 / 2 : ℝ))) ≤
            Real.rpow (Real.log X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ := exists_nat_gt ((8 / 3 : ℝ) * (P + A + 1))
  refine ⟨B₀, ?_⟩
  intro B hB
  have hB' : (B₀ : ℝ) ≤ B := by exact_mod_cast hB
  have hBexp : P - 3 * (B : ℝ) / 8 < -A := by linarith
  obtain ⟨Cc₀, hCc₀⟩ := exists_nat_gt (P + 9 * (B : ℝ) / 8 + A + 1)
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  have hCc' : (Cc₀ : ℝ) ≤ Cc := by exact_mod_cast hCc
  have hCcexp : P + 9 * (B : ℝ) / 8 - Cc < -A := by linarith
  have h1 := eventually_const_polylog_mul_neg_rpow_le_log_decay
    (120 * C) (P + 9 * (B : ℝ) / 8) A delta (by positivity) hdelta
  have h2 := eventually_const_log_power_le_decay
    (120 * C) (P - 3 * (B : ℝ) / 8) A hBexp
  have h3 := eventually_const_log_power_le_decay
    (120 * C) (P + 9 * (B : ℝ) / 8 - Cc) A hCcexp
  have h4 := eventually_const_polylog_mul_neg_rpow_le_log_decay
    (120 * C) (P + 13 * (B : ℝ) / 8) A (1 / 2) (by positivity) (by norm_num)
  filter_upwards [h1, h2, h3, h4] with X h1 h2 h3 h4
  linarith

/-- The scalar source envelope is bounded by the four logarithmic terms,
retaining the literal modulus range and far-width lower bound. -/
theorem high_scalar_envelope_le_four_log_terms
    {X U C P delta : ℝ} (B Cc : ℕ)
    (hX : 1 < X) (hC : 0 ≤ C)
    (hU : (Real.log X) ^ Cc ≤ U) :
    let Q := (Real.log X) ^ B
    C * Real.rpow (Real.log X) P *
      (Real.rpow Q (1 / 8 : ℝ) *
          (Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U) +
        Real.rpow Q (13 / 8 : ℝ) * Real.rpow X (-(1 / 2 : ℝ))) ≤
      C * (Real.rpow (Real.log X) (P + 9 * (B : ℝ) / 8) *
          Real.rpow X (-delta) +
        Real.rpow (Real.log X) (P - 3 * (B : ℝ) / 8) +
        Real.rpow (Real.log X) (P + 9 * (B : ℝ) / 8 - Cc) +
        Real.rpow (Real.log X) (P + 13 * (B : ℝ) / 8) *
          Real.rpow X (-(1 / 2 : ℝ))) := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hQ (a : ℝ) : Real.rpow ((Real.log X) ^ B) a =
      Real.rpow (Real.log X) ((B : ℝ) * a) := by
    simpa only [Real.rpow_eq_pow] using
      (Real.rpow_natCast_mul hlog.le B a).symm
  have hsqrt : Real.sqrt ((Real.log X) ^ B) =
      Real.rpow (Real.log X) ((B : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [div_eq_mul_inv, Real.rpow_eq_pow, one_mul] using hQ (1 / 2)
  have hQbase : (Real.log X) ^ B = Real.rpow (Real.log X) (B : ℝ) :=
    (Real.rpow_natCast _ B).symm
  have hCcbase : (Real.log X) ^ Cc = Real.rpow (Real.log X) (Cc : ℝ) :=
    (Real.rpow_natCast _ Cc).symm
  have hinv : 1 / U ≤ 1 / (Real.log X) ^ Cc :=
    one_div_le_one_div_of_le (pow_pos hlog _) hU
  have hLP : 0 ≤ Real.rpow (Real.log X) P := Real.rpow_nonneg hlog.le _
  have hQE : 0 ≤ Real.rpow ((Real.log X) ^ B) (1 / 8 : ℝ) :=
    Real.rpow_nonneg (pow_nonneg hlog.le _) _
  dsimp only
  calc
    _ ≤ C * Real.rpow (Real.log X) P *
        (Real.rpow ((Real.log X) ^ B) (1 / 8 : ℝ) *
            ((Real.log X) ^ B * Real.rpow X (-delta) +
              1 / Real.sqrt ((Real.log X) ^ B) + (Real.log X) ^ B / (Real.log X) ^ Cc) +
          Real.rpow ((Real.log X) ^ B) (13 / 8 : ℝ) *
            Real.rpow X (-(1 / 2 : ℝ))) := by
      gcongr
    _ = _ := by
      rw [hQ (1 / 8), hQ (13 / 8), hsqrt, hQbase, hCcbase]
      rw [show P + 9 * (B : ℝ) / 8 = P + (B : ℝ) / 8 + (B : ℝ) by ring,
        show P - 3 * (B : ℝ) / 8 = P + (B : ℝ) / 8 - (B : ℝ) / 2 by ring,
        show (B : ℝ) * (1 / 8) = (B : ℝ) / 8 by ring,
        show (B : ℝ) * (13 / 8) = 13 * (B : ℝ) / 8 by ring]
      simp only [Real.rpow_eq_pow, Real.rpow_add hlog, Real.rpow_sub hlog]
      ring

/-- Final `/30` absorption for the literal scalar source envelope. -/
theorem eventually_high_scalar_envelope_le_thirtieth
    (C P A delta : ℝ) (hC : 0 ≤ C) (hdelta : 0 < delta) :
    ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∃ Cc₀ : ℕ, ∀ Cc : ℕ, Cc₀ ≤ Cc →
        ∀ᶠ X : ℝ in atTop, ∀ U : ℝ, (Real.log X) ^ Cc ≤ U →
          let Q := (Real.log X) ^ B
          C * Real.rpow (Real.log X) P *
            (Real.rpow Q (1 / 8 : ℝ) *
                (Q * Real.rpow X (-delta) + 1 / Real.sqrt Q + Q / U) +
              Real.rpow Q (13 / 8 : ℝ) * Real.rpow X (-(1 / 2 : ℝ))) ≤
            Real.rpow (Real.log X) (-A) / 30 := by
  obtain ⟨B₀, hB₀⟩ := eventually_four_high_log_terms_le_thirtieth C P A delta hC hdelta
  refine ⟨B₀, ?_⟩
  intro B hB
  obtain ⟨Cc₀, hCc₀⟩ := hB₀ B hB
  refine ⟨Cc₀, ?_⟩
  intro Cc hCc
  filter_upwards [hCc₀ Cc hCc, eventually_gt_atTop (1 : ℝ)] with X hbudget hX
  intro U hU
  exact (high_scalar_envelope_le_four_log_terms B Cc hX hC hU).trans hbudget

end
end MRTProposition61HighPolylogBudgetV3

#print axioms MRTProposition61HighPolylogBudgetV3.eventually_four_high_log_terms_le_thirtieth

#print axioms MRTProposition61HighPolylogBudgetV3.eventually_high_scalar_envelope_le_thirtieth
