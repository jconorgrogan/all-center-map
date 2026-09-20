import KoukDigammaAwayFromPoles

/-!
# Quantitative Dirichlet Gamma-factor growth

This is the exact adapter from an away-from-poles digamma estimate to the
archimedean terms in the Dirichlet functional equation.  The pole-clearance
hypotheses remain literal so the contour modules can discharge them from their
own geometry.
-/

namespace KoukGammaFactorGrowthBound

open Complex
open KoukGammaFactorLogDerivative KoukDigammaAwayFromPoles

noncomputable section

/-- The positive-real logarithm of `pi`, viewed in `ℂ`, has a harmless
explicit norm bound. -/
theorem norm_complexLog_pi_le_four :
    ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 := by
  rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.log_pos (by linarith [Real.pi_gt_three]))]
  exact (Real.log_le_self Real.pi_pos.le).trans Real.pi_lt_four.le

/-- Fixed-constant form of the parity-uniform Gamma-factor estimate. -/
theorem norm_logDeriv_gammaFactor_le_fixed
    (C : ℝ) (hC : 0 < C)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hclearEven : ∀ m : ℕ,
      (1 / 4 : ℝ) ≤ ‖s / 2 + (m : ℂ)‖)
    (hclearOdd : ∀ m : ℕ,
      (1 / 4 : ℝ) ≤ ‖(s + 1) / 2 + (m : ℂ)‖) :
    ‖logDeriv (DirichletCharacter.gammaFactor chi) s‖ ≤
      2 + C * Real.log (‖s‖ + 3) := by
  have hscalePos : 0 < ‖s‖ + 3 := by positivity
  have hscaleLog : 0 ≤ Real.log (‖s‖ + 3) :=
    Real.log_nonneg (by linarith [norm_nonneg s])
  rcases chi.even_or_odd with heven | hodd
  · have hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hz : s / 2 + (m : ℂ) = 0 := by linear_combination hm
      have hc := hclearEven m
      rw [hz, norm_zero] at hc
      norm_num at hc
    rw [logDeriv_gammaFactor_of_even chi heven s hpole]
    have hdig := hDigamma (s / 2) hclearEven
    have harg : ‖s / 2‖ + 2 ≤ ‖s‖ + 3 := by
      rw [norm_div]
      norm_num
      linarith [norm_nonneg s]
    have hlog : Real.log (‖s / 2‖ + 2) ≤ Real.log (‖s‖ + 3) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < ‖s / 2‖ + 2 by positivity) hscalePos harg
    have hdig' : ‖Complex.digamma (s / 2)‖ ≤
        C * Real.log (‖s‖ + 3) :=
      hdig.trans (mul_le_mul_of_nonneg_left hlog hC.le)
    calc
      ‖-(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
          (1 / 2 : ℂ) * Complex.digamma (s / 2)‖ ≤
        ‖-(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)‖ +
          ‖(1 / 2 : ℂ) * Complex.digamma (s / 2)‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖Complex.log (Real.pi : ℂ)‖ +
          (1 / 2 : ℝ) * ‖Complex.digamma (s / 2)‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 4 +
          (1 / 2 : ℝ) * (C * Real.log (‖s‖ + 3)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left norm_complexLog_pi_le_four (by norm_num))
          (mul_le_mul_of_nonneg_left hdig' (by norm_num))
      _ ≤ 2 + C * Real.log (‖s‖ + 3) := by
        have hCL : 0 ≤ C * Real.log (‖s‖ + 3) :=
          mul_nonneg hC.le hscaleLog
        linarith
  · have hpole : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
      intro m hm
      have hz : (s + 1) / 2 + (m : ℂ) = 0 := by linear_combination hm
      have hc := hclearOdd m
      rw [hz, norm_zero] at hc
      norm_num at hc
    rw [logDeriv_gammaFactor_of_odd chi hodd s hpole]
    have hdig := hDigamma ((s + 1) / 2) hclearOdd
    have hargNorm : ‖(s + 1) / 2‖ ≤ (‖s‖ + 1) / 2 := by
      rw [norm_div]
      norm_num
      have hsum := norm_add_le s (1 : ℂ)
      norm_num at hsum ⊢
      linarith
    have harg : ‖(s + 1) / 2‖ + 2 ≤ ‖s‖ + 3 := by
      linarith [norm_nonneg s]
    have hlog : Real.log (‖(s + 1) / 2‖ + 2) ≤
        Real.log (‖s‖ + 3) :=
      Real.strictMonoOn_log.monotoneOn
        (show 0 < ‖(s + 1) / 2‖ + 2 by positivity) hscalePos harg
    have hdig' : ‖Complex.digamma ((s + 1) / 2)‖ ≤
        C * Real.log (‖s‖ + 3) :=
      hdig.trans (mul_le_mul_of_nonneg_left hlog hC.le)
    calc
      ‖-(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
          (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2)‖ ≤
        ‖-(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ)‖ +
          ‖(1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2)‖ := norm_add_le _ _
      _ = (1 / 2 : ℝ) * ‖Complex.log (Real.pi : ℂ)‖ +
          (1 / 2 : ℝ) * ‖Complex.digamma ((s + 1) / 2)‖ := by
        simp only [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
        norm_num
      _ ≤ (1 / 2 : ℝ) * 4 +
          (1 / 2 : ℝ) * (C * Real.log (‖s‖ + 3)) :=
        add_le_add
          (mul_le_mul_of_nonneg_left norm_complexLog_pi_le_four (by norm_num))
          (mul_le_mul_of_nonneg_left hdig' (by norm_num))
      _ ≤ 2 + C * Real.log (‖s‖ + 3) := by
        have hCL : 0 ≤ C * Real.log (‖s‖ + 3) :=
          mul_nonneg hC.le hscaleLog
        linarith

/-- An away-from-poles digamma estimate gives a parity-uniform logarithmic
bound for the exact Dirichlet Gamma-factor logarithmic derivative. -/
theorem norm_logDeriv_gammaFactor_le_of_awayFromPoles
    (hDigamma : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hclearEven : ∀ m : ℕ,
      (1 / 4 : ℝ) ≤ ‖s / 2 + (m : ℂ)‖)
    (hclearOdd : ∀ m : ℕ,
      (1 / 4 : ℝ) ≤ ‖(s + 1) / 2 + (m : ℂ)‖) :
    ∃ C : ℝ, 0 < C ∧
      ‖logDeriv (DirichletCharacter.gammaFactor chi) s‖ ≤
        2 + C * Real.log (‖s‖ + 3) := by
  obtain ⟨C, hC, hbound⟩ := hDigamma
  exact ⟨C, hC, norm_logDeriv_gammaFactor_le_fixed
    C hC hbound chi s hclearEven hclearOdd⟩

end

end KoukGammaFactorGrowthBound

#print axioms KoukGammaFactorGrowthBound.norm_logDeriv_gammaFactor_le_of_awayFromPoles
#print axioms KoukGammaFactorGrowthBound.norm_logDeriv_gammaFactor_le_fixed
