import JutilaLemma6ParameterLedger
import PostA5HighStripSplitReductionFromFourthMoment

namespace MAPJutilaLemma6GenericDeltaLedger
open Real Filter
open MAPJutilaLemma6MellinIntegral
open PostA5HighStripSplitReductionFromFourthMoment
noncomputable section

def deltaSaving (δ : ℝ) : ℝ := 2 * δ - 12 * δ ^ 2 - 1 / 560

theorem deltaSaving_280 : deltaSaving (1 / 280) = 51 / 9800 := by
  norm_num [deltaSaving]
theorem deltaSaving_560 : deltaSaving (1 / 560) = 137 / 78400 := by
  norm_num [deltaSaving]

theorem deltaSaving_pos {δ : ℝ} (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280) :
    0 < deltaSaving δ := by
  have hp := mul_nonneg (sub_nonneg.mpr hlo)
    (show 0 ≤ 2 - 12 * (δ + 1 / 560) by linarith)
  dsimp [deltaSaving]
  nlinarith

theorem error_exponent_le {δ beta : ℝ} (hδ : 0 ≤ δ)
    (hbeta : 1 - δ ≤ beta) :
    -(1 + 12 * δ) * beta + (1 / 2 + 8 * δ) + δ + p48HeightExponent ≤
      -deltaSaving δ := by
  have hp := mul_nonneg (show 0 ≤ 1 + 12 * δ by linarith)
    (sub_nonneg.mpr hbeta)
  norm_num [p48HeightExponent, MAPJutilaCollarA5Budget.detectorLogBudget,
    deltaSaving] at *
  nlinarith

theorem error_power_le {D δ beta : ℝ} (hD : 1 ≤ D) (hδ : 0 ≤ δ)
    (hbeta : 1 - δ ≤ beta) :
    Real.rpow (Real.rpow D (1 + 12 * δ)) (-beta) *
      Real.rpow D (1 / 2 + 8 * δ) * Real.rpow D δ *
        Real.rpow D p48HeightExponent ≤ Real.rpow D (-deltaSaving δ) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hDp.le]
  rw [← Real.rpow_add hDp, ← Real.rpow_add hDp, ← Real.rpow_add hDp]
  apply Real.rpow_le_rpow_of_exponent_le hD
  convert error_exponent_le hδ hbeta using 1 <;> ring

/-- A fixed collar distance may enlarge the constant arbitrarily, but the
strict power saving absorbs the complete logarithmic fourth power. -/
theorem eventually_error_envelope_lt_one
    {δ : ℝ} (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ D : ℝ in atTop,
      C * (1 + Real.log D) ^ 4 * Real.rpow D (-deltaSaving δ) < 1 := by
  have hs := deltaSaving_pos hlo hhi
  have habs := eventually_const_mul_polylog_le_rpow (16 * C) 4
    (deltaSaving δ / 2) (by positivity) (by positivity)
  filter_upwards [habs, eventually_ge_atTop (Real.exp 1),
    eventually_gt_atTop (1 : ℝ)] with D habs hDe hDone
  have hDp : 0 < D := zero_lt_one.trans hDone
  have hlog : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDe
  have hp : (1 + Real.log D) ^ 4 ≤ 16 * (Real.log D) ^ 4 := by
    calc
      _ ≤ (2 * Real.log D) ^ 4 := by gcongr; linarith
      _ = _ := by ring
  have hh : C * (1 + Real.log D) ^ 4 ≤ Real.rpow D (deltaSaving δ / 2) := by
    calc
      _ ≤ C * (16 * (Real.log D) ^ 4) := mul_le_mul_of_nonneg_left hp hC
      _ = (16 * C) * Real.rpow (Real.log D) 4 := by
        rw [show Real.rpow (Real.log D) 4 = (Real.log D) ^ (4 : ℕ) from Real.rpow_natCast _ 4]
        ring
      _ ≤ _ := habs
  calc
    _ ≤ Real.rpow D (deltaSaving δ / 2) * Real.rpow D (-deltaSaving δ) := by
      exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hDp.le _)
    _ = Real.rpow D (-deltaSaving δ / 2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hDp]
      congr 1
      ring
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hDone (by linarith)

theorem eventually_error_logFive_envelope_lt_one
    {δ : ℝ} (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280)
    (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ D : ℝ in atTop,
      C * (1 + Real.log D) ^ 5 * Real.rpow D (-deltaSaving δ) < 1 := by
  have hs := deltaSaving_pos hlo hhi
  have habs := eventually_const_mul_polylog_le_rpow (32 * C) 5
    (deltaSaving δ / 2) (by positivity) (by positivity)
  filter_upwards [habs, eventually_ge_atTop (Real.exp 1),
    eventually_gt_atTop (1 : ℝ)] with D habs hDe hDone
  have hDp : 0 < D := zero_lt_one.trans hDone
  have hlog : 1 ≤ Real.log D := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hDe
  have hp : (1 + Real.log D) ^ 5 ≤ 32 * (Real.log D) ^ 5 := by
    calc
      _ ≤ (2 * Real.log D) ^ 5 := by gcongr; linarith
      _ = _ := by ring
  have hh : C * (1 + Real.log D) ^ 5 ≤ Real.rpow D (deltaSaving δ / 2) := by
    calc
      _ ≤ C * (32 * (Real.log D) ^ 5) := mul_le_mul_of_nonneg_left hp hC
      _ = (32 * C) * Real.rpow (Real.log D) 5 := by
        rw [show Real.rpow (Real.log D) 5 = (Real.log D) ^ (5 : ℕ) from Real.rpow_natCast _ 5]
        ring
      _ ≤ _ := habs
  calc
    _ ≤ Real.rpow D (deltaSaving δ / 2) * Real.rpow D (-deltaSaving δ) := by
      exact mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hDp.le _)
    _ = Real.rpow D (-deltaSaving δ / 2) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hDp]
      congr 1
      ring
    _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hDone (by linarith)

/-- Literal numeric Mellin envelope, including the finite mollifier's fourth
harmonic power and the full shifted conductor-height variable. -/
theorem mellin_numeric_envelope_le
    {D δ beta K H : ℝ} {z R : ℕ}
    (hD : 1 ≤ D) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1)
    (hbeta : 1 - δ ≤ beta) (hK : 0 ≤ K) (hH : 0 ≤ H) (hHD : H ≤ D)
    (hz : (z : ℝ) ≤ Real.rpow D (1 / 2 + 8 * δ))
    (hR : 1 ≤ R) (hRD : (R : ℝ) ≤ Real.rpow D δ) :
    (Real.rpow (Real.rpow D (1 + 12 * δ)) (-beta) *
        ((z : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
      (K * Real.rpow H p48HeightExponent) ≤
        K * (1 + Real.log D) ^ 4 * Real.rpow D (-deltaSaving δ) := by
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hh0 : 0 ≤ (harmonic R : ℝ) := by unfold harmonic; positivity
  have hRp : (0 : ℝ) < R := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hR)
  have hRle : (R : ℝ) ≤ D := hRD.trans (by
    simpa using Real.rpow_le_rpow_of_exponent_le hD hδhi)
  have hh : (harmonic R : ℝ) ≤ 1 + Real.log D :=
    (harmonic_le_one_add_log R).trans (by
      linarith [Real.log_le_log hRp hRle])
  have hHpow := Real.rpow_le_rpow hH hHD p48HeightExponent_nonneg
  have hpow := error_power_le hD hδ hbeta
  simp only [Real.rpow_eq_pow] at *
  calc
    _ ≤ (Real.rpow (Real.rpow D (1 + 12 * δ)) (-beta) *
        (Real.rpow D (1 / 2 + 8 * δ) * Real.rpow D δ * (1 + Real.log D) ^ 4)) *
        (K * Real.rpow D p48HeightExponent) := by
      simp only [Real.rpow_eq_pow]
      gcongr <;> first | assumption | positivity
    _ = K * (1 + Real.log D) ^ 4 *
        (Real.rpow (Real.rpow D (1 + 12 * δ)) (-beta) *
          Real.rpow D (1 / 2 + 8 * δ) * Real.rpow D δ *
            Real.rpow D p48HeightExponent) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

/-- The source collar gap bounds the inverse pole distance uniformly by a
single logarithm once the outer parameter is large. -/
theorem inv_omega_le_log_of_gap {D omega : ℝ}
    (hD : Real.exp (Real.exp 1) ≤ D) (ho : 0 < omega)
    (hgap : Real.log D ≤ Real.rpow D (omega / 140)) :
    omega⁻¹ ≤ Real.log D := by
  have hDp : 0 < D := (Real.exp_pos _).trans_le hD
  have hlog : Real.exp 1 ≤ Real.log D := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.log_le_log (Real.exp_pos _) hD
  have hlogp : 0 < Real.log D := (Real.exp_pos _).trans_le hlog
  have hloglog : 1 ≤ Real.log (Real.log D) := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) hlog
  have hh := Real.log_le_log hlogp hgap
  simp only [Real.rpow_eq_pow, Real.log_rpow hDp] at hh
  rw [inv_eq_one_div, div_le_iff₀ ho]
  nlinarith

theorem gammaSqConstant_le_log_of_gap {D omega : ℝ}
    (hD : Real.exp (Real.exp 1) ≤ D) (ho : 0 < omega)
    (hgap : Real.log D ≤ Real.rpow D (omega / 140)) :
    MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant omega ≤ 18 * Real.log D := by
  have hinv := inv_omega_le_log_of_gap hD ho hgap
  have hlog : 1 ≤ Real.log D := by
    have he : Real.exp 1 ≤ D :=
      (Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num))).trans hD
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) he
  unfold MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant
  have hi : (4 * omega / 5)⁻¹ = (5 / 4 : ℝ) * omega⁻¹ := by ring
  rw [hi]
  nlinarith

/-- Uniform smallness of the complete literal numeric Mellin error. The
threshold is independent of omega, beta, conductor-height H, and integers
z,R; the collar gap is the only inverse-distance assumption. -/
theorem eventually_uniform_mellin_numeric_lt_one
    {δ : ℝ} (hlo : 1 / 560 ≤ δ) (hhi : δ ≤ 1 / 280) :
    ∀ᶠ D : ℝ in atTop, ∀ (omega beta H : ℝ) (z R : ℕ),
      0 < omega → Real.log D ≤ Real.rpow D (omega / 140) →
      1 - δ ≤ beta → 0 ≤ H → H ≤ D →
      (z : ℝ) ≤ Real.rpow D (1 / 2 + 8 * δ) →
      1 ≤ R → (R : ℝ) ≤ Real.rpow D δ →
      (Real.rpow (Real.rpow D (1 + 12 * δ)) (-beta) *
        ((z : ℝ) * (R : ℝ) * (harmonic R : ℝ) ^ 4)) *
      (2 * Real.pi * MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant omega *
        MAPJutilaP48ConvexityAdapter.p48ConvexityConstant *
          Real.rpow H p48HeightExponent) < 1 := by
  let C : ℝ := 36 * Real.pi * MAPJutilaP48ConvexityAdapter.p48ConvexityConstant
  have hp48 := MAPJutilaP48ConvexityAdapter.p48ConvexityConstant_pos
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsmall := eventually_error_logFive_envelope_lt_one hlo hhi C hC
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp (Real.exp 1)),
    eventually_ge_atTop (1 : ℝ)] with D hsmall hDlarge hD
  intro omega beta H z R ho hgap hbeta hH hHD hz hR hRD
  have hgammap := MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant_pos ho
  have hbound := mellin_numeric_envelope_le hD (by linarith : 0 ≤ δ)
    (by linarith : δ ≤ 1) hbeta
    (show 0 ≤ 2 * Real.pi * MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant omega *
      MAPJutilaP48ConvexityAdapter.p48ConvexityConstant by positivity)
    hH hHD hz hR hRD
  have hGamma := gammaSqConstant_le_log_of_gap hDlarge ho hgap
  have hlog0 : 0 ≤ Real.log D := Real.log_nonneg hD
  have hCp : 2 * Real.pi * MAPJutilaLemma6GammaKernel.lemmaSixGammaSqConstant omega *
      MAPJutilaP48ConvexityAdapter.p48ConvexityConstant ≤ C * (1 + Real.log D) := by
    calc
      _ ≤ 2 * Real.pi * (18 * Real.log D) *
          MAPJutilaP48ConvexityAdapter.p48ConvexityConstant := by gcongr
      _ ≤ C * (1 + Real.log D) := by dsimp [C]; nlinarith [Real.pi_pos]
  apply lt_of_le_of_lt hbound
  apply lt_of_le_of_lt _ hsmall
  calc
    _ ≤ (C * (1 + Real.log D)) * (1 + Real.log D) ^ 4 *
        Real.rpow D (-deltaSaving δ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCp (by positivity))
        (Real.rpow_nonneg (zero_le_one.trans hD) _)
    _ = C * (1 + Real.log D) ^ 5 * Real.rpow D (-deltaSaving δ) := by ring

end
end MAPJutilaLemma6GenericDeltaLedger
#print axioms MAPJutilaLemma6GenericDeltaLedger.eventually_error_envelope_lt_one

#print axioms MAPJutilaLemma6GenericDeltaLedger.eventually_uniform_mellin_numeric_lt_one
