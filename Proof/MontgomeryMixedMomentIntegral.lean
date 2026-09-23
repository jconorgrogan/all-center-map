import MontgomeryLowStripContinuousTypeII
import MontgomeryMixedMomentLowStrip
import Mathlib.Algebra.QuadraticDiscriminant

namespace MAPMontgomeryMixedMomentIntegral
open scoped BigOperators
open Complex MeasureTheory
open MAPMontgomeryLowStripContinuousTypeII MAPMRTCorollary25Minkowski
open MAPMRTLemma211AllCharacterSource MAPAppendixA4DetectorDichotomy
open MAPAppendixA4FullContourLimit MAPMontgomeryLowStripGamma
open MAPMollifierCoefficientIdentity
noncomputable section

/-- Uniform for every zero with beta at least 1/2+delta and at most 1. -/
def mixedStripGammaConstant (delta : ℝ) : ℝ := lowStripGammaConstant delta + 58

theorem mixedStripGammaConstant_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < mixedStripGammaConstant delta := by
  unfold mixedStripGammaConstant
  linarith [lowStripGammaConstant_pos hdelta]

theorem gammaLeftKernelNorm_le_mixedStrip
    {delta : ℝ} (hdelta : 0 < delta) {rho : ℂ}
    (hbetaLow : 1/2+delta ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) (u : ℝ) :
    gammaLeftKernelNorm rho Y u ≤ mixedStripGammaConstant delta *
      Real.rpow Y (1/2-rho.re) * (1+u^2)⁻¹ := by
  have hp : 0 ≤ Real.rpow Y (1/2-rho.re) := Real.rpow_nonneg (by linarith) _
  have hi : 0 ≤ (1+u^2)⁻¹ := by positivity
  by_cases hlow : rho.re ≤ 7/10
  · apply (gammaLeftKernelNorm_le_lowStrip hdelta hbetaLow hlow hY u).trans
    apply mul_le_mul_of_nonneg_right _ hi
    apply mul_le_mul_of_nonneg_right _ hp
    unfold mixedStripGammaConstant; linarith
  · apply (gammaLeftKernelNorm_le_uniform (le_of_lt (lt_of_not_ge hlow)) hbetaHigh hY u).trans
    apply mul_le_mul_of_nonneg_right _ hi
    apply mul_le_mul_of_nonneg_right _ hp
    unfold mixedStripGammaConstant
    linarith [lowStripGammaConstant_pos hdelta]

theorem intervalIntegral_weighted_product_sq_le
    {w f g : ℝ → ℝ} (hw : Continuous w) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (hw0 : ∀ x, 0 ≤ w x) :
    (∫ x in a..b, w x * (f x * g x))^2 ≤
      (∫ x in a..b, w x * f x ^ 2) * (∫ x in a..b, w x * g x ^ 2) := by
  have hp : ∀ z : ℝ,
      0 ≤ (∫ x in a..b, w x * f x ^ 2) * (z*z) +
        (2 * ∫ x in a..b, w x * (f x * g x)) * z +
        (∫ x in a..b, w x * g x ^ 2) := by
    intro z
    have hnonneg : 0 ≤ ∫ x in a..b, w x * (z * f x + g x)^2 :=
      intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (hw0 x) (sq_nonneg _))
    have heq : (fun x => w x * (z * f x + g x)^2) =
        (fun x => z^2 * (w x * f x^2) + (2*z) * (w x * (f x*g x)) + w x * g x^2) := by
      funext x; ring
    have hi1 : IntervalIntegrable (fun x => z^2 * (w x * f x^2)) volume a b :=
      ((hw.mul (hf.pow 2)).const_mul _).intervalIntegrable a b
    have hi2 : IntervalIntegrable (fun x => (2*z) * (w x * (f x*g x))) volume a b :=
      ((hw.mul (hf.mul hg)).const_mul _).intervalIntegrable a b
    have hi3 : IntervalIntegrable (fun x => w x * g x^2) volume a b :=
      (hw.mul (hg.pow 2)).intervalIntegrable a b
    rw [heq, intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hnonneg
    nlinarith only [hnonneg]
  have h := discrim_le_zero hp
  unfold discrim at h
  nlinarith only [h]

/-- Actual compact-interval mixed moment, with exact weight mass. -/
theorem intervalIntegral_weighted_product_fourth_le
    {w f g : ℝ → ℝ} (hw : Continuous w) (hf : Continuous f) (hg : Continuous g)
    {a b : ℝ} (hab : a ≤ b) (hw0 : ∀ x, 0 ≤ w x)
    (hW : 0 < ∫ x in a..b, w x) :
    (∫ x in a..b, w x * (f x * g x))^4 ≤
      (∫ x in a..b, w x) * (∫ x in a..b, w x * f x^4) *
        (∫ x in a..b, w x * g x^2)^2 := by
  have hfirst := intervalIntegral_weighted_product_sq_le hw hf hg hab hw0
  have hsecond := intervalIntegral_weighted_sq_le hw (hf.pow 2) hab hw0 hW
  simp only [Pi.pow_apply, ← pow_mul] at hsecond
  have hsquare := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hmul := mul_le_mul_of_nonneg_right hsecond
    (sq_nonneg (∫ x in a..b, w x * g x^2))
  nlinarith only [hsquare, hmul]

/-- Retains the true finite mollifier; valid also for the principal character. -/
def criticalLineMollifierNorm {q : ℕ} (chi : DirichletCharacter ℂ q) (U : ℕ) (t : ℝ) : ℝ :=
  ‖mollifier chi U (((1/2 : ℝ) : ℂ) + t * I)‖

theorem continuous_criticalLineMollifierNorm {q : ℕ}
    (chi : DirichletCharacter ℂ q) (U : ℕ) : Continuous (criticalLineMollifierNorm chi U) := by
  apply Continuous.norm
  rw [continuous_iff_continuousAt]
  intro t
  exact (MAPAppendixA4Detector.analyticAt_mollifier chi _).continuousAt.comp_of_eq
    (by fun_prop) rfl

theorem norm_gammaLeftIntegrand_le_retainedProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdelta : 0 < delta) {U : ℕ} {rho : ℂ}
    (hbetaLow : 1/2 + delta ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) (u : ℝ) :
    ‖gammaLeftIntegrand chi U rho Y u‖ ≤
      (2 * mixedStripGammaConstant delta * Real.rpow Y (1/2-rho.re)) *
        (perronWeight u * (criticalLineLNorm chi (rho.im+u) *
          criticalLineMollifierNorm chi U (rho.im+u))) := by
  have hk := gammaLeftKernelNorm_le_mixedStrip hdelta hbetaLow hbetaHigh hY u
  have hp := inv_one_add_sq_le_two_perronWeight u
  have hprod : criticalLineProductNorm chi U rho u =
      criticalLineLNorm chi (rho.im+u) * criticalLineMollifierNorm chi U (rho.im+u) := by
    rw [criticalLineProductNorm_eq, norm_mul]
    simp [criticalLineLNorm, criticalLineMollifierNorm, Complex.ofReal_add]
  rw [norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm, hprod]
  have hn : 0 ≤ criticalLineLNorm chi (rho.im+u) * criticalLineMollifierNorm chi U (rho.im+u) := by
    unfold criticalLineLNorm criticalLineMollifierNorm; positivity
  have h := mul_le_mul_of_nonneg_right hk hn
  have hp' := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ mixedStripGammaConstant delta * Real.rpow Y (1/2-rho.re) by
      exact mul_nonneg (mixedStripGammaConstant_pos hdelta).le (Real.rpow_nonneg (by linarith) _))
  have hp'' := mul_le_mul_of_nonneg_right hp' hn
  nlinarith only [h, hp'']
/-- Literal central integral domination retaining both factors, including
principal characters. No zero or nonprincipal hypothesis is needed here. -/
theorem norm_normalizedCentralGammaIntegral_le_retainedProduct
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdelta : 0 < delta) {U : ℕ} {rho : ℂ}
    (hbetaLow : 1/2 + delta ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    ‖normalizedCentralGammaIntegral chi U rho Y B‖ ≤
      ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-rho.re)) *
        perronConvolution (fun t => criticalLineLNorm chi t *
          criticalLineMollifierNorm chi U t) B rho.im := by
  let A := 2 * mixedStripGammaConstant delta * Real.rpow Y (1/2-rho.re)
  have hcont : Continuous (fun u => A * (perronWeight u *
      (criticalLineLNorm chi (rho.im+u) * criticalLineMollifierNorm chi U (rho.im+u)))) :=
    continuous_const.mul (continuous_perronWeight.mul
      (((continuous_criticalLineLNorm chi).mul
        (continuous_criticalLineMollifierNorm chi U)).comp (continuous_const.add continuous_id)))
  have hint : ‖∫ u in (-B)..B, gammaLeftIntegrand chi U rho Y u‖ ≤
      ∫ u in (-B)..B, A * (perronWeight u *
        (criticalLineLNorm chi (rho.im+u) * criticalLineMollifierNorm chi U (rho.im+u))) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · exact Filter.Eventually.of_forall fun u _ =>
        norm_gammaLeftIntegrand_le_retainedProduct chi hdelta hbetaLow hbetaHigh hY u
    · exact hcont.intervalIntegrable _ _
  have hc : ‖(((1/(2*Real.pi) : ℝ) : ℂ))‖ = 1/(2*Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]; positivity
  rw [normalizedCentralGammaIntegral, norm_mul, hc]
  have h := mul_le_mul_of_nonneg_left hint (show 0 ≤ 1/(2*Real.pi) by positivity)
  rw [intervalIntegral.integral_const_mul] at h
  convert h using 1 <;> dsimp [perronConvolution, A] <;> ring

/-- The compact central integral now has a literal L-fourth / mollifier-second
budget, instead of the former pointwise square-root mollifier cost. -/
theorem normalizedCentralGammaIntegral_fourth_le_mixedMoments
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta : ℝ} (hdelta : 0 < delta) {U : ℕ} {rho : ℂ}
    (hbetaLow : 1/2 + delta ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 < B) :
    ‖normalizedCentralGammaIntegral chi U rho Y B‖^4 ≤
      ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-rho.re))^4 *
        (∫ u in (-B)..B, perronWeight u) *
        perronConvolution (fun t => criticalLineLNorm chi t ^ 4) B rho.im *
        (perronConvolution (fun t => criticalLineMollifierNorm chi U t ^ 2) B rho.im)^2 := by
  have hnorm := norm_normalizedCentralGammaIntegral_le_retainedProduct
    chi (U := U) hdelta hbetaLow hbetaHigh hY hB.le
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hnorm 4
  have hW : 0 < ∫ u in (-B)..B, perronWeight u := by
    apply intervalIntegral.integral_pos (by linarith) continuous_perronWeight.continuousOn
    · intro u hu; exact (perronWeight_pos u).le
    · exact ⟨0, ⟨by linarith, by linarith⟩, perronWeight_pos 0⟩
  have hholder := intervalIntegral_weighted_product_fourth_le
    (f := fun u => criticalLineLNorm chi (rho.im + u))
    (g := fun u => criticalLineMollifierNorm chi U (rho.im + u)) continuous_perronWeight
    ((continuous_criticalLineLNorm chi).comp (continuous_const.add continuous_id))
    ((continuous_criticalLineMollifierNorm chi U).comp (continuous_const.add continuous_id))
    (by linarith) (fun u => (perronWeight_pos u).le) hW
  have hmul := mul_le_mul_of_nonneg_left hholder
    (show 0 ≤ ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-rho.re))^4 by positivity)
  dsimp only [perronConvolution] at hpow ⊢
  nlinarith only [hpow, hmul]

end
end MAPMontgomeryMixedMomentIntegral
#print axioms MAPMontgomeryMixedMomentIntegral.intervalIntegral_weighted_product_sq_le
#print axioms MAPMontgomeryMixedMomentIntegral.intervalIntegral_weighted_product_fourth_le
#print axioms MAPMontgomeryMixedMomentIntegral.norm_gammaLeftIntegrand_le_retainedProduct

#print axioms MAPMontgomeryMixedMomentIntegral.normalizedCentralGammaIntegral_fourth_le_mixedMoments
