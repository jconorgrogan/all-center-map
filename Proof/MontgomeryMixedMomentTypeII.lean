import MontgomeryMixedMomentPacking
import MontgomeryMollifierSecondMoment
namespace MAPMontgomeryMixedMomentTypeII
open scoped BigOperators
open Complex MeasureTheory
open MAPMontgomeryMixedMomentIntegral MAPMontgomeryMixedMomentFamily MAPMontgomeryMixedMomentPacking
open MAPMontgomeryLowStripContinuousTypeII MAPMRTCorollary25Minkowski
open MAPMRTLemma211AllCharacterSource MAPAppendixA4DetectorDichotomy
open MAPMontgomeryLowStripGamma
noncomputable section

def allCharacterMollifierSecondIntegral (q U : ℕ) (H : ℝ) : ℝ :=
  ∑ chi : DirichletCharacter ℂ q, ∫ t in (-H)..H, criticalLineMollifierNorm chi U t ^ 2

/-- Retained-integral all-character Type-II count with its exact second
moment. Principal characters are included; no point extraction is used. -/
theorem mixed_typeII_family_budget
    {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
    {delta sigma Y B T b : ℝ} {U : ℕ}
    (hdelta : 0 < delta) (hY : 1 ≤ Y) (hB : 0 < B) (hT : 0 ≤ T) (hb : 0 ≤ b)
    (hbetaLow : ∀ chi rho, rho ∈ W chi → 1/2 + delta ≤ rho.re)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 1)
    (hsigma : ∀ chi rho, rho ∈ W chi → sigma ≤ rho.re)
    (hheight : ∀ chi rho, rho ∈ W chi → |rho.im| ≤ T)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' → 3*B ≤ |rho.im-rho'.im|)
    (hcentral : ∀ chi rho, rho ∈ W chi → b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ))^3 * b^4 ≤
      ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-sigma))^4 *
        (∫ u in (-B)..B, perronWeight u) *
        allCharacterCriticalLineFourthIntegral q (T+B) *
        (allCharacterMollifierSecondIntegral q U (T+B))^2 := by
  classical
  let C := (mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-sigma)
  let S : Finset ((chi : DirichletCharacter ℂ q) × ℂ) := Finset.univ.sigma W
  have hC : 0 ≤ C := mul_nonneg
    (div_nonneg (mixedStripGammaConstant_pos hdelta).le Real.pi_pos.le)
    (Real.rpow_nonneg (by linarith) _)
  have hmass : 0 < ∫ u in (-B)..B, perronWeight u := by
    apply intervalIntegral.integral_pos (by linarith) continuous_perronWeight.continuousOn
    · intro u hu; exact (perronWeight_pos u).le
    · exact ⟨0,⟨by linarith,by linarith⟩,perronWeight_pos 0⟩
  have hrow : ∀ chi rho, rho ∈ W chi → b ≤ C *
      perronConvolution (fun t => criticalLineLNorm chi t * criticalLineMollifierNorm chi U t) B rho.im := by
    intro chi rho hrho
    have hn := norm_normalizedCentralGammaIntegral_le_retainedProduct chi (U := U)
      hdelta (hbetaLow chi rho hrho) (hbetaHigh chi rho hrho) hY hB.le
    apply (hcentral chi rho hrho).trans (hn.trans ?_)
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hY (by linarith [hsigma chi rho hrho]))
        (div_nonneg (mixedStripGammaConstant_pos hdelta).le Real.pi_pos.le)
    · apply perronConvolution_nonneg _ hB.le
      intro t; unfold criticalLineLNorm criticalLineMollifierNorm; positivity
  have hfinite := integral_family_mixed_count_scaled S perronWeight
    (fun row u => criticalLineLNorm row.1 (row.2.im+u))
    (fun row u => criticalLineMollifierNorm row.1 U (row.2.im+u))
    continuous_perronWeight
    (fun row hrow => (continuous_criticalLineLNorm row.1).comp (continuous_const.add continuous_id))
    (fun row hrow => (continuous_criticalLineMollifierNorm row.1 U).comp (continuous_const.add continuous_id))
    (by linarith) hb (fun u => (perronWeight_pos u).le) hmass
    (C := C) (by
      intro row hrowS
      exact hrow row.1 row.2 (Finset.mem_sigma.mp hrowS).2)
  have hfinite' :
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ))^3 * b^4 ≤
        C^4 * (∫ u in (-B)..B, perronWeight u) *
          (∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ W chi,
            perronConvolution (fun t => criticalLineLNorm chi t^4) B rho.im) *
          (∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ W chi,
            perronConvolution (fun t => criticalLineMollifierNorm chi U t^2) B rho.im)^2 := by
    simpa [S, Finset.card_sigma, Finset.sum_sigma, Nat.cast_sum, perronConvolution] using hfinite
  have hfourth := sum_zeroFamily_perronConvolution_le W
    (fun chi t => criticalLineLNorm chi t^4)
    (fun chi => (continuous_criticalLineLNorm chi).pow 4)
    (fun chi t => by positivity) hB hT hheight hsep
  have hsecond := sum_zeroFamily_perronConvolution_le W
    (fun chi t => criticalLineMollifierNorm chi U t^2)
    (fun chi => (continuous_criticalLineMollifierNorm chi U).pow 2)
    (fun chi t => sq_nonneg _) hB hT hheight hsep
  have hsecond0 : 0 ≤ ∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ W chi,
      perronConvolution (fun t => criticalLineMollifierNorm chi U t^2) B rho.im := by
    apply Finset.sum_nonneg; intro chi hchi
    apply Finset.sum_nonneg; intro rho hrho
    exact perronConvolution_nonneg (fun t => sq_nonneg _) hB.le
  have hfourth0 : 0 ≤ ∑ chi : DirichletCharacter ℂ q, ∑ rho ∈ W chi,
      perronConvolution (fun t => criticalLineLNorm chi t^4) B rho.im := by
    apply Finset.sum_nonneg; intro chi hchi
    apply Finset.sum_nonneg; intro rho hrho
    exact perronConvolution_nonneg (fun t => by positivity) hB.le
  apply hfinite'.trans
  change _ ≤ C^4 * (∫ u in (-B)..B, perronWeight u) *
    (∑ chi : DirichletCharacter ℂ q, ∫ t in (-(T+B))..(T+B), criticalLineLNorm chi t^4) *
    (∑ chi : DirichletCharacter ℂ q, ∫ t in (-(T+B))..(T+B), criticalLineMollifierNorm chi U t^2)^2
  exact mul_le_mul
    (mul_le_mul_of_nonneg_left hfourth (mul_nonneg (pow_nonneg hC _) hmass.le))
    (pow_le_pow_left₀ hsecond0 hsecond 2) (sq_nonneg _)
    (mul_nonneg (mul_nonneg (pow_nonneg hC _) hmass.le) (hfourth0.trans hfourth))
/-- Instantiates the literal all-character mollifier second moment. -/
theorem allCharacterMollifierSecondIntegral_le
    {q U : ℕ} [NeZero q] (hU : 1 ≤ U) {H : ℝ} (hH : 0 ≤ H) :
    allCharacterMollifierSecondIntegral q U H ≤
      ((q : ℝ)*(2*H)+8*Real.pi*(U : ℝ)) * (1+Real.log U) := by
  unfold allCharacterMollifierSecondIntegral
  rw [← intervalIntegral.integral_finsetSum]
  · have h := MAPMontgomeryMollifierSecondMoment.mollifier_second_moment_interval_le
      (q := q) hU (-H) (show 0 ≤ 2*H by linarith)
    simpa only [show -H+2*H=H by ring] using h
  · intro chi hchi
    exact ((continuous_criticalLineMollifierNorm chi U).pow 2).intervalIntegrable _ _

/-- A universal, fully instantiated mixed Type-II estimate. The fourth
moment's actual logarithmic and conductor losses remain explicit in its
published-source scale; they are not replaced by a ninth logarithm. -/
theorem exists_constant_mixed_typeII_family_budget :
    ∃ C₆ : ℝ, 0 < C₆ ∧
    ∀ {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
      {delta sigma Y B T b : ℝ} {U : ℕ},
      1 ≤ U → 0 < delta → 1 ≤ Y → 0 < B → 0 ≤ T → 3 ≤ T+B → 0 ≤ b →
      (∀ chi rho, rho ∈ W chi → 1/2+delta ≤ rho.re) →
      (∀ chi rho, rho ∈ W chi → rho.re ≤ 1) →
      (∀ chi rho, rho ∈ W chi → sigma ≤ rho.re) →
      (∀ chi rho, rho ∈ W chi → |rho.im| ≤ T) →
      (∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
        rho ≠ rho' → 3*B ≤ |rho.im-rho'.im|) →
      (∀ chi rho, rho ∈ W chi → b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) →
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ))^3 * b^4 ≤
        ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-sigma))^4 *
          (∫ u in (-B)..B, perronWeight u) *
          (C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale q (T+B)) *
          (((q : ℝ)*(2*(T+B))+8*Real.pi*(U : ℝ)) * (1+Real.log U))^2 := by
  obtain ⟨C₆,hC₆,hram⟩ := RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
  refine ⟨C₆,hC₆,?_⟩
  intro q _ W delta sigma Y B T b U hU hdelta hY hB hT hTB hb
    hbetaLow hbetaHigh hsigma hheight hsep hcentral
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hprod : 1 < (q : ℝ)*(T+B) := by nlinarith
  have hstrip : |(1/2 : ℝ)-1/2| ≤ (100*Real.log ((q : ℝ)*(T+B)))⁻¹ := by
    rw [sub_self,abs_zero]
    exact inv_nonneg.mpr (mul_nonneg (by norm_num) (Real.log_pos hprod).le)
  have hfourth := hram q (T+B) (1/2) hTB hstrip
  change allCharacterCriticalLineFourthIntegral q (T+B) ≤
    C₆ * RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale q (T+B) at hfourth
  have hsecond := allCharacterMollifierSecondIntegral_le (q := q) hU
    (show 0 ≤ T+B by linarith)
  have hsecond0 : 0 ≤ allCharacterMollifierSecondIntegral q U (T+B) := by
    unfold allCharacterMollifierSecondIntegral
    apply Finset.sum_nonneg; intro chi hchi
    exact intervalIntegral.integral_nonneg (by linarith) (fun t ht => sq_nonneg _)
  have hfourth0 : 0 ≤ allCharacterCriticalLineFourthIntegral q (T+B) := by
    unfold allCharacterCriticalLineFourthIntegral
    apply Finset.sum_nonneg; intro chi hchi
    exact intervalIntegral.integral_nonneg (by linarith) (fun t ht => by
      unfold criticalLineLFourth; positivity)
  have hfront := mixed_typeII_family_budget W hdelta hY hB hT hb
    hbetaLow hbetaHigh hsigma hheight hsep hcentral
  apply hfront.trans
  have hfactor : 0 ≤
      ((mixedStripGammaConstant delta / Real.pi) * Real.rpow Y (1/2-sigma))^4 *
        (∫ u in (-B)..B, perronWeight u) := by
    apply mul_nonneg (by positivity)
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun u hu => (perronWeight_pos u).le)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hfourth hfactor)
    (pow_le_pow_left₀ hsecond0 hsecond 2) (sq_nonneg _)
    (mul_nonneg hfactor (hfourth0.trans hfourth))

end
end MAPMontgomeryMixedMomentTypeII
#print axioms MAPMontgomeryMixedMomentTypeII.mixed_typeII_family_budget

#print axioms MAPMontgomeryMixedMomentTypeII.exists_constant_mixed_typeII_family_budget
