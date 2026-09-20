import JutilaLemma6FiniteContour
import JutilaMNonnegativeHalfPlaneBound
import JutilaP53LeftLineEstimate

/-! Both vertical sides of the actual Lemma 6 detector contour are integrable. -/
namespace MAPJutilaLemma6VerticalIntegrability
open Complex Real MeasureTheory Set
open MAPJutilaLemma6FiniteContour MAPJutilaLemma6ErrorBound
open MAPJutilaMEntire MAPJutilaMNonnegativeHalfPlaneBound
open MAPJutilaLemma6MellinIntegral MAPJutilaP53LeftLineEstimate
open MAPGammaCompactStripSharp MAPPrimitiveLFixedStrip
open RamachandraShiftedGammaPoleContour
noncomputable section

theorem continuous_detector_vertical
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (rho : ℂ) (xi : ℕ → ℂ) {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d)
    (S : Finset ℕ) {X a : ℝ} (hX : 0 < X) (ha : -1 < a) :
    Continuous (fun u : ℝ => jutilaDetectorExtension chi rho xi D S X ((a : ℂ) + u * I)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have houter := (analyticAt_jutilaDetectorExtension chi hchi rho xi hDpos S hX
    (z := (a : ℂ) + u * I) (by simpa [MAPAppendixA4Detector.contourStrip] using ha)).continuousAt
  exact houter.comp (f := fun v : ℝ => (a : ℂ) + v * I) (by fun_prop)

theorem integrable_detector_left
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (xi : ℕ → ℂ)
    {D S : Finset ℕ} {z2 R : ℕ}
    (hDcard : D.card ≤ z2) (hDpos : ∀ d ∈ D, 0 < d)
    (hxi : ∀ d ∈ D, ‖xi d‖ ≤ 1) (hS : S ⊆ Finset.Icc 1 R)
    (hSq : ∀ r ∈ S, Squarefree r) (hcop : ∀ r ∈ S, r.Coprime q)
    {beta omega t X : ℝ} (homega : 0 < omega)
    (hbetaLo : 4 / 5 ≤ beta) (hbetaHi : beta ≤ 1 - omega) (hX : 0 < X)
    (hrho : DirichletCharacter.LFunction chi (lemmaSixZeroPoint beta t) = 0) :
    Integrable (fun u : ℝ => jutilaDetectorExtension chi (lemmaSixZeroPoint beta t)
      xi D S X (((-beta : ℝ) : ℂ) + u * I)) := by
  let C := Real.rpow X (-beta) * ((z2 : ℝ) * (R : ℝ) * (harmonic R : ℝ)^4)
  have hmajor := (integrable_lemmaSixGammaLNorm chi hprim hchi homega hbetaLo hbetaHi t).const_mul C
  apply hmajor.mono'
  · exact (continuous_detector_vertical chi hchi _ xi hDpos S hX (by linarith)).aestronglyMeasurable
  · filter_upwards with u
    have heq : jutilaDetectorExtension chi (lemmaSixZeroPoint beta t) xi D S X
        (((-beta : ℝ) : ℂ) + u * I) = lemmaSixMellinErrorIntegrand chi xi D S beta t X u := by
      simpa only [lemmaSixLeftPoint, Complex.ofReal_neg] using
        jutilaDetectorExtension_left_eq_errorIntegrand chi xi D S (u := u) (by linarith) hrho
    rw [heq]
    exact norm_lemmaSixMellinErrorIntegrand_le chi xi hDcard hDpos hxi hS hSq hcop hX

theorem integrable_detector_rightOne
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (rho : ℂ) (xi : ℕ → ℂ) {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d)
    (S : Finset ℕ) {X : ℝ} (hX : 0 < X)
    (hrhoLo : 0 ≤ rho.re) (hrhoHi : rho.re ≤ 1)
    (hrho : DirichletCharacter.LFunction chi rho = 0) :
    Integrable (fun u : ℝ => jutilaDetectorExtension chi rho xi D S X ((1 : ℂ) + u * I)) := by
  obtain ⟨C, hC, hM⟩ := exists_jutilaMWeightedSumComplex_bound chi xi hDpos S
  let H := 5 + |rho.im|
  let K := 2400 * (q : ℝ)^2 * H^2 * X * C
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmajor := integrable_one_add_abs_pow_six_mul_exp_neg_abs.const_mul K
  apply hmajor.mono'
  · exact (continuous_detector_vertical chi hchi rho xi hDpos S hX (by norm_num)).aestronglyMeasurable
  · filter_upwards with u
    let w : ℂ := 1 + (u : ℂ) * I
    let z := rho + w
    have hw : w ≠ 0 := by intro h; have := congrArg Complex.re h; simp [w] at this
    have hzRe : z.re = rho.re + 1 := by simp [z, w]
    have hzIm : z.im = rho.im + u := by simp [z, w]
    have hLraw := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi
      (z := z) (by rw [hzRe]; linarith) (by rw [hzRe]; linarith)
    have hzNorm : ‖z + 3‖ ≤ H + |u| := by
      calc
        _ ≤ |(z + 3).re| + |(z + 3).im| := Complex.norm_le_abs_re_add_abs_im _
        _ = |rho.re + 4| + |rho.im + u| := by simp [z, w]; ring_nf
        _ ≤ 5 + (|rho.im| + |u|) := by
          rw [abs_of_nonneg (by linarith)]
          exact add_le_add (by linarith) (abs_add_le _ _)
        _ = _ := by dsimp [H]; ring
    have hL : ‖DirichletCharacter.LFunction chi z‖ ≤ 200 * (q : ℝ)^2 * (H + |u|)^2 :=
      hLraw.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzNorm 2) (by positivity))
    have hGamma : ‖Complex.Gamma w‖ ≤ 12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|) := by
      simpa [w, GammaCompactStripScratch.stripPoint] using
        norm_Gamma_positive_strip_le_exp_pi_half (a := 1) (t := u) (by norm_num) (by norm_num)
    have hPow : ‖(X : ℂ)^w‖ = X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
      simp [w]
    have hM' := hM z (by rw [hzRe]; linarith)
    have hH : 1 ≤ H := by dsimp [H]; linarith [abs_nonneg rho.im]
    have hprod : H + |u| ≤ H * (1 + |u|) := by nlinarith [abs_nonneg u]
    have hpower : (H + |u|)^2 ≤ H^2 * (1 + |u|)^2 := by
      calc
        _ ≤ (H * (1 + |u|))^2 := pow_le_pow_left₀ (by positivity) hprod 2
        _ = _ := by ring
    have hpoly : (1 + |u|)^3 ≤ (1 + |u|)^6 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg u]) (by norm_num)
    have hexp : Real.exp (-(Real.pi / 2) * |u|) ≤ Real.exp (-|u|) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three, abs_nonneg u]
    change ‖jutilaDetectorExtension chi rho xi D S X w‖ ≤ _
    rw [jutilaDetectorExtension_eq_raw chi xi D S X hrho hw]
    simp only [norm_mul, hPow]
    calc
      _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
          (200 * (q : ℝ)^2 * (H + |u|)^2) * X * C := by gcongr
      _ ≤ (12 * (1 + |u|) * Real.exp (-(Real.pi / 2) * |u|)) *
          (200 * (q : ℝ)^2 * (H^2 * (1 + |u|)^2)) * X * C := by gcongr
      _ = K * ((1 + |u|)^3 * Real.exp (-(Real.pi / 2) * |u|)) := by dsimp [K]; ring
      _ ≤ K * ((1 + |u|)^6 * Real.exp (-|u|)) := by gcongr

end
end MAPJutilaLemma6VerticalIntegrability
#print axioms MAPJutilaLemma6VerticalIntegrability.integrable_detector_left

#print axioms MAPJutilaLemma6VerticalIntegrability.integrable_detector_rightOne
