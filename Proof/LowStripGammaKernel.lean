import AppendixA4DetectorDichotomy

/-!
# Delta-uniform Gamma-kernel control below `7/10`

The canonical Appendix A.4 detector is analytic for every zero with
`1/2 < Re rho`, but its exported numerical kernel bound uses the compact
substrip `7/10 <= Re rho <= 1`.  Montgomery's low-strip argument instead
needs a constant uniform on

`1/2 + delta <= Re rho <= 7/10`.

This file proves that missing normalization with an explicit constant
depending only on `delta`.  It does not assert a zero-density estimate and it
does not perform the later zero-set/Fourier/crowding transfer.
-/

namespace MAPMontgomeryLowStripGamma

open Complex Real Set MeasureTheory
open scoped Real
open MAPAppendixA4DetectorDichotomy MAPAppendixA4GammaEndpoint
  MAPAppendixA4GammaTails

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Explicit compact-strip constant.  The factor `8` bounds
`Gamma(a+2)+Gamma(a+4)`, while `1 + 5/(4 delta)` bounds the inverse Cauchy
factor when `-1/5 <= a <= -delta`. -/
def lowStripGammaConstant (delta : ℝ) : ℝ :=
  8 * (1 + (4 * delta / 5)⁻¹)

theorem lowStripGammaConstant_pos {delta : ℝ} (hdelta : 0 < delta) :
    0 < lowStripGammaConstant delta := by
  unfold lowStripGammaConstant
  have : 0 < 4 * delta / 5 := by positivity
  positivity

/-- Source-faithful compact-parameter bound for the fourth-order Gamma
envelope used by Appendix A.4. -/
theorem gammaLeftCompactConstant_le_delta
    {delta a : ℝ} (hdelta : 0 < delta)
    (haLow : -(1 / 5 : ℝ) ≤ a) (haHigh : a ≤ -delta) :
    (1 + ((-a) * (a + 1))⁻¹) *
        (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤
      lowStripGammaConstant delta := by
  have haNeg : a < 0 := lt_of_le_of_lt haHigh (neg_neg_of_pos hdelta)
  have hminusA : delta ≤ -a := by linarith
  have haOne : 4 / 5 ≤ a + 1 := by linarith
  have hdeltaNonneg : 0 ≤ delta := hdelta.le
  have hfourFifths : (0 : ℝ) ≤ 4 / 5 := by norm_num
  have hcpos : 0 < (-a) * (a + 1) := by
    apply mul_pos <;> linarith
  have hcLower : 4 * delta / 5 ≤ (-a) * (a + 1) := by
    calc
      4 * delta / 5 = delta * (4 / 5) := by ring
      _ ≤ (-a) * (a + 1) :=
        mul_le_mul hminusA haOne hfourFifths (by linarith)
  have hbasePos : 0 < 4 * delta / 5 := by positivity
  have hcinv : ((-a) * (a + 1))⁻¹ ≤ (4 * delta / 5)⁻¹ :=
    (inv_le_inv₀ hcpos hbasePos).2 hcLower
  have hfac :
      1 + ((-a) * (a + 1))⁻¹ ≤ 1 + (4 * delta / 5)⁻¹ :=
    by simpa [add_comm] using add_le_add_left hcinv 1
  have ha2pos : 0 < a + 2 := by linarith
  have ha2one : 1 ≤ a + 2 := by linarith
  have ha3mem : a + 3 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hthreeMem : (3 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn ha3mem hthreeMem (by linarith)
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left (Real.Gamma_pos_of_pos ha2pos)).2 ha2one
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (ne_of_gt ha2pos)]
      _ ≤ Real.Gamma 3 := hGa3
      _ = 2 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have ha4mem : a + 4 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hfourMem : (4 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa4 : Real.Gamma (a + 4) ≤ 6 := by
    calc
      Real.Gamma (a + 4) ≤ Real.Gamma 4 :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn ha4mem hfourMem (by linarith)
      _ = 6 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have hsum : Real.Gamma (a + 2) + Real.Gamma (a + 4) ≤ 8 := by
    linarith
  have hsum0 : 0 ≤ Real.Gamma (a + 2) + Real.Gamma (a + 4) :=
    add_nonneg (Real.Gamma_pos_of_pos ha2pos).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  have htargetFac0 : 0 ≤ 1 + (4 * delta / 5)⁻¹ := by positivity
  calc
    (1 + ((-a) * (a + 1))⁻¹) *
          (Real.Gamma (a + 2) + Real.Gamma (a + 4))
        ≤ (1 + (4 * delta / 5)⁻¹) * 8 :=
      mul_le_mul hfac hsum hsum0 htargetFac0
    _ = lowStripGammaConstant delta := by
      unfold lowStripGammaConstant
      ring

/-- Pointwise Gamma--Mellin kernel majorant on the complete Montgomery low
strip.  The only deterioration at the critical line is the displayed
`delta`-constant. -/
theorem gammaLeftKernelNorm_le_lowStrip
    {delta : ℝ} (hdelta : 0 < delta)
    {rho : ℂ} (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y : ℝ} (hY : 1 ≤ Y) (t : ℝ) :
    gammaLeftKernelNorm rho Y t ≤
      lowStripGammaConstant delta *
        Real.rpow Y (1 / 2 - rho.re) * (1 + t ^ 2)⁻¹ := by
  let a : ℝ := 1 / 2 - rho.re
  let Cgamma : ℝ :=
    (1 + ((-a) * (a + 1))⁻¹) *
      (Real.Gamma (a + 2) + Real.Gamma (a + 4))
  have haLowHalf : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haLowFifth : -(1 / 5 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a ≤ -delta := by dsimp [a]; linarith
  have haNeg : a < 0 := lt_of_le_of_lt haHigh (neg_neg_of_pos hdelta)
  have hCgamma : Cgamma ≤ lowStripGammaConstant delta := by
    exact gammaLeftCompactConstant_le_delta hdelta haLowFifth haHigh
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Cgamma * (1 + t ^ 2)⁻¹ ^ 2 := by
    simpa [Cgamma] using norm_Gamma_left_vertical_le_inv_sq haLowHalf haNeg
  have hpow : ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ = Real.rpow Y a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp
  have hden : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hinv0 : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  have hsquare : (1 + t ^ 2)⁻¹ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
    have hinv1 : (1 + t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hden
    nlinarith [sq_nonneg ((1 + t ^ 2)⁻¹ - 1 / 2)]
  unfold gammaLeftKernelNorm
  dsimp only [a]
  rw [norm_mul, hpow]
  calc
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ * Real.rpow Y a ≤
        (Cgamma * (1 + t ^ 2)⁻¹ ^ 2) * Real.rpow Y a :=
      mul_le_mul_of_nonneg_right hgamma (Real.rpow_nonneg hYpos.le _)
    _ ≤ (lowStripGammaConstant delta * (1 + t ^ 2)⁻¹) *
          Real.rpow Y a := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hYpos.le _)
      calc
        Cgamma * (1 + t ^ 2)⁻¹ ^ 2 ≤
            lowStripGammaConstant delta * (1 + t ^ 2)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hCgamma (sq_nonneg _)
        _ ≤ lowStripGammaConstant delta * (1 + t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hsquare
            (lowStripGammaConstant_pos hdelta).le
    _ = lowStripGammaConstant delta *
          Real.rpow Y (1 / 2 - rho.re) * (1 + t ^ 2)⁻¹ := by
      dsimp [a]
      ring

/-- Integrated low-strip kernel mass, uniform in the zero ordinate and the
truncation height. -/
theorem truncatedGammaLeftKernelMass_le_lowStrip
    {delta : ℝ} (hdelta : 0 < delta)
    {rho : ℂ} (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    truncatedGammaLeftKernelMass rho Y B ≤
      lowStripGammaConstant delta * Real.pi *
        Real.rpow Y (1 / 2 - rho.re) := by
  let K : ℝ := lowStripGammaConstant delta *
    Real.rpow Y (1 / 2 - rho.re)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (lowStripGammaConstant_pos hdelta).le
      (Real.rpow_nonneg hYpos.le _)
  have hkernel : IntervalIntegrable (gammaLeftKernelNorm rho Y) volume (-B) B :=
    (continuous_gammaLeftKernelNorm (by linarith) (by linarith) hYpos).intervalIntegrable _ _
  have hmajor : IntervalIntegrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹)
      volume (-B) B := integrable_inv_one_add_sq.const_mul K |>.intervalIntegrable
  calc
    truncatedGammaLeftKernelMass rho Y B =
        ∫ t : ℝ in (-B)..B, gammaLeftKernelNorm rho Y t := rfl
    _ ≤ ∫ t : ℝ in (-B)..B, K * (1 + t ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) hkernel hmajor
      intro t ht
      simpa [K] using gammaLeftKernelNorm_le_lowStrip
        hdelta hbetaLow hbetaHigh hY t
    _ = K * ∫ t : ℝ in (-B)..B, (1 + t ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * Real.pi := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [intervalIntegral.integral_of_le (by linarith)]
      calc
        (∫ t : ℝ in Set.Ioc (-B) B, (1 + t ^ 2)⁻¹) ≤
            ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
          setIntegral_le_integral integrable_inv_one_add_sq
            (Filter.Eventually.of_forall fun t => by positivity)
        _ = Real.pi := integral_univ_inv_one_add_sq
    _ = lowStripGammaConstant delta * Real.pi *
          Real.rpow Y (1 / 2 - rho.re) := by
      dsimp [K]
      ring

/-- Exact normalized form consumed by the L-function-only Type-II extraction.
The factor `1/(2*pi)` cancels the displayed `pi`, leaving `C_delta/2`. -/
theorem normalized_truncatedGammaLeftKernelMass_le_lowStrip
    {delta : ℝ} (hdelta : 0 < delta)
    {rho : ℂ} (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    (U : ℕ) {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) * (U + 1) ≤
      (lowStripGammaConstant delta / 2) *
        Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
  have hmass := truncatedGammaLeftKernelMass_le_lowStrip
    hdelta hbetaLow hbetaHigh hY hB
  have hscale : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hU : 0 ≤ (U + 1 : ℝ) := by positivity
  calc
    ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) * (U + 1) ≤
        ((1 / (2 * Real.pi)) *
          (lowStripGammaConstant delta * Real.pi *
            Real.rpow Y (1 / 2 - rho.re))) * (U + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hscale) hU
    _ = (lowStripGammaConstant delta / 2) *
          Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
      field_simp [ne_of_gt Real.pi_pos]

/-- Low-strip version of the final pointwise Appendix A.4 detector
alternative.  This is the exact interface needed before the separate
zero-set thinning/Fourier transfer and Montgomery mean-value estimates. -/
theorem post_A5_budgeted_fixedCharacter_detector_to_largeValue_lowStrip
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta kappa eta : ℝ} (hdelta : 0 < delta)
    (_hkappa : 0 < kappa) (_heta : 0 < eta)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-CGLProofDAG.inputLoss kappa eta) +
          (lowStripGammaConstant delta / 2) *
            Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-CGLProofDAG.inputLoss kappa eta) ≤
        Real.exp (-(1 / Y))) :
    Real.rpow R (-CGLProofDAG.inputLoss kappa eta) ≤
        ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        Real.rpow R (-CGLProofDAG.inputLoss kappa eta) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  let V : ℝ := Real.rpow R (-CGLProofDAG.inputLoss kappa eta)
  let D : ℝ :=
    ((1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) * (U + 1)
  have hbetaHalf : 1 / 2 < rho.re := by linarith
  have hbetaOne : rho.re ≤ 1 := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hBpos : 0 < detectorVerticalCutoff R := lt_of_lt_of_le zero_lt_one hB
  have hmasspos : 0 < truncatedGammaLeftKernelMass rho Y
      (detectorVerticalCutoff R) :=
    truncatedGammaLeftKernelMass_pos hbetaHalf hbetaOne hYpos hBpos
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (by positivity) hmasspos) (by positivity)
  have hDle : D ≤ (lowStripGammaConstant delta / 2) *
      Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
    dsimp [D]
    exact normalized_truncatedGammaLeftKernelMass_le_lowStrip
      hdelta hbetaLow hbetaHigh U hY (by linarith)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Real.rpow_pos_of_pos hR _
  rcases post_A5_quantitative_detector_dichotomy_with_LFunction_large_value
    chi hchi hU hrho hbetaHalf hbetaOne hY hUN hB
      (a := V)
      (b := (lowStripGammaConstant delta / 2) *
        Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V)
      (by simpa [V] using hbudget) with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    refine ⟨t, ht, ?_⟩
    apply (show V ≤
        ((lowStripGammaConstant delta / 2) *
          Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V) / D by
      rw [le_div_iff₀ hDpos]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hDle hVpos.le) |>.trans
    simpa [V, D] using htlarge

end
end MAPMontgomeryLowStripGamma

#print axioms MAPMontgomeryLowStripGamma.gammaLeftCompactConstant_le_delta
#print axioms MAPMontgomeryLowStripGamma.gammaLeftKernelNorm_le_lowStrip
#print axioms MAPMontgomeryLowStripGamma.truncatedGammaLeftKernelMass_le_lowStrip
#print axioms MAPMontgomeryLowStripGamma.normalized_truncatedGammaLeftKernelMass_le_lowStrip
#print axioms MAPMontgomeryLowStripGamma.post_A5_budgeted_fixedCharacter_detector_to_largeValue_lowStrip
