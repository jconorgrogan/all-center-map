import AppendixA4DetectorDichotomy
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

/-!
# Polynomial-height repair of the Appendix A.4 Gamma tail

The old quantitative tail proof absorbed
`(5 + |rho.im| + |t|)^3` into one exponential before separating the zero
height from the Mellin displacement.  That produced the unusable factor
`exp ((5 + |rho.im|) / 2)`.

Here the fixed height is factored first:

`5 + |rho.im| + |t| <= (5 + |rho.im|) * (1 + |t|)`.

Only the displacement polynomial is then absorbed by Gamma decay.  The result
is polynomial in `|rho.im|` and exponentially small in the translation-
invariant distance `|u - rho.im|`.
-/

namespace MAPAppendixA4RecenteredGammaRepair

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
  MAPAppendixA4FullContourLimit MAPAppendixA4GammaTails
  MAPAppendixA4DetectorDichotomy

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The shifted-line detector written in the absolute critical-line ordinate
`u`, rather than the displacement `t` from the zero ordinate. -/
def recenteredGammaLeftIntegrand
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y : ℝ) (u : ℝ) : ℂ :=
  gammaLeftIntegrand chi U rho Y (u - rho.im)

/-- Exact recentered formula.  Gamma sees the displacement from the zero,
while `L` and the mollifier see the absolute critical-line ordinate. -/
theorem recenteredGammaLeftIntegrand_eq
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y u : ℝ) :
    recenteredGammaLeftIntegrand chi U rho Y u =
      let a : ℝ := 1 / 2 - rho.re
      MAPMellinDetectorLeaf.gammaMellinWeight Y
          (a + (u - rho.im) * I) *
        DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + u * I) *
        mollifier chi U (((1 / 2 : ℝ) : ℂ) + u * I) := by
  let a : ℝ := 1 / 2 - rho.re
  have hs : rho + ((a : ℂ) + ((u - rho.im : ℝ) : ℂ) * I) =
      (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I) := by
    apply Complex.ext <;> simp [a]
  unfold recenteredGammaLeftIntegrand gammaLeftIntegrand
  dsimp only
  rw [hs]
  simp only [Complex.ofReal_sub]

/-- The paper's central integral is exactly the recentered integral over the
window centered at the zero ordinate. -/
theorem normalizedCentralGammaIntegral_eq_recentered
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (rho : ℂ) (Y B : ℝ) :
    normalizedCentralGammaIntegral chi U rho Y B =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ in (rho.im - B)..(rho.im + B),
          recenteredGammaLeftIntegrand chi U rho Y u) := by
  unfold normalizedCentralGammaIntegral recenteredGammaLeftIntegrand
  rw [intervalIntegral.integral_comp_sub_right]
  congr 2 <;> ring

/-- Pointwise Gamma-detector envelope with polynomial, rather than
exponential, dependence on the zero height. -/
theorem norm_gammaLeftIntegrand_le_exp_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖gammaLeftIntegrand chi U rho Y t‖ ≤
      (115200 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2)) * Real.exp (-|t| / 2) := by
  let a : ℝ := 1 / 2 - rho.re
  let C₀ : ℝ := 5 + |rho.im|
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) := by
    have h := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      haLow haHigh ht
    simpa [GammaCompactStripScratch.stripPoint] using h
  have hYpow : ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY (by dsimp [a]; linarith)
  have hslo : -1 ≤ (rho + ((a : ℂ) + t * I)).re := by
    simp [a]
    norm_num
  have hshi : (rho + ((a : ℂ) + t * I)).re ≤ 2 := by
    simp [a]
    norm_num
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi hslo hshi
  have him : |(rho + ((a : ℂ) + t * I) + 3).im| ≤
      |rho.im| + |t| := by
    simp
    exact abs_add_le rho.im t
  have hre : |(rho + ((a : ℂ) + t * I) + 3).re| ≤ 5 := by
    simp [a]
    norm_num
  have hnormshift : ‖rho + ((a : ℂ) + t * I) + 3‖ ≤ C₀ + |t| := by
    calc
      ‖rho + ((a : ℂ) + t * I) + 3‖ ≤
          |(rho + ((a : ℂ) + t * I) + 3).re| +
            |(rho + ((a : ℂ) + t * I) + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|rho.im| + |t|) := add_le_add hre him
      _ = C₀ + |t| := by dsimp [C₀]; ring
  have hL : ‖DirichletCharacter.LFunction chi
      (rho + ((a : ℂ) + t * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (C₀ + |t|) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnormshift 2) (by positivity))
  have hsnonneg : 0 ≤ (rho + ((a : ℂ) + t * I)).re := by simp [a]
  have hM := MAPAppendixA4GammaTails.norm_mollifier_le_card chi U hsnonneg
  have hC₀ : 1 ≤ C₀ := by dsimp [C₀]; linarith [abs_nonneg rho.im]
  have hfactor : C₀ + |t| ≤ C₀ * (1 + |t|) := by
    nlinarith [abs_nonneg t]
  have hpolyfactor :
      (1 + |t|) * (C₀ + |t|) ^ 2 ≤
        C₀ ^ 2 * (1 + |t|) ^ 3 := by
    have hnonneg : 0 ≤ 1 + |t| := by positivity
    calc
      (1 + |t|) * (C₀ + |t|) ^ 2 ≤
          (1 + |t|) * (C₀ * (1 + |t|)) ^ 2 := by gcongr
      _ = C₀ ^ 2 * (1 + |t|) ^ 3 := by ring
  let x : ℝ := (1 + |t|) / 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have htaylor := Real.pow_div_factorial_le_exp x hx 3
  have hpolyexp : (1 + |t|) ^ 3 ≤ 48 * Real.exp x := by
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac] at htaylor
    dsimp [x] at htaylor ⊢
    nlinarith [Real.exp_pos ((1 + |t|) / 2)]
  have hexpcombine : Real.exp x * Real.exp (-|t|) =
      Real.exp (1 / 2) * Real.exp (-|t| / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  unfold gammaLeftIntegrand MAPMellinDetectorLeaf.gammaMellinWeight
  dsimp only
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ *
        ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ *
        ‖DirichletCharacter.LFunction chi (rho + ((a : ℂ) + t * I))‖ *
        ‖mollifier chi U (rho + ((a : ℂ) + t * I))‖
        ≤ (12 * (1 + |t|) * Real.exp (-|t|)) * 1 *
            (200 * (q : ℝ) ^ 2 * (C₀ + |t|) ^ 2) * (U + 1) := by
          gcongr
    _ = 2400 * (q : ℝ) ^ 2 * (U + 1) *
          (((1 + |t|) * (C₀ + |t|) ^ 2) * Real.exp (-|t|)) := by
      ring
    _ ≤ 2400 * (q : ℝ) ^ 2 * (U + 1) *
          ((C₀ ^ 2 * (1 + |t|) ^ 3) * Real.exp (-|t|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpolyfactor (Real.exp_nonneg _))
        (by positivity)
    _ ≤ 2400 * (q : ℝ) ^ 2 * (U + 1) *
          ((C₀ ^ 2 * (48 * Real.exp x)) * Real.exp (-|t|)) := by
      gcongr
    _ = (115200 * (q : ℝ) ^ 2 * (U + 1) * C₀ ^ 2 *
          Real.exp (1 / 2)) * Real.exp (-|t| / 2) := by
      rw [show C₀ ^ 2 * (48 * Real.exp x) =
          48 * C₀ ^ 2 * Real.exp x by ring, mul_assoc (48 * C₀ ^ 2 : ℝ),
        hexpcombine]
      ring
    _ = (115200 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
          Real.exp (1 / 2)) * Real.exp (-|t| / 2) := by rfl

/-- Translation-invariant form of the pointwise tail: after recentering, the
decay depends on `|u-rho.im|`, with only polynomial dependence on the center. -/
theorem norm_recenteredGammaLeftIntegrand_le_exp_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {u : ℝ}
    (hu : 1 ≤ |u - rho.im|) :
    ‖recenteredGammaLeftIntegrand chi U rho Y u‖ ≤
      (115200 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2)) * Real.exp (-|u - rho.im| / 2) := by
  exact norm_gammaLeftIntegrand_le_exp_polynomial_height chi hchi hbetaLow
    hbetaHigh U hY hu

/-- The two shifted-line tails now have only polynomial zero-height cost. -/
theorem norm_gammaLeftIntegrand_two_tails_le_exp_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
      460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2) * Real.exp (-B / 2) := by
  let K : ℝ := 115200 * (q : ℝ) ^ 2 * (U + 1) *
    (5 + |rho.im|) ^ 2 * Real.exp (1 / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hupperMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((-1 / 2 : ℝ) * t)) (Set.Ioi B) :=
    (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B).const_mul K
  have hlowerMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((1 / 2 : ℝ) * t)) (Set.Iic (-B)) :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)).const_mul K
  have hupper :
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
          ∫ t : ℝ in Set.Ioi B, K * Real.exp ((-1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hupperMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        change B < t at ht
        have htpos : 0 < t := lt_of_le_of_lt (by linarith : 0 ≤ B) ht
        have htlarge : 1 ≤ |t| := by
          rw [abs_of_pos htpos]
          linarith
        have hpoint := norm_gammaLeftIntegrand_le_exp_polynomial_height
          chi hchi hbetaLow hbetaHigh U hY (t := t) htlarge
        rw [abs_of_pos htpos] at hpoint
        simpa [K, div_eq_mul_inv, mul_comm] using hpoint
      _ = K * (-Real.exp ((-1 / 2 : ℝ) * B) / (-1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (-1 / 2 : ℝ) * B = -B / 2 by ring]
        ring
  have hlower :
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ ≤
          ∫ t : ℝ in Set.Iic (-B), K * Real.exp ((1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hlowerMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
        change t ≤ -B at ht
        have htnonpos : t ≤ 0 := by linarith
        have htlarge : 1 ≤ |t| := by
          rw [abs_of_nonpos htnonpos]
          linarith
        have hpoint := norm_gammaLeftIntegrand_le_exp_polynomial_height
          chi hchi hbetaLow hbetaHigh U hY (t := t) htlarge
        rw [abs_of_nonpos htnonpos] at hpoint
        simpa [K, div_eq_mul_inv, mul_comm] using hpoint
      _ = K * (Real.exp ((1 / 2 : ℝ) * (-B)) / (1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (1 / 2 : ℝ) * (-B) = -B / 2 by ring]
        ring
  calc
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
        ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ +
          ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ :=
      norm_add_le _ _
    _ ≤ 2 * K * Real.exp (-B / 2) + 2 * K * Real.exp (-B / 2) :=
      add_le_add hlower hupper
    _ = 460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2) * Real.exp (-B / 2) := by
      dsimp [K]
      ring

/-- Quantitative detector error with the repaired vertical tail. -/
theorem norm_quantitative_detector_truncation_error_le_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chi U N rho Y -
        normalizedCentralGammaIntegral chi U rho Y B‖ ≤
      (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ +
        (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
            Real.exp (1 / 2) * Real.exp (-B / 2)) := by
  let A : ℂ := ∑' k : ℕ,
    arithmeticDetectorTerm chi U rho Y (k + (N + 1))
  let V : ℂ :=
    (∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
      ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hdecomp := quantitative_detector_decomposition chi hchi hU hUN hrho
    hbetaLow hbetaHigh hY B
  have herr :
      (Real.exp (-(1 / Y)) : ℂ) +
          arithmeticDetectorBlock chi U N rho Y -
          normalizedCentralGammaIntegral chi U rho Y B = c * V - A := by
    dsimp [A, V, c]
    linear_combination hdecomp
  have hA := norm_arithmetic_shifted_tail_le chi U N
    (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbetaLow.le)
    (lt_of_lt_of_le zero_lt_one hY)
  have hV := norm_gammaLeftIntegrand_two_tails_le_exp_polynomial_height
    chi hchi hbetaLow hbetaHigh U hY hB
  rw [herr]
  calc
    ‖c * V - A‖ ≤ ‖c * V‖ + ‖A‖ := norm_sub_le _ _
    _ = ‖c‖ * ‖V‖ + ‖A‖ := by rw [norm_mul]
    _ ≤ (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
            Real.exp (1 / 2) * Real.exp (-B / 2)) +
        ((U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹) := by
      have hc : ‖c‖ = 1 / (2 * Real.pi) := by
        dsimp [c]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        positivity
      rw [hc]
      exact add_le_add (mul_le_mul_of_nonneg_left hV (by positivity)) hA
    _ = (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ +
        (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
            Real.exp (1 / 2) * Real.exp (-B / 2)) := by
      ring

/-- Repaired paper-scale error envelope. -/
def detectorTruncationErrorEnvelopePolynomialHeight
    (q U : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  (U + 1) * (Real.exp (-(1 / Y))) ^
      (detectorArithmeticCutoff Y R + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ +
    (1 / (2 * Real.pi)) *
      (460800 * (q : ℝ) ^ 2 * (U + 1) * (5 + |rho.im|) ^ 2 *
        Real.exp (1 / 2) * Real.exp (-(detectorVerticalCutoff R) / 2))

/-- Exact paper-scale specialization of the repaired envelope. -/
theorem norm_paper_scale_detector_truncation_error_le_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y -
        normalizedCentralGammaIntegral chi U rho Y
          (detectorVerticalCutoff R)‖ ≤
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R := by
  simpa [detectorTruncationErrorEnvelopePolynomialHeight] using
    norm_quantitative_detector_truncation_error_le_polynomial_height
      chi hchi hU hUN hrho hbetaLow hbetaHigh hY hB

/-- The paper-scale detector dichotomy with its literal conclusion unchanged;
only the now-valid polynomial-height error budget replaces the old envelope. -/
theorem post_A5_quantitative_detector_dichotomy_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + a + b ≤
        Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      b ≤ ‖normalizedCentralGammaIntegral chi U rho Y
        (detectorVerticalCutoff R)‖ := by
  apply detector_norm_dichotomy_of_error
    (norm_paper_scale_detector_truncation_error_le_polynomial_height
      chi hchi hU hrho hbetaLow hbetaHigh hY hUN hB)
  have hnorm : ‖(Real.exp (-(1 / Y)) : ℂ)‖ =
      Real.exp (-(1 / Y)) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-(1 / Y)))]
  rw [hnorm]
  exact hbudget

/-- End-to-end repaired detector alternative, with the Type-II branch
extracted at one literal critical-line point. -/
theorem post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + a + b ≤
        Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        b / ((1 / (2 * Real.pi)) *
            truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) ≤
          ‖DirichletCharacter.LFunction chi
              (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) *
            mollifier chi U
              (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases post_A5_quantitative_detector_dichotomy_polynomial_height
    chi hchi hU hrho hbetaLow hbetaHigh hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ :=
      exists_criticalLine_large_value_div_mass_of_central chi hchi U
        hbetaLow hbetaHigh (lt_of_lt_of_le zero_lt_one hY)
        (lt_of_lt_of_le zero_lt_one hB) hII
    refine ⟨t, ht, ?_⟩
    simpa only [criticalLineProductNorm_eq] using htlarge

/-- Final repaired L-function-only pointwise Type-II extraction. -/
theorem post_A5_quantitative_detector_dichotomy_with_LFunction_large_value_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + a + b ≤
        Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        b / (((1 / (2 * Real.pi)) *
            truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) *
              (U + 1)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases
      post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value_polynomial_height
        chi hchi hU hrho hbetaLow hbetaHigh hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    refine ⟨t, ht, ?_⟩
    have hL := lFunction_norm_lower_of_criticalLineProduct chi U rho t
      (V := b / ((1 / (2 * Real.pi)) *
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)))
      (by simpa only [criticalLineProductNorm_eq] using htlarge)
    simpa only [div_div] using hL

/-- The repaired bridge-facing conclusion is exactly the existing Type-I or
critical-line large-value alternative; no downstream target is weakened. -/
theorem post_A5_budgeted_fixedCharacter_detector_to_largeValue_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {κ η : ℝ} (_hκ : 0 < κ) (_hη : 0 < η)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R +
          Real.rpow R (-CGLProofDAG.inputLoss κ η) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
        Real.exp (-(1 / Y))) :
    Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
        ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  let V : ℝ := Real.rpow R (-CGLProofDAG.inputLoss κ η)
  let D : ℝ :=
    ((1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) * (U + 1)
  have hbetaHalf : 1 / 2 < rho.re := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hBpos : 0 < detectorVerticalCutoff R := lt_of_lt_of_le zero_lt_one hB
  have hmasspos : 0 < truncatedGammaLeftKernelMass rho Y
      (detectorVerticalCutoff R) :=
    truncatedGammaLeftKernelMass_pos hbetaHalf hbetaHigh hYpos hBpos
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (by positivity) hmasspos) (by positivity)
  have hDle : D ≤ 29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
    dsimp [D]
    exact normalized_truncatedGammaLeftKernelMass_le_uniform
      hbetaLow hbetaHigh U hY (by linarith)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Real.rpow_pos_of_pos hR _
  rcases
      post_A5_quantitative_detector_dichotomy_with_LFunction_large_value_polynomial_height
        chi hchi hU hrho hbetaHalf hbetaHigh hY hUN hB
        (a := V)
        (b := 29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V)
        (by simpa [V] using hbudget) with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    refine ⟨t, ht, ?_⟩
    apply (show V ≤
        (29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V) / D by
      rw [le_div_iff₀ hDpos]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hDle hVpos.le) |>.trans
    simpa [V, D] using htlarge

end
end MAPAppendixA4RecenteredGammaRepair

#print axioms MAPAppendixA4RecenteredGammaRepair.recenteredGammaLeftIntegrand_eq
#print axioms MAPAppendixA4RecenteredGammaRepair.normalizedCentralGammaIntegral_eq_recentered
#print axioms MAPAppendixA4RecenteredGammaRepair.norm_gammaLeftIntegrand_le_exp_polynomial_height
#print axioms MAPAppendixA4RecenteredGammaRepair.norm_gammaLeftIntegrand_two_tails_le_exp_polynomial_height
#print axioms MAPAppendixA4RecenteredGammaRepair.norm_paper_scale_detector_truncation_error_le_polynomial_height
#print axioms MAPAppendixA4RecenteredGammaRepair.post_A5_quantitative_detector_dichotomy_polynomial_height
#print axioms MAPAppendixA4RecenteredGammaRepair.post_A5_budgeted_fixedCharacter_detector_to_largeValue_polynomial_height
