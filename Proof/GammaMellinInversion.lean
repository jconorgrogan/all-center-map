import MellinDetectorLeaf
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Exact inverse Mellin formula for the exponential detector

This closes the Mellin-inversion part preceding Appendix (A.4).  The contour
shift and its horizontal/tail estimates remain separate.
-/

namespace MAPGammaMellinInversion

open Set MeasureTheory Real Complex
open scoped Interval

noncomputable section

/-- Two Gamma recurrences give a quadratic vertical bound on every positive
vertical line. -/
theorem im_sq_mul_norm_Gamma_vertical_le
    {sigma t : ℝ} (hsigma : 0 < sigma) :
    t ^ 2 * ‖Complex.Gamma ((sigma : ℂ) + t * Complex.I)‖ ≤
      Real.Gamma (sigma + 2) := by
  let z : ℂ := (sigma : ℂ) + t * Complex.I
  have hz : z ≠ 0 := by
    intro hz0
    have hre := congrArg Complex.re hz0
    simp [z] at hre
    linarith
  have hzadd : z + 1 ≠ 0 := by
    intro hz0
    have hre := congrArg Complex.re hz0
    simp [z] at hre
    linarith
  have hshift : 0 < (z + 2).re := by
    simp [z]
    linarith
  have hGamma := MAPMellinDetectorLeaf.norm_Gamma_le_realGamma_re hshift
  have hrec :
      Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
    calc
      Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by ring_nf
      _ = (z + 1) * Complex.Gamma (z + 1) :=
        Complex.Gamma_add_one (z + 1) hzadd
      _ = (z + 1) * z * Complex.Gamma z := by
        rw [Complex.Gamma_add_one z hz]
        simp only [mul_assoc]
  have hproduct :
      ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ ≤
        Real.Gamma (sigma + 2) := by
    rw [hrec, norm_mul, norm_mul] at hGamma
    have hre : (z + 2).re = sigma + 2 := by simp [z]
    rw [hre] at hGamma
    exact hGamma
  have himz : |t| ≤ ‖z‖ := by
    simpa [z] using Complex.abs_im_le_norm z
  have himzadd : |t| ≤ ‖z + 1‖ := by
    simpa [z] using Complex.abs_im_le_norm (z + 1)
  have himsq : t ^ 2 ≤ ‖z + 1‖ * ‖z‖ := by
    rw [← sq_abs, pow_two]
    exact mul_le_mul himzadd himz (abs_nonneg t) (norm_nonneg (z + 1))
  exact (mul_le_mul_of_nonneg_right himsq (norm_nonneg _)).trans hproduct

/-- An integrable Cauchy majorant for Gamma on a positive vertical line. -/
theorem norm_Gamma_vertical_le_inv_one_add_sq
    {sigma t : ℝ} (hsigma : 0 < sigma) :
    ‖Complex.Gamma ((sigma : ℂ) + t * Complex.I)‖ ≤
      (Real.Gamma sigma + Real.Gamma (sigma + 2)) * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (sigma : ℂ) + t * Complex.I
  have hzre : z.re = sigma := by simp [z]
  have hzero := MAPMellinDetectorLeaf.norm_Gamma_le_realGamma_re
    (s := z) (by simpa [hzre] using hsigma)
  rw [hzre] at hzero
  have hsquare := im_sq_mul_norm_Gamma_vertical_le hsigma (t := t)
  have hden : 0 < 1 + t ^ 2 := by positivity
  change ‖Complex.Gamma z‖ ≤
    (Real.Gamma sigma + Real.Gamma (sigma + 2)) / (1 + t ^ 2)
  rw [le_div_iff₀ hden]
  calc
    ‖Complex.Gamma z‖ * (1 + t ^ 2) =
        ‖Complex.Gamma z‖ + t ^ 2 * ‖Complex.Gamma z‖ := by ring
    _ ≤ Real.Gamma sigma + Real.Gamma (sigma + 2) :=
      add_le_add hzero hsquare

/-- Gamma is vertically integrable on every line `Re s = sigma > 0`.
Mathlib does not currently expose this specialization directly. -/
theorem verticalIntegrable_Gamma {sigma : ℝ} (hsigma : 0 < sigma) :
    Complex.VerticalIntegrable Complex.Gamma sigma := by
  let C : ℝ := Real.Gamma sigma + Real.Gamma (sigma + 2)
  have hmajor : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  have hcontinuous : Continuous (fun t : ℝ =>
      Complex.Gamma ((sigma : ℂ) + t * Complex.I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : ContinuousAt (fun u : ℝ =>
        (sigma : ℂ) + u * Complex.I) t := by fun_prop
    exact (Complex.continuousAt_Gamma _ (fun m h => by
      have hre := congrArg Complex.re h
      simp at hre
      linarith)).comp_of_eq hinner rfl
  exact hmajor.mono' hcontinuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => by
      simpa [C] using norm_Gamma_vertical_le_inv_one_add_sq hsigma (t := t))

/-- The exponentially decaying profile is Mellin convergent in every positive
strip. -/
theorem mellinConvergent_exp_neg {sigma : ℝ} (hsigma : 0 < sigma) :
    MellinConvergent (fun x : ℝ => (Real.exp (-x) : ℂ)) (sigma : ℂ) := by
  have h := Complex.GammaIntegral_convergent (s := (sigma : ℂ)) (by simpa using hsigma)
  simpa only [MellinConvergent, smul_eq_mul, mul_comm] using h

/-- The Mellin transform of `exp(-x)` is vertically integrable on a positive
line, via its pointwise identification with Gamma there. -/
theorem verticalIntegrable_mellin_exp_neg {sigma : ℝ} (hsigma : 0 < sigma) :
    Complex.VerticalIntegrable
      (mellin fun x : ℝ => (Real.exp (-x) : ℂ)) sigma := by
  have hGamma := verticalIntegrable_Gamma hsigma
  apply hGamma.congr
  filter_upwards [] with t
  rw [← Complex.GammaIntegral_eq_mellin]
  have hsline : 0 < (((sigma : ℂ) + t * Complex.I).re) := by
    simpa using hsigma
  exact Complex.Gamma_eq_integral hsline

/-- Exact inverse Mellin formula with the `GammaIntegral` presentation. -/
theorem mellinInv_GammaIntegral_eq_exp_neg
    {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    mellinInv sigma Complex.GammaIntegral x = (Real.exp (-x) : ℂ) := by
  rw [Complex.GammaIntegral_eq_mellin]
  exact mellinInv_mellin_eq sigma (fun y : ℝ => (Real.exp (-y) : ℂ)) hx
    (mellinConvergent_exp_neg hsigma)
    (verticalIntegrable_mellin_exp_neg hsigma)
    ((Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp continuous_neg)).continuousAt)

/-- Exact inverse Mellin formula with the meromorphic Gamma function used in
Appendix (A.4). -/
theorem mellinInv_Gamma_eq_exp_neg
    {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    mellinInv sigma Complex.Gamma x = (Real.exp (-x) : ℂ) := by
  have hGI := mellinInv_GammaIntegral_eq_exp_neg hsigma hx
  rw [mellinInv] at hGI
  rw [mellinInv]
  have hInt :
      (∫ t : ℝ, (x : ℂ) ^ (-(sigma + t * Complex.I)) •
          Complex.Gamma (sigma + t * Complex.I)) =
        ∫ t : ℝ, (x : ℂ) ^ (-(sigma + t * Complex.I)) •
          Complex.GammaIntegral (sigma + t * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    have hsline : 0 < (((sigma : ℂ) + t * Complex.I).re) := by
      simpa using hsigma
    rw [Complex.Gamma_eq_integral hsline]
  rw [hInt]
  exact hGI

/-- The inverse Mellin theorem expanded with the exact number-theoretic
`1/(2*pi)` vertical-line normalization. -/
theorem exp_neg_eq_gamma_vertical_integral
    {sigma x : ℝ} (hsigma : 0 < sigma) (hx : 0 < x) :
    (Real.exp (-x) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, Complex.Gamma ((sigma : ℂ) + t * Complex.I) *
          (x : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))) := by
  have h := (mellinInv_Gamma_eq_exp_neg hsigma hx).symm
  rw [mellinInv] at h
  convert h
  simp [smul_eq_mul, mul_comm]

/-- Reversing a positive real quotient turns the negative Mellin exponent
into the positive exponent used in Appendix (A.4). -/
theorem cpow_neg_div_eq_reverse_cpow
    {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) (z : ℂ) :
    ((x / Y : ℝ) : ℂ) ^ (-z) = ((Y / x : ℝ) : ℂ) ^ z := by
  have hxy : 0 < x / Y := div_pos hx hY
  have harg : (((x / Y : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hxy.le]
    exact ne_of_lt Real.pi_pos
  have hbase : ((Y / x : ℝ) : ℂ) = (((x / Y : ℝ) : ℂ))⁻¹ := by
    push_cast
    rw [inv_div]
  rw [Complex.cpow_neg]
  rw [hbase]
  exact (Complex.inv_cpow (((x / Y : ℝ) : ℂ)) z harg).symm

/-- Literal unshifted detector identity for one positive integer coefficient:
`exp(-n/Y)` is the Gamma integral on `Re z = sigma`.  This is the right-hand
line that is shifted in Appendix (A.4). -/
theorem exp_neg_nat_div_eq_detector_right_line
    {sigma Y : ℝ} {n : ℕ} (hsigma : 0 < sigma)
    (hY : 0 < Y) (hn : 0 < n) :
    (Real.exp (-((n : ℝ) / Y)) : ℂ) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t : ℝ, Complex.Gamma ((sigma : ℂ) + t * Complex.I) *
          ((Y / n : ℝ) : ℂ) ^ ((sigma : ℂ) + t * Complex.I)) := by
  have hratio : 0 < (n : ℝ) / Y := div_pos (by exact_mod_cast hn) hY
  have h := exp_neg_eq_gamma_vertical_integral hsigma hratio
  calc
    (Real.exp (-((n : ℝ) / Y)) : ℂ) =
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, Complex.Gamma ((sigma : ℂ) + t * Complex.I) *
            (((n : ℝ) / Y : ℝ) : ℂ) ^
              (-((sigma : ℂ) + t * Complex.I))) := h
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [cpow_neg_div_eq_reverse_cpow (by exact_mod_cast hn) hY]

end
end MAPGammaMellinInversion

#print axioms MAPGammaMellinInversion.verticalIntegrable_Gamma
#print axioms MAPGammaMellinInversion.mellinInv_Gamma_eq_exp_neg
#print axioms MAPGammaMellinInversion.exp_neg_nat_div_eq_detector_right_line
