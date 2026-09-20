import GammaCompactStrip
import Mathlib.Analysis.Complex.PhragmenLindelof

open Complex Filter Topology Asymptotics Real Set MeasureTheory
open scoped Real

namespace PLInteriorGrowth

noncomputable section

/-- A deliberately coarse complex sine bound, sufficient for Gamma reflection. -/
theorem norm_complex_sin_le_exp_abs_im (z : ℂ) :
    ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat]
  have hsub : ‖Complex.exp (-z * Complex.I) - Complex.exp (z * Complex.I)‖ ≤
      ‖Complex.exp (-z * Complex.I)‖ + ‖Complex.exp (z * Complex.I)‖ :=
    norm_sub_le _ _
  have hneg : ‖Complex.exp (-z * Complex.I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hpos : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [hneg, hpos] at hsub
  have hz1 : Real.exp z.im ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self _)
  have hz2 : Real.exp (-z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs _)
  nlinarith

private lemma one_sub_stripPoint_eq (a t : ℝ) :
    1 - GammaCompactStripScratch.stripPoint a t =
      GammaCompactStripScratch.stripPoint (1 - a) (-t) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]

private lemma stripPoint_not_neg_nat_of_abs_im
    {a t : ℝ} (ht : 1 ≤ |t|) (n : ℕ) :
    GammaCompactStripScratch.stripPoint a t ≠ -(n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [GammaCompactStripScratch.stripPoint] at him
  subst t
  norm_num at ht

/-- Reciprocal Gamma has at most single-exponential growth on the compact
positive strip.  This is obtained from the reflection identity and the
certified compact-strip Gamma decay, without Stirling. -/
theorem norm_inv_Gamma_positive_strip_le
    {a t : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      12 * (1 + |t|) * Real.exp (Real.pi * |t|) := by
  let w := GammaCompactStripScratch.stripPoint a t
  have hwne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero (stripPoint_not_neg_nat_of_abs_im ht)
  have h1wne : Complex.Gamma (1 - w) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [w, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have href := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at href
    exact (mul_ne_zero hwne h1wne) href
  have heq : (Complex.Gamma w)⁻¹ =
      Complex.Gamma (1 - w) * Complex.sin ((Real.pi : ℂ) * w) / Real.pi := by
    apply (mul_left_cancel₀ hwne)
    rw [mul_inv_cancel₀ hwne, mul_div_assoc, ← mul_assoc, href]
    field_simp [hsin, Real.pi_ne_zero]
  have hgamma : ‖Complex.Gamma (1 - w)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) := by
    rw [one_sub_stripPoint_eq]
    simpa [abs_neg] using
      GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
        (a := 1 - a) (t := -t) (by linarith) (by linarith) (by simpa [abs_neg])
  have hsinb : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤
      Real.exp (Real.pi * |t|) := by
    have hs := norm_complex_sin_le_exp_abs_im ((Real.pi : ℂ) * w)
    have him : (((Real.pi : ℂ) * w).im) = Real.pi * t := by
      simp [w, GammaCompactStripScratch.stripPoint]
    rw [him, abs_mul, abs_of_pos Real.pi_pos] at hs
    exact hs
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnum : ‖Complex.Gamma (1 - w)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) * Real.exp (Real.pi * |t|) := by
    exact mul_le_mul hgamma hsinb (norm_nonneg _) (by positivity)
  calc
    ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin ((Real.pi : ℂ) * w)‖ / Real.pi ≤
        ‖Complex.Gamma (1 - w)‖ * ‖Complex.sin ((Real.pi : ℂ) * w)‖ :=
      div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpi
    _ ≤ 12 * (1 + |t|) * Real.exp (-|t|) * Real.exp (Real.pi * |t|) := hnum
    _ ≤ 12 * (1 + |t|) * Real.exp (Real.pi * |t|) := by
      have he : Real.exp (-|t|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith [abs_nonneg t])
      rw [show 12 * (1 + |t|) * Real.exp (-|t|) *
          Real.exp (Real.pi * |t|) =
          (12 * (1 + |t|) * Real.exp (Real.pi * |t|)) *
            Real.exp (-|t|) by ring]
      have hfront : 0 ≤ 12 * (1 + |t|) * Real.exp (Real.pi * |t|) := by
        positivity
      simpa using mul_le_mul_of_nonneg_left he hfront

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.norm_inv_Gamma_positive_strip_le
