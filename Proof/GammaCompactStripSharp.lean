import GammaCompactStrip

/-!
# Sharp exponential rate for Gamma on the compact strip

`GammaCompactStrip` deliberately weakened the exact central-line decay from
`exp (-pi |t| / 2)` to `exp (-|t|)`.  Huxley's reflected contour needs the
sharp rate because it cancels the exponential growth from the reflection
sine.  This module retains that rate using only Mathlib's exact Gamma
reflection identity, elementary hyperbolic identities, recurrence, and the
already certified beta-integral strip comparison.  No version of Stirling's
formula is assumed.
-/

namespace MAPGammaCompactStripSharp

open Complex Real

noncomputable section

def centralPoint (t : ℝ) : ℂ := (1 / 2 : ℝ) + t * I

private theorem one_sub_centralPoint (t : ℝ) :
    1 - centralPoint t = starRingEnd ℂ (centralPoint t) := by
  apply Complex.ext <;> simp [centralPoint]
  norm_num

private theorem sin_pi_mul_centralPoint (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * centralPoint t) =
      (Real.cosh (Real.pi * t) : ℂ) := by
  rw [show (Real.pi : ℂ) * centralPoint t =
      (Real.pi : ℂ) / 2 + (Real.pi * t : ℝ) * I by
    apply Complex.ext <;> simp [centralPoint] <;> ring]
  rw [Complex.sin_add_mul_I, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two, one_mul, zero_mul]
  simpa using (Complex.ofReal_cosh (Real.pi * t)).symm

/-- Exact central-line norm identity. -/
theorem norm_Gamma_centralPoint_sq (t : ℝ) :
    ‖Complex.Gamma (centralPoint t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  have href := Complex.Gamma_mul_Gamma_one_sub (centralPoint t)
  rw [one_sub_centralPoint, Complex.Gamma_conj] at href
  have hnorm := congrArg norm href
  rw [norm_mul, RCLike.norm_conj, norm_div,
    sin_pi_mul_centralPoint] at hnorm
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hcosh : ‖(Real.cosh (Real.pi * t) : ℂ)‖ =
      Real.cosh (Real.pi * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  rw [hpi, hcosh] at hnorm
  simpa [pow_two] using hnorm

/-- Sharp-rate central-line Gamma bound.  The constant `3` is only a
convenient rational majorant for `sqrt (2*pi)`. -/
theorem norm_Gamma_centralPoint_le_exp_pi_half (t : ℝ) :
    ‖Complex.Gamma (centralPoint t)‖ ≤
      3 * Real.exp (-(Real.pi / 2) * |t|) := by
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hsq := norm_Gamma_centralPoint_sq t
  have hcosh := GammaCompactStripScratch.exp_abs_le_two_mul_cosh
    (Real.pi * t)
  have habs : |Real.pi * t| = Real.pi * |t| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [habs] at hcosh
  have hsq_le :
      ‖Complex.Gamma (centralPoint t)‖ ^ 2 ≤
        2 * Real.pi * Real.exp (-(Real.pi * |t|)) := by
    rw [hsq]
    have hexp_pos := Real.exp_pos (Real.pi * |t|)
    rw [Real.exp_neg]
    change Real.pi / Real.cosh (Real.pi * t) ≤
      (2 * Real.pi) / Real.exp (Real.pi * |t|)
    apply (div_le_div_iff₀ hcosh_pos hexp_pos).2
    nlinarith [Real.pi_pos]
  have hpi_bound : 2 * Real.pi ≤ 9 := by
    nlinarith [Real.pi_le_four]
  have hexp_sq :
      Real.exp (-(Real.pi * |t|)) =
        Real.exp (-(Real.pi / 2) * |t|) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsq_final :
      ‖Complex.Gamma (centralPoint t)‖ ^ 2 ≤
        (3 * Real.exp (-(Real.pi / 2) * |t|)) ^ 2 := by
    rw [hexp_sq] at hsq_le
    nlinarith [Real.exp_pos (-(Real.pi / 2) * |t|)]
  nlinarith [norm_nonneg (Complex.Gamma (centralPoint t)),
    Real.exp_pos (-(Real.pi / 2) * |t|)]

private theorem centralPoint_add_one (t : ℝ) :
    centralPoint t + 1 =
      GammaCompactStripScratch.stripPoint (3 / 2) t := by
  apply Complex.ext <;> simp [centralPoint, GammaCompactStripScratch.stripPoint]
  norm_num

private theorem norm_centralPoint_le_one_add_abs (t : ℝ) :
    ‖centralPoint t‖ ≤ 1 + |t| := by
  calc
    ‖centralPoint t‖ ≤ |(centralPoint t).re| + |(centralPoint t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + |t| := by simp [centralPoint]
    _ ≤ 1 + |t| := by linarith

/-- Sharp-rate bound on the upper comparison line `Re z = 3/2`. -/
theorem norm_Gamma_upperPoint_le_exp_pi_half (t : ℝ) :
    ‖Complex.Gamma
        (GammaCompactStripScratch.stripPoint (3 / 2) t)‖ ≤
      3 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  have hcentral_ne : centralPoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [centralPoint] at hre
  have hrec := Complex.Gamma_add_one (centralPoint t) hcentral_ne
  rw [centralPoint_add_one] at hrec
  have hnorm := congrArg norm hrec
  rw [norm_mul] at hnorm
  rw [hnorm]
  calc
    ‖centralPoint t‖ * ‖Complex.Gamma (centralPoint t)‖ ≤
        (1 + |t|) *
          (3 * Real.exp (-(Real.pi / 2) * |t|)) :=
      mul_le_mul (norm_centralPoint_le_one_add_abs t)
        (norm_Gamma_centralPoint_le_exp_pi_half t) (norm_nonneg _) (by positivity)
    _ = 3 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by ring

/-- Sharp exponential rate throughout `1/2 <= Re z <= 3/2`. -/
theorem norm_Gamma_positive_strip_le_exp_pi_half
    {a t : ℝ} (halo : 1 / 2 ≤ a) (hahi : a ≤ 3 / 2) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  calc
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
        4 * ‖Complex.Gamma
          (GammaCompactStripScratch.stripPoint (3 / 2) t)‖ :=
      GammaCompactStripScratch.norm_Gamma_stripPoint_le_four_upper halo hahi
    _ ≤ 4 * (3 * (1 + |t|) *
        Real.exp (-(Real.pi / 2) * |t|)) := by
      gcongr
      exact norm_Gamma_upperPoint_le_exp_pi_half t
    _ = 12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by ring

/-- Sharp exponential rate on `-1/2 <= Re z <= 1/2`, obtained by one
Gamma recurrence from the positive strip. -/
theorem norm_Gamma_compactStrip_le_exp_pi_half
    {a t : ℝ} (halo : -(1 / 2 : ℝ) ≤ a) (hahi : a ≤ 1 / 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  have hz_ne : GammaCompactStripScratch.stripPoint a t ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp [GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hrec := Complex.Gamma_add_one
    (GammaCompactStripScratch.stripPoint a t) hz_ne
  rw [GammaCompactStripScratch.stripPoint_add_one] at hrec
  have hnormrec := congrArg norm hrec
  rw [norm_mul] at hnormrec
  have hnormz : 1 ≤ ‖GammaCompactStripScratch.stripPoint a t‖ := by
    exact ht.trans (by
      simpa [GammaCompactStripScratch.stripPoint] using
        Complex.abs_im_le_norm (GammaCompactStripScratch.stripPoint a t))
  have hshift :
      ‖Complex.Gamma (GammaCompactStripScratch.stripPoint (a + 1) t)‖ ≤
        12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    apply norm_Gamma_positive_strip_le_exp_pi_half
    · linarith
    · linarith
  have hbase :
      ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
        ‖Complex.Gamma
          (GammaCompactStripScratch.stripPoint (a + 1) t)‖ := by
    rw [hnormrec]
    nlinarith [norm_nonneg
      (Complex.Gamma (GammaCompactStripScratch.stripPoint a t))]
  exact hbase.trans hshift

end

end MAPGammaCompactStripSharp

#print axioms MAPGammaCompactStripSharp.norm_Gamma_centralPoint_sq
#print axioms MAPGammaCompactStripSharp.norm_Gamma_centralPoint_le_exp_pi_half
#print axioms MAPGammaCompactStripSharp.norm_Gamma_upperPoint_le_exp_pi_half
#print axioms MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
#print axioms MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
