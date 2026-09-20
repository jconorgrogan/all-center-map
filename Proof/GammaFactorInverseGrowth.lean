import GammaInverseGrowth
import Mathlib.NumberTheory.LSeries.DirichletContinuation

open Complex Real
open scoped Real

namespace PLInteriorGrowth

noncomputable section

private lemma eq_stripPoint_re_im (z : ℂ) :
    z = GammaCompactStripScratch.stripPoint z.re z.im := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]

private lemma norm_stripPoint_le_one_add_abs {a t : ℝ} (ha : |a| ≤ 1 / 2) :
    ‖GammaCompactStripScratch.stripPoint a t‖ ≤ 1 + |t| := by
  calc
    ‖GammaCompactStripScratch.stripPoint a t‖ ≤ |a| + |t| := by
      simpa [GammaCompactStripScratch.stripPoint] using
        Complex.norm_le_abs_re_add_abs_im
          (GammaCompactStripScratch.stripPoint a t)
    _ ≤ 1 + |t| := by linarith

/-- Reciprocal Gamma on the range needed for the even Dirichlet gamma factor.
The only input beyond algebra is the positive-strip reflection bound. -/
theorem norm_inv_Gamma_neg_half_one_le
    {a t : ℝ} (ha : -(1 / 2 : ℝ) ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      12 * (1 + |t|) ^ 2 * Real.exp (Real.pi * |t|) := by
  by_cases hlow : a < 1 / 2
  · have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one
        (GammaCompactStripScratch.stripPoint a t)
    rw [GammaCompactStripScratch.stripPoint_add_one] at hrec
    rw [hrec, norm_mul]
    have hpos := norm_inv_Gamma_positive_strip_le
      (a := a + 1) (t := t) (by linarith) (by linarith) ht
    have haabs : |a| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    have hz := norm_stripPoint_le_one_add_abs (t := t) haabs
    calc
      ‖GammaCompactStripScratch.stripPoint a t‖ *
          ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint (a + 1) t))⁻¹‖
          ≤ (1 + |t|) * (12 * (1 + |t|) * Real.exp (Real.pi * |t|)) :=
        mul_le_mul hz hpos (norm_nonneg _) (by positivity)
      _ = 12 * (1 + |t|) ^ 2 * Real.exp (Real.pi * |t|) := by ring
  · have hpos := norm_inv_Gamma_positive_strip_le
      (a := a) (t := t) (by linarith) (by linarith) ht
    have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    calc
      ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖
          ≤ 12 * (1 + |t|) * Real.exp (Real.pi * |t|) := hpos
      _ ≤ 12 * (1 + |t|) ^ 2 * Real.exp (Real.pi * |t|) := by
        have hsquare : 1 + |t| ≤ (1 + |t|) ^ 2 := by nlinarith
        gcongr

/-- Reciprocal Gamma on the slightly wider positive range needed after the odd
parity shift.  The upper half is reduced by the Gamma recurrence. -/
theorem norm_inv_Gamma_half_two_le
    {a t : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2) (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      12 * (1 + |t|) * Real.exp (Real.pi * |t|) := by
  by_cases hupper : a ≤ 3 / 2
  · exact norm_inv_Gamma_positive_strip_le ha hupper ht
  · let z := GammaCompactStripScratch.stripPoint (a - 1) t
    have hz_ne : z ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [z, GammaCompactStripScratch.stripPoint] at him
      subst t
      norm_num at ht
    have hrec := Complex.Gamma_add_one z hz_ne
    have hadd : z + 1 = GammaCompactStripScratch.stripPoint a t := by
      apply Complex.ext <;> simp [z, GammaCompactStripScratch.stripPoint]
    rw [hadd] at hrec
    have hinv : (Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹ =
        z⁻¹ * (Complex.Gamma z)⁻¹ := by
      rw [hrec, mul_inv_rev, mul_comm]
    rw [hinv, norm_mul]
    have hz_inv : ‖z⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      have hz_norm : 1 ≤ ‖z‖ := ht.trans (by
        simpa [z, GammaCompactStripScratch.stripPoint] using Complex.abs_im_le_norm z)
      exact inv_le_one_of_one_le₀ hz_norm
    have hbase := norm_inv_Gamma_positive_strip_le
      (a := a - 1) (t := t) (by linarith) (by linarith) ht
    calc
      ‖z⁻¹‖ * ‖(Complex.Gamma z)⁻¹‖ ≤
          1 * (12 * (1 + |t|) * Real.exp (Real.pi * |t|)) :=
        mul_le_mul hz_inv (by simpa [z] using hbase) (norm_nonneg _) (by norm_num)
      _ = 12 * (1 + |t|) * Real.exp (Real.pi * |t|) := by ring

private theorem norm_pi_cpow_half_le_sixteen {s : ℂ} (hs : s.re ≤ 3) :
    ‖(Real.pi : ℂ) ^ (s / 2)‖ ≤ 16 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have hre : (s / 2).re ≤ 2 := by simp; linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le
    (by linarith [Real.pi_gt_three] : (1 : ℝ) ≤ Real.pi) hre
  rw [Real.rpow_two] at hmono
  nlinarith [Real.pi_le_four, Real.pi_pos]

/-- The inverse Deligne real gamma factor has single-exponential growth on the
fixed strip.  Constants are intentionally crude: this theorem only supplies
Phragmen--Lindelof's global-growth premise. -/
theorem norm_inv_GammaReal_fixedStrip_le
    {s : ℂ} (hslo : -1 ≤ s.re) (hshi : s.re ≤ 3) (ht : 2 ≤ |s.im|) :
    ‖(Complex.Gammaℝ s)⁻¹‖ ≤
      192 * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
  rw [Complex.Gammaℝ_def, mul_inv_rev, norm_mul, mul_comm]
  have hpow : ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ ≤ 16 := by
    rw [show -s / 2 = -(s / 2) by ring, Complex.cpow_neg, inv_inv]
    exact norm_pi_cpow_half_le_sixteen hshi
  have him : |(s / 2).im| = |s.im| / 2 := by
    simp [abs_div]
  have ht' : 1 ≤ |(s / 2).im| := by rw [him]; linarith
  have hrelo : -(1 / 2 : ℝ) ≤ (s / 2).re := by simp; linarith
  have hrehi : (s / 2).re ≤ 3 / 2 := by simp; linarith
  have hgamma := norm_inv_Gamma_neg_half_one_le
    (a := (s / 2).re) (t := (s / 2).im) hrelo hrehi ht'
  rw [← eq_stripPoint_re_im (s / 2)] at hgamma
  calc
    ‖((Real.pi : ℂ) ^ (-s / 2))⁻¹‖ * ‖(Complex.Gamma (s / 2))⁻¹‖
        ≤ 16 * (12 * (1 + |(s / 2).im|) ^ 2 *
          Real.exp (Real.pi * |(s / 2).im|)) :=
      mul_le_mul hpow hgamma (norm_nonneg _) (by positivity)
    _ ≤ 192 * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
      rw [him]
      have habs : 0 ≤ |s.im| := abs_nonneg _
      have hpoly : (1 + |s.im| / 2) ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith
      have hexp : Real.exp (Real.pi * (|s.im| / 2)) ≤
          Real.exp (Real.pi * |s.im|) := Real.exp_le_exp.mpr (by
            nlinarith [Real.pi_pos])
      calc
        16 * (12 * (1 + |s.im| / 2) ^ 2 * Real.exp (Real.pi * (|s.im| / 2))) =
            192 * (1 + |s.im| / 2) ^ 2 * Real.exp (Real.pi * (|s.im| / 2)) := by ring
        _ ≤ 192 * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
          gcongr

/-- The actual parity-dependent Dirichlet gamma factor obeys the same kind of
single-exponential strip bound. -/
theorem norm_inv_gammaFactor_fixedStrip_le
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hslo : -1 ≤ s.re) (hshi : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖(DirichletCharacter.gammaFactor χ s)⁻¹‖ ≤
      192 * (1 + |s.im|) ^ 2 * Real.exp (Real.pi * |s.im|) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact norm_inv_GammaReal_fixedStrip_le hslo (by linarith) ht
  · rw [hχ.gammaFactor_def]
    have h := norm_inv_GammaReal_fixedStrip_le (s := s + 1)
      (by simp; linarith) (by simp; linarith) (by simpa using ht)
    simpa using h

end

end PLInteriorGrowth

#print axioms PLInteriorGrowth.norm_inv_gammaFactor_fixedStrip_le
