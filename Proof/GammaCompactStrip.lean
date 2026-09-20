import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds

open Set MeasureTheory
open scoped Real

namespace GammaCompactStripScratch

noncomputable section

private def centralPoint (t : ℝ) : ℂ := (1 / 2 : ℝ) + t * Complex.I

lemma one_sub_centralPoint (t : ℝ) :
    1 - centralPoint t = (starRingEnd ℂ) (centralPoint t) := by
  apply Complex.ext <;> simp [centralPoint]
  norm_num

lemma sin_pi_mul_centralPoint (t : ℝ) :
    Complex.sin ((Real.pi : ℂ) * centralPoint t) = (Real.cosh (Real.pi * t) : ℂ) := by
  rw [show (Real.pi : ℂ) * centralPoint t =
      (Real.pi : ℂ) / 2 + (Real.pi * t : ℝ) * Complex.I by
    apply Complex.ext <;> simp [centralPoint]
    <;> ring]
  rw [Complex.sin_add_mul_I, Complex.sin_pi_div_two,
    Complex.cos_pi_div_two, one_mul, zero_mul]
  simpa using (Complex.ofReal_cosh (Real.pi * t)).symm

lemma norm_Gamma_centralPoint_sq (t : ℝ) :
    ‖Complex.Gamma (centralPoint t)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * t) := by
  have href := Complex.Gamma_mul_Gamma_one_sub (centralPoint t)
  rw [one_sub_centralPoint, Complex.Gamma_conj] at href
  have hnorm := congrArg norm href
  rw [norm_mul, RCLike.norm_conj, norm_div,
    sin_pi_mul_centralPoint] at hnorm
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hcosh : ‖(Real.cosh (Real.pi * t) : ℂ)‖ = Real.cosh (Real.pi * t) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _)]
  rw [hpi, hcosh] at hnorm
  simpa [pow_two] using hnorm

lemma two_mul_cosh_abs (x : ℝ) :
    2 * Real.cosh x = Real.exp |x| + Real.exp (-|x|) := by
  rw [← Real.cosh_abs x, Real.cosh_eq]
  ring

lemma exp_abs_le_two_mul_cosh (x : ℝ) :
    Real.exp |x| ≤ 2 * Real.cosh x := by
  rw [two_mul_cosh_abs]
  exact le_add_of_nonneg_right (Real.exp_pos _).le

lemma norm_Gamma_centralPoint_le_exp (t : ℝ) :
    ‖Complex.Gamma (centralPoint t)‖ ≤ 3 * Real.exp (-|t|) := by
  have hcosh_pos : 0 < Real.cosh (Real.pi * t) := Real.cosh_pos _
  have hsq := norm_Gamma_centralPoint_sq t
  have hcosh := exp_abs_le_two_mul_cosh (Real.pi * t)
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
  have hpi_two : (2 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hexp_cmp : Real.exp (-(Real.pi * |t|)) ≤ Real.exp (-2 * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [abs_nonneg t]
  have hpi_bound : 2 * Real.pi ≤ 9 := by nlinarith [Real.pi_le_four]
  have hsq_final :
      ‖Complex.Gamma (centralPoint t)‖ ^ 2 ≤
        (3 * Real.exp (-|t|)) ^ 2 := by
    calc
      ‖Complex.Gamma (centralPoint t)‖ ^ 2
          ≤ 2 * Real.pi * Real.exp (-(Real.pi * |t|)) := hsq_le
      _ ≤ 2 * Real.pi * Real.exp (-2 * |t|) := by
        gcongr
      _ ≤ 9 * Real.exp (-2 * |t|) := by
        gcongr
      _ = (3 * Real.exp (-|t|)) ^ 2 := by
        rw [show -2 * |t| = -|t| + -|t| by ring, Real.exp_add]
        ring
  nlinarith [norm_nonneg (Complex.Gamma (centralPoint t)), Real.exp_pos (-|t|)]

lemma norm_betaIntegral_le_real_integral {u v : ℂ} :
    ‖Complex.betaIntegral u v‖ ≤
      ∫ x : ℝ in 0..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
  rw [Complex.betaIntegral]
  calc
    ‖∫ x : ℝ in 0..1,
        (x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ ≤
        ∫ x : ℝ in 0..1,
          ‖(x : ℂ) ^ (u - 1) * (1 - (x : ℂ)) ^ (v - 1)‖ :=
      intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ = ∫ x : ℝ in 0..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) := by
      apply intervalIntegral.integral_congr_ae
      have hne : ∀ᵐ x : ℝ, x ≠ 1 := by simp [ae_iff, measure_singleton]
      filter_upwards [hne] with x hxne
      intro hx
      simp only [uIoc_of_le zero_le_one] at hx
      rcases hx with ⟨hx0, hx1⟩
      have hx1lt : x < 1 := hx1.lt_of_ne hxne
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos (sub_pos.mpr hx1lt)]
      simp

lemma betaIntegral_ofReal_eq_ofReal_integral {s d : ℝ} :
    Complex.betaIntegral (s : ℂ) (d : ℂ) =
      (∫ x : ℝ in 0..1, x ^ (s - 1) * (1 - x) ^ (d - 1) : ℝ) := by
  rw [Complex.betaIntegral, ← intervalIntegral.integral_ofReal]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ x : ℝ, x ≠ 1 := by simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hxne
  intro hx
  simp only [uIoc_of_le zero_le_one] at hx
  rcases hx with ⟨hx0, hx1⟩
  have hx1lt : x < 1 := hx1.lt_of_ne hxne
  rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by norm_cast,
    show (d : ℂ) - 1 = ((d - 1 : ℝ) : ℂ) by norm_cast,
    show 1 - (x : ℂ) = ((1 - x : ℝ) : ℂ) by norm_cast]
  rw [← Complex.ofReal_cpow hx0.le,
    ← Complex.ofReal_cpow (sub_nonneg.mpr hx1lt.le)]
  push_cast
  rfl

lemma real_beta_integral_eq_Gamma_div {s d : ℝ}
    (hs : 0 < s) (hd : 0 < d) :
    (∫ x : ℝ in 0..1, x ^ (s - 1) * (1 - x) ^ (d - 1)) =
      Real.Gamma s * Real.Gamma d / Real.Gamma (s + d) := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div (s : ℂ) (d : ℂ)
    (by simpa using hs) (by simpa using hd)
  rw [betaIntegral_ofReal_eq_ofReal_integral,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal] at h
  have hG : Complex.Gamma ((s : ℂ) + (d : ℂ)) =
      (Real.Gamma (s + d) : ℂ) := by
    rw [← Complex.ofReal_add, Complex.Gamma_ofReal]
  rw [hG,
    ← Complex.ofReal_mul, ← Complex.ofReal_div] at h
  exact Complex.ofReal_inj.mp h

lemma norm_betaIntegral_le_Gamma_div {u v : ℂ}
    (hu : 0 < u.re) (hv : 0 < v.re) :
    ‖Complex.betaIntegral u v‖ ≤
      Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) := by
  calc
    ‖Complex.betaIntegral u v‖ ≤
        ∫ x : ℝ in 0..1, x ^ (u.re - 1) * (1 - x) ^ (v.re - 1) :=
      norm_betaIntegral_le_real_integral
    _ = Real.Gamma u.re * Real.Gamma v.re / Real.Gamma (u.re + v.re) :=
      real_beta_integral_eq_Gamma_div hu hv

lemma Gamma_half_sq : Real.Gamma (1 / 2) ^ 2 = Real.pi := by
  have h := Real.Gamma_mul_Gamma_one_sub (1 / 2 : ℝ)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
    show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
    Real.sin_pi_div_two, div_one] at h
  simpa [pow_two] using h

lemma one_le_Gamma_half : (1 : ℝ) ≤ Real.Gamma (1 / 2) := by
  have hpos := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  nlinarith [Gamma_half_sq, Real.pi_gt_three]

lemma Gamma_half_le_two : Real.Gamma (1 / 2) ≤ 2 := by
  have hpos := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  nlinarith [Gamma_half_sq, Real.pi_le_four]

lemma Gamma_real_Icc_half_three_half_le_two {s : ℝ}
    (hslo : 1 / 2 ≤ s) (hshi : s ≤ 3 / 2) :
    Real.Gamma s ≤ 2 := by
  by_cases hs_one : s ≤ 1
  · rcases hslo.eq_or_lt with hs_half | hs_half
    · subst s
      exact Gamma_half_le_two
    by_cases hseq_one : s = 1
    · subst s
      simp
    have hs_lt_one : s < 1 := lt_of_le_of_ne hs_one hseq_one
    let a : ℝ := 2 - 2 * s
    let b : ℝ := 2 * s - 1
    have ha : 0 < a := by dsimp [a]; linarith
    have hb : 0 < b := by dsimp [b]; linarith
    have hab : a + b = 1 := by dsimp [a, b]; ring
    have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
      (s := (1 / 2 : ℝ)) (t := 1) (a := a) (b := b)
      (by norm_num) (by norm_num) ha hb hab
    have harg : a * (1 / 2 : ℝ) + b * 1 = s := by
      dsimp [a, b]
      ring
    rw [harg, Real.Gamma_one, Real.one_rpow, mul_one] at hconv
    exact hconv.trans <| (Real.rpow_le_self_of_one_le one_le_Gamma_half (by
      dsimp [a]
      linarith)).trans Gamma_half_le_two
  · have hs_gt_one : 1 < s := lt_of_not_ge hs_one
    let a : ℝ := 2 - s
    let b : ℝ := s - 1
    have ha : 0 < a := by dsimp [a]; linarith
    have hb : 0 < b := by dsimp [b]; linarith
    have hab : a + b = 1 := by dsimp [a, b]; ring
    have hconv := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
      (s := (1 : ℝ)) (t := 2) (a := a) (b := b)
      (by norm_num) (by norm_num) ha hb hab
    have harg : a * (1 : ℝ) + b * 2 = s := by
      dsimp [a, b]
      ring
    rw [harg, Real.Gamma_one, Real.Gamma_two,
      Real.one_rpow, Real.one_rpow, mul_one] at hconv
    linarith

/-- The standard point `s + i t` on a vertical line. -/
def stripPoint (s t : ℝ) : ℂ := (s : ℂ) + t * Complex.I

lemma stripPoint_re (s t : ℝ) : (stripPoint s t).re = s := by simp [stripPoint]

lemma stripPoint_im (s t : ℝ) : (stripPoint s t).im = t := by simp [stripPoint]

lemma stripPoint_add_real (s d t : ℝ) :
    stripPoint s t + (d : ℂ) = stripPoint (s + d) t := by
  apply Complex.ext <;> simp [stripPoint]

lemma Gamma_three_half_ge_half : (1 / 2 : ℝ) ≤ Real.Gamma (3 / 2) := by
  have hrec := Real.Gamma_add_one (s := (1 / 2 : ℝ)) (by norm_num)
  rw [show (1 / 2 : ℝ) + 1 = 3 / 2 by norm_num] at hrec
  rw [hrec]
  nlinarith [one_le_Gamma_half]

lemma norm_Gamma_stripPoint_le_four_upper
    {s t : ℝ} (hslo : 1 / 2 ≤ s) (hshi : s ≤ 3 / 2) :
    ‖Complex.Gamma (stripPoint s t)‖ ≤
      4 * ‖Complex.Gamma (stripPoint (3 / 2) t)‖ := by
  rcases hshi.eq_or_lt with hs_eq | hs_lt
  · subst s
    nlinarith [norm_nonneg (Complex.Gamma (stripPoint (3 / 2) t))]
  let d : ℝ := 3 / 2 - s
  have hd : 0 < d := by dsimp [d]; linarith
  have hspos : 0 < s := lt_of_lt_of_le (by norm_num) hslo
  have hu_re : 0 < (stripPoint s t).re := by simpa [stripPoint] using hspos
  have hd_re : 0 < ((d : ℝ) : ℂ).re := by simpa using hd
  have hbeta := norm_betaIntegral_le_Gamma_div hu_re hd_re
  simp only [stripPoint_re, Complex.ofReal_re] at hbeta
  have hsd : s + d = 3 / 2 := by dsimp [d]; ring
  rw [hsd] at hbeta
  have hbeta_four :
      ‖Complex.betaIntegral (stripPoint s t) (d : ℂ)‖ ≤
        4 * Real.Gamma d := by
    calc
      ‖Complex.betaIntegral (stripPoint s t) (d : ℂ)‖
          ≤ Real.Gamma s * Real.Gamma d / Real.Gamma (3 / 2) := hbeta
      _ ≤ 4 * Real.Gamma d := by
        apply (div_le_iff₀ (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 3 / 2))).2
        have hsG := Gamma_real_Icc_half_three_half_le_two hslo hshi
        have hdG := Real.Gamma_pos_of_pos hd
        nlinarith [Gamma_three_half_ge_half]
  have hprod := Complex.Gamma_mul_Gamma_eq_betaIntegral hu_re hd_re
  rw [stripPoint_add_real, show s + d = 3 / 2 by dsimp [d]; ring] at hprod
  have hnorm := congrArg norm hprod
  rw [norm_mul, norm_mul] at hnorm
  have hGd : ‖Complex.Gamma (d : ℂ)‖ = Real.Gamma d := by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.Gamma_pos_of_pos hd)]
  rw [hGd] at hnorm
  have hupper_nonneg := norm_nonneg (Complex.Gamma (stripPoint (3 / 2) t))
  have hGd_pos := Real.Gamma_pos_of_pos hd
  nlinarith [mul_le_mul_of_nonneg_left hbeta_four hupper_nonneg]

lemma centralPoint_add_one (t : ℝ) :
    centralPoint t + 1 = stripPoint (3 / 2) t := by
  apply Complex.ext <;> simp [centralPoint, stripPoint]
  norm_num

lemma norm_centralPoint_le_one_add_abs (t : ℝ) :
    ‖centralPoint t‖ ≤ 1 + |t| := by
  calc
    ‖centralPoint t‖ ≤ |(centralPoint t).re| + |(centralPoint t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 / 2 + |t| := by simp [centralPoint]
    _ ≤ 1 + |t| := by linarith

lemma norm_Gamma_upperPoint_le_exp (t : ℝ) :
    ‖Complex.Gamma (stripPoint (3 / 2) t)‖ ≤
      3 * (1 + |t|) * Real.exp (-|t|) := by
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
    ‖centralPoint t‖ * ‖Complex.Gamma (centralPoint t)‖
        ≤ (1 + |t|) * (3 * Real.exp (-|t|)) :=
      mul_le_mul (norm_centralPoint_le_one_add_abs t)
        (norm_Gamma_centralPoint_le_exp t) (norm_nonneg _)
        (by positivity)
    _ = 3 * (1 + |t|) * Real.exp (-|t|) := by ring

lemma norm_Gamma_positive_strip_le_exp
    {s t : ℝ} (hslo : 1 / 2 ≤ s) (hshi : s ≤ 3 / 2) :
    ‖Complex.Gamma (stripPoint s t)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) := by
  calc
    ‖Complex.Gamma (stripPoint s t)‖ ≤
        4 * ‖Complex.Gamma (stripPoint (3 / 2) t)‖ :=
      norm_Gamma_stripPoint_le_four_upper hslo hshi
    _ ≤ 4 * (3 * (1 + |t|) * Real.exp (-|t|)) := by
      gcongr
      exact norm_Gamma_upperPoint_le_exp t
    _ = 12 * (1 + |t|) * Real.exp (-|t|) := by ring

lemma stripPoint_add_one (s t : ℝ) :
    stripPoint s t + 1 = stripPoint (s + 1) t := by
  apply Complex.ext <;> simp [stripPoint]

/-- Explicit compact-strip exponential Gamma bound obtained without Stirling.
The constants are `C = 12`, `E = 1`, and `c = 1`. -/
theorem norm_Gamma_compactStrip_le_exp
    {a t : ℝ} (halo : -(1 / 2 : ℝ) ≤ a) (hahi : a ≤ 1 / 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (stripPoint a t)‖ ≤
      12 * (1 + |t|) ^ (1 : ℕ) * Real.exp (-(1 : ℝ) * |t|) := by
  have hz_ne : stripPoint a t ≠ 0 := by
    intro hz
    have him := congrArg Complex.im hz
    simp [stripPoint] at him
    subst t
    norm_num at ht
  have hrec := Complex.Gamma_add_one (stripPoint a t) hz_ne
  rw [stripPoint_add_one] at hrec
  have hnormrec := congrArg norm hrec
  rw [norm_mul] at hnormrec
  have hnormz : 1 ≤ ‖stripPoint a t‖ := by
    exact ht.trans (by
      simpa [stripPoint] using Complex.abs_im_le_norm (stripPoint a t))
  have hshift :
      ‖Complex.Gamma (stripPoint (a + 1) t)‖ ≤
        12 * (1 + |t|) * Real.exp (-|t|) := by
    apply norm_Gamma_positive_strip_le_exp
    · linarith
    · linarith
  have hGamma_nonneg := norm_nonneg (Complex.Gamma (stripPoint a t))
  have hbase :
      ‖Complex.Gamma (stripPoint a t)‖ ≤
        ‖Complex.Gamma (stripPoint (a + 1) t)‖ := by
    rw [hnormrec]
    nlinarith
  simpa using hbase.trans hshift

/-- The same estimate in the exact normalization of
`MAPAppendixA4Detector.GammaCompactStripExponentialDecay`. -/
theorem norm_Gamma_compactStrip_le_exp_pi_div_four
    {a t : ℝ} (halo : -(1 / 2 : ℝ) ≤ a) (hahi : a ≤ 1 / 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma ((a : ℂ) + t * Complex.I)‖ ≤
      12 * (1 + |t|) ^ (1 : ℝ) *
        Real.exp (-(Real.pi / 4) * |t|) := by
  have hmain := norm_Gamma_compactStrip_le_exp halo hahi ht
  have hexp : Real.exp (-(1 : ℝ) * |t|) ≤
      Real.exp (-(Real.pi / 4) * |t|) := by
    apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_le_four, abs_nonneg t]
  simpa [stripPoint] using
    hmain.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

end

end GammaCompactStripScratch
