import HuxleyGammaExactNorm
import GammaInverseGrowthSharp
import GammaOneSharpPower

/-!
# Polynomial Gamma-factor bounds on Huxley's shifted contours

This module retains the sharp exponential cancellation needed in Huxley
1973, (3.14), on the two specific contour lines used in (3.23)--(3.24).
The proof is built from exact reflection, recurrence, and beta comparison;
it does not import Stirling's formula.
-/

namespace MAPHuxleyGammaShiftedBounds

open Complex DirichletCharacter Real

noncomputable section

variable {q : ℕ} [NeZero q]

def rightLine (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * I

def leftLine (t : ℝ) : ℂ := (-3 / 4 : ℂ) + (t : ℂ) * I

private theorem norm_GammaR_even_quotient_eq (s : ℂ) :
    ‖Complex.Gammaℝ s / Complex.Gammaℝ (1 - s)‖ =
      Real.rpow Real.pi (1 / 2 - s.re) *
        ‖Complex.Gamma (s / 2)‖ *
        ‖(Complex.Gamma ((1 - s) / 2))⁻¹‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv,
    mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-s / 2)‖ =
      Real.rpow Real.pi (-s.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-(1 - s) / 2))⁻¹‖ =
      Real.rpow Real.pi ((1 - s.re) / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg (le_of_lt Real.pi_pos)]
    congr 1
    simp
    ring
  rw [hnum, hden]
  rw [show Real.rpow Real.pi (-s.re / 2) * ‖Complex.Gamma (s / 2)‖ *
      (‖(Complex.Gamma ((1 - s) / 2))⁻¹‖ *
        Real.rpow Real.pi ((1 - s.re) / 2)) =
      (Real.rpow Real.pi (-s.re / 2) *
        Real.rpow Real.pi ((1 - s.re) / 2)) *
        ‖Complex.Gamma (s / 2)‖ *
        ‖(Complex.Gamma ((1 - s) / 2))⁻¹‖ by ring]
  have hp : Real.rpow Real.pi (-s.re / 2) *
      Real.rpow Real.pi ((1 - s.re) / 2) =
      Real.rpow Real.pi ((-s.re / 2) + ((1 - s.re) / 2)) := by
    exact (Real.rpow_add Real.pi_pos (-s.re / 2) ((1 - s.re) / 2)).symm
  rw [hp]
  congr 2
  ring

private theorem norm_GammaR_odd_quotient_eq (s : ℂ) :
    ‖Complex.Gammaℝ (s + 1) / Complex.Gammaℝ (2 - s)‖ =
      Real.rpow Real.pi (1 / 2 - s.re) *
        ‖Complex.Gamma ((s + 1) / 2)‖ *
        ‖(Complex.Gamma ((2 - s) / 2))⁻¹‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv,
    mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-(s + 1) / 2)‖ =
      Real.rpow Real.pi (-(s.re + 1) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-(2 - s) / 2))⁻¹‖ =
      Real.rpow Real.pi ((2 - s.re) / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg (le_of_lt Real.pi_pos)]
    congr 1
    simp
    ring
  rw [hnum, hden]
  rw [show Real.rpow Real.pi (-(s.re + 1) / 2) *
      ‖Complex.Gamma ((s + 1) / 2)‖ *
      (‖(Complex.Gamma ((2 - s) / 2))⁻¹‖ *
        Real.rpow Real.pi ((2 - s.re) / 2)) =
      (Real.rpow Real.pi (-(s.re + 1) / 2) *
        Real.rpow Real.pi ((2 - s.re) / 2)) *
        ‖Complex.Gamma ((s + 1) / 2)‖ *
        ‖(Complex.Gamma ((2 - s) / 2))⁻¹‖ by ring]
  have hp : Real.rpow Real.pi (-(s.re + 1) / 2) *
      Real.rpow Real.pi ((2 - s.re) / 2) =
      Real.rpow Real.pi ((-(s.re + 1) / 2) + ((2 - s.re) / 2)) := by
    exact (Real.rpow_add Real.pi_pos (-(s.re + 1) / 2) ((2 - s.re) / 2)).symm
  rw [hp]
  congr 2
  ring

private theorem left_even_num_geometry (t : ℝ) :
    leftLine t / 2 =
      GammaCompactStripScratch.stripPoint (-3 / 8) (t / 2) := by
  apply Complex.ext <;> simp [leftLine, GammaCompactStripScratch.stripPoint]
  <;> ring

private theorem left_even_den_geometry (t : ℝ) :
    (1 - leftLine t) / 2 =
      GammaCompactStripScratch.stripPoint (7 / 8) (-t / 2) := by
  apply Complex.ext <;> simp [leftLine, GammaCompactStripScratch.stripPoint]
  <;> ring

private theorem left_odd_num_geometry (t : ℝ) :
    (leftLine t + 1) / 2 =
      GammaCompactStripScratch.stripPoint (1 / 8) (t / 2) := by
  apply Complex.ext <;> simp [leftLine, GammaCompactStripScratch.stripPoint]
  <;> ring

private theorem left_odd_den_geometry (t : ℝ) :
    (2 - leftLine t) / 2 =
      GammaCompactStripScratch.stripPoint (11 / 8) (-t / 2) := by
  apply Complex.ext <;> simp [leftLine, GammaCompactStripScratch.stripPoint]
  <;> ring

private theorem one_le_abs_half {t : ℝ} (ht : 2 ≤ |t|) :
    1 ≤ |t / 2| := by
  rw [abs_div]
  norm_num
  linarith

private theorem one_add_abs_half_le {t : ℝ} :
    1 + |t / 2| ≤ 1 + |t| := by
  rw [abs_div]
  norm_num

private theorem exp_cancel_half (t : ℝ) :
    Real.exp (-(Real.pi / 2) * |t / 2|) *
        Real.exp ((Real.pi / 2) * |-t / 2|) = 1 := by
  have hneg : -t / 2 = -(t / 2) := by ring
  rw [hneg, abs_neg, ← Real.exp_add, Real.exp_eq_one_iff]
  ring

/-! ## Duplication repair for the left-line polynomial exponent -/

private def quarterPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (1 / 8) (t / 2)

private def minusThreeEighthPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (-3 / 8) (t / 2)

private def evenDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (7 / 8) (-t / 2)

private def oddDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (11 / 8) (-t / 2)

private def duplicationRhs (t : ℝ) (b : ℂ) : ℂ :=
  Complex.Gamma (2 * quarterPoint t) *
      (2 : ℂ) ^ (1 - 2 * quarterPoint t) * (Real.sqrt Real.pi : ℂ) *
      Complex.sin ((Real.pi : ℂ) * b) /
    ((Real.pi : ℂ) * minusThreeEighthPoint t)

private theorem quarter_add_half (t : ℝ) :
    quarterPoint t + 1 / 2 = minusThreeEighthPoint t + 1 := by
  apply Complex.ext <;>
    simp [quarterPoint, minusThreeEighthPoint,
      GammaCompactStripScratch.stripPoint]
  norm_num

private theorem one_sub_evenDenominatorPoint (t : ℝ) :
    1 - evenDenominatorPoint t = quarterPoint t := by
  apply Complex.ext <;>
    simp [evenDenominatorPoint, quarterPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem one_sub_oddDenominatorPoint (t : ℝ) :
    1 - oddDenominatorPoint t = minusThreeEighthPoint t := by
  apply Complex.ext <;>
    simp [oddDenominatorPoint, minusThreeEighthPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem shiftedPoint_ne_zero
    {a t : ℝ} (ht : 0 < |t|) :
    GammaCompactStripScratch.stripPoint a (t / 2) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp [GammaCompactStripScratch.stripPoint] at him
  subst t
  norm_num at ht

private theorem Gamma_shiftedPoint_ne_zero
    {a t : ℝ} (ht : 0 < |t|) :
    Complex.Gamma (GammaCompactStripScratch.stripPoint a (t / 2)) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n h
  have him := congrArg Complex.im h
  simp [GammaCompactStripScratch.stripPoint] at him
  subst t
  norm_num at ht

private theorem reflectedGamma_inverse
    {b z : ℂ} (hb : Complex.Gamma b ≠ 0)
    (hz : Complex.Gamma z ≠ 0)
    (hzb : 1 - b = z) :
    (Complex.Gamma b)⁻¹ =
      Complex.Gamma z * Complex.sin ((Real.pi : ℂ) * b) / Real.pi := by
  have href := Complex.Gamma_mul_Gamma_one_sub b
  rw [hzb] at href
  have hsin : Complex.sin ((Real.pi : ℂ) * b) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at href
    exact (mul_ne_zero hb hz) href
  apply mul_left_cancel₀ hb
  rw [mul_inv_cancel₀ hb, mul_div_assoc, ← mul_assoc, href]
  field_simp [hsin, Real.pi_ne_zero]

private theorem even_ordinaryGamma_quotient_eq_duplicationRhs
    {t : ℝ} (ht : 2 ≤ |t|) :
    Complex.Gamma (minusThreeEighthPoint t) *
        (Complex.Gamma (evenDenominatorPoint t))⁻¹ =
      duplicationRhs t (evenDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have ha : minusThreeEighthPoint t ≠ 0 := shiftedPoint_ne_zero ht0
  have hb : Complex.Gamma (evenDenominatorPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [evenDenominatorPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hz : Complex.Gamma (quarterPoint t) ≠ 0 := by
    exact Gamma_shiftedPoint_ne_zero ht0
  have hinv := reflectedGamma_inverse hb hz (one_sub_evenDenominatorPoint t)
  have hrec := Complex.Gamma_add_one (minusThreeEighthPoint t) ha
  rw [← quarter_add_half] at hrec
  have hdup := Complex.Gamma_mul_Gamma_add_half (quarterPoint t)
  rw [hrec] at hdup
  have hcore : minusThreeEighthPoint t *
      Complex.Gamma (minusThreeEighthPoint t) * Complex.Gamma (quarterPoint t) =
      Complex.Gamma (2 * quarterPoint t) *
        (2 : ℂ) ^ (1 - 2 * quarterPoint t) * (Real.sqrt Real.pi : ℂ) := by
    calc
      minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t) *
          Complex.Gamma (quarterPoint t) =
        Complex.Gamma (quarterPoint t) *
          (minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t)) := by ring
      _ = _ := hdup
  rw [hinv]
  unfold duplicationRhs
  field_simp [ha, Real.pi_ne_zero]
  calc
    Complex.Gamma (minusThreeEighthPoint t) * Complex.Gamma (quarterPoint t) *
        Complex.sin ((Real.pi : ℂ) * evenDenominatorPoint t) *
        minusThreeEighthPoint t =
      (minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t) *
        Complex.Gamma (quarterPoint t)) *
        Complex.sin ((Real.pi : ℂ) * evenDenominatorPoint t) := by ring
    _ = _ := by rw [hcore]; ring

private theorem odd_ordinaryGamma_quotient_eq_duplicationRhs
    {t : ℝ} (ht : 2 ≤ |t|) :
    Complex.Gamma (quarterPoint t) *
        (Complex.Gamma (oddDenominatorPoint t))⁻¹ =
      duplicationRhs t (oddDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have ha : minusThreeEighthPoint t ≠ 0 := shiftedPoint_ne_zero ht0
  have hb : Complex.Gamma (oddDenominatorPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [oddDenominatorPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hz : Complex.Gamma (minusThreeEighthPoint t) ≠ 0 := by
    exact Gamma_shiftedPoint_ne_zero ht0
  have hinv := reflectedGamma_inverse hb hz (one_sub_oddDenominatorPoint t)
  have hrec := Complex.Gamma_add_one (minusThreeEighthPoint t) ha
  rw [← quarter_add_half] at hrec
  have hdup := Complex.Gamma_mul_Gamma_add_half (quarterPoint t)
  rw [hrec] at hdup
  have hcore : minusThreeEighthPoint t *
      Complex.Gamma (minusThreeEighthPoint t) * Complex.Gamma (quarterPoint t) =
      Complex.Gamma (2 * quarterPoint t) *
        (2 : ℂ) ^ (1 - 2 * quarterPoint t) * (Real.sqrt Real.pi : ℂ) := by
    calc
      minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t) *
          Complex.Gamma (quarterPoint t) =
        Complex.Gamma (quarterPoint t) *
          (minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t)) := by ring
      _ = _ := hdup
  rw [hinv]
  unfold duplicationRhs
  field_simp [ha, Real.pi_ne_zero]
  calc
    Complex.Gamma (quarterPoint t) * Complex.Gamma (minusThreeEighthPoint t) *
        Complex.sin ((Real.pi : ℂ) * oddDenominatorPoint t) *
        minusThreeEighthPoint t =
      (minusThreeEighthPoint t * Complex.Gamma (minusThreeEighthPoint t) *
        Complex.Gamma (quarterPoint t)) *
        Complex.sin ((Real.pi : ℂ) * oddDenominatorPoint t) := by ring
    _ = _ := by rw [hcore]; ring

private theorem two_mul_quarterPoint (t : ℝ) :
    2 * quarterPoint t =
      GammaCompactStripScratch.stripPoint (1 / 4) t := by
  apply Complex.ext <;>
    simp [quarterPoint, GammaCompactStripScratch.stripPoint] <;> ring

private theorem norm_duplicationRhs_le
    {t : ℝ} (ht : 2 ≤ |t|) (b : ℂ) (hbim : b.im = -t / 2) :
    ‖duplicationRhs t b‖ ≤ 144 := by
  have htone : 1 ≤ |t| := by linarith
  have hgamma :
      ‖Complex.Gamma (2 * quarterPoint t)‖ ≤
        12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [two_mul_quarterPoint]
    exact MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
      (a := (1 / 4 : ℝ)) (t := t) (by norm_num) (by norm_num) htone
  have hpow :
      ‖(2 : ℂ) ^ (1 - 2 * quarterPoint t)‖ ≤ 2 := by
    change ‖((2 : ℝ) : ℂ) ^ (1 - 2 * quarterPoint t)‖ ≤ 2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : (1 - 2 * quarterPoint t).re = (3 / 4 : ℝ) := by
      norm_num [quarterPoint, GammaCompactStripScratch.stripPoint]
    rw [hre]
    exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.pi_le_four]
  have hsin :
      ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        Real.exp ((Real.pi / 2) * |t|) := by
    have hs := PLInteriorGrowth.norm_complex_sin_le_exp_abs_im
      ((Real.pi : ℂ) * b)
    have him : (((Real.pi : ℂ) * b).im) = -(Real.pi / 2) * t := by
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, hbim]
      ring
    rw [him] at hs
    have habs : |-(Real.pi / 2) * t| = (Real.pi / 2) * |t| := by
      rw [abs_mul, abs_neg,
        abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))]
    rw [habs] at hs
    exact hs
  have hexp : Real.exp (-(Real.pi / 2) * |t|) *
      Real.exp ((Real.pi / 2) * |t|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hnum :
      ‖Complex.Gamma (2 * quarterPoint t)‖ *
          ‖(2 : ℂ) ^ (1 - 2 * quarterPoint t)‖ *
          ‖(Real.sqrt Real.pi : ℂ)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        48 * (1 + |t|) := by
    have hsqrtNorm : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [hsqrtNorm]
    calc
      ‖Complex.Gamma (2 * quarterPoint t)‖ *
          ‖(2 : ℂ) ^ (1 - 2 * quarterPoint t)‖ * Real.sqrt Real.pi *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * 2 * 2 *
          Real.exp ((Real.pi / 2) * |t|) := by gcongr
      _ = 48 * (1 + |t|) := by
        rw [show
          (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * 2 * 2 *
              Real.exp ((Real.pi / 2) * |t|) =
            48 * (1 + |t|) *
              (Real.exp (-(Real.pi / 2) * |t|) *
                Real.exp ((Real.pi / 2) * |t|)) by ring, hexp]
        ring
  have hima : (minusThreeEighthPoint t).im = t / 2 := by
    simp [minusThreeEighthPoint, GammaCompactStripScratch.stripPoint]
  have hnorma : |t| / 2 ≤ ‖minusThreeEighthPoint t‖ := by
    have h := Complex.abs_im_le_norm (minusThreeEighthPoint t)
    rw [hima, abs_div] at h
    norm_num at h
    exact h
  have hden : |t| / 2 ≤
      ‖(Real.pi : ℂ) * minusThreeEighthPoint t‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
    have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
    calc
      |t| / 2 ≤ ‖minusThreeEighthPoint t‖ := hnorma
      _ ≤ Real.pi * ‖minusThreeEighthPoint t‖ :=
        (le_mul_of_one_le_left (norm_nonneg _) hpi)
  have hdenpos : 0 < ‖(Real.pi : ℂ) * minusThreeEighthPoint t‖ :=
    lt_of_lt_of_le (by positivity : 0 < |t| / 2) hden
  unfold duplicationRhs
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  apply (div_le_iff₀ hdenpos).2
  calc
    ‖Complex.Gamma (2 * quarterPoint t)‖ *
          ‖(2 : ℂ) ^ (1 - 2 * quarterPoint t)‖ *
          ‖(Real.sqrt Real.pi : ℂ)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        48 * (1 + |t|) := hnum
    _ ≤ 144 * ‖(Real.pi : ℂ) * minusThreeEighthPoint t‖ := by
      nlinarith

/-- Duplication improves the even ordinary-Gamma quotient from a quadratic
bound to an absolute constant on the left line. -/
theorem even_ordinaryGamma_quotient_norm_leftLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma (minusThreeEighthPoint t) *
        (Complex.Gamma (evenDenominatorPoint t))⁻¹‖ ≤ 144 := by
  rw [even_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_duplicationRhs_le ht
  simp [evenDenominatorPoint, GammaCompactStripScratch.stripPoint]

/-- The identical duplication bound in odd parity. -/
theorem odd_ordinaryGamma_quotient_norm_leftLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma (quarterPoint t) *
        (Complex.Gamma (oddDenominatorPoint t))⁻¹‖ ≤ 144 := by
  rw [odd_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_duplicationRhs_le ht
  simp [oddDenominatorPoint, GammaCompactStripScratch.stripPoint]

/-- Source-useful even GammaR bound: duplication removes the spurious
quadratic loss from generic compact-strip comparison. -/
theorem even_gammaR_quotient_norm_leftLine_le_constant
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (leftLine t) /
        Complex.Gammaℝ (1 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 := by
  rw [norm_GammaR_even_quotient_eq]
  have hre : 1 / 2 - (leftLine t).re = (5 / 4 : ℝ) := by
    norm_num [leftLine]
  rw [hre, left_even_num_geometry, left_even_den_geometry]
  have hscaled := mul_le_mul_of_nonneg_left
    (even_ordinaryGamma_quotient_norm_leftLine_le ht)
    (Real.rpow_nonneg Real.pi_pos.le (5 / 4))
  simpa [minusThreeEighthPoint, evenDenominatorPoint, norm_mul, mul_assoc] using hscaled

/-- Source-useful odd GammaR bound with the same constant. -/
theorem odd_gammaR_quotient_norm_leftLine_le_constant
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (leftLine t + 1) /
        Complex.Gammaℝ (2 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 := by
  rw [norm_GammaR_odd_quotient_eq]
  have hre : 1 / 2 - (leftLine t).re = (5 / 4 : ℝ) := by
    norm_num [leftLine]
  rw [hre, left_odd_num_geometry, left_odd_den_geometry]
  have hscaled := mul_le_mul_of_nonneg_left
    (odd_ordinaryGamma_quotient_norm_leftLine_le ht)
    (Real.rpow_nonneg Real.pi_pos.le (5 / 4))
  simpa [quarterPoint, oddDenominatorPoint, norm_mul, mul_assoc] using hscaled

/-! ## Right-line duplication bound -/

private def rightQuarterPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint 1 (t / 2)

private def rightEvenDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (-1 / 2) (-t / 2)

private def rightOddDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint 0 (-t / 2)

private def rightDuplicationRhs (t : ℝ) (b : ℂ) : ℂ :=
  Complex.Gamma (2 * rightQuarterPoint t) *
      (2 : ℂ) ^ (1 - 2 * rightQuarterPoint t) * (Real.sqrt Real.pi : ℂ) *
      Complex.sin ((Real.pi : ℂ) * b) /
    (Real.pi : ℂ)

private theorem one_sub_rightEvenDenominatorPoint (t : ℝ) :
    1 - rightEvenDenominatorPoint t = rightQuarterPoint t + 1 / 2 := by
  apply Complex.ext <;>
    simp [rightEvenDenominatorPoint, rightQuarterPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem one_sub_rightOddDenominatorPoint (t : ℝ) :
    1 - rightOddDenominatorPoint t = rightQuarterPoint t := by
  apply Complex.ext <;>
    simp [rightOddDenominatorPoint, rightQuarterPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem right_even_ordinaryGamma_quotient_eq_duplicationRhs
    {t : ℝ} (ht : 2 ≤ |t|) :
    Complex.Gamma (rightQuarterPoint t) *
        (Complex.Gamma (rightEvenDenominatorPoint t))⁻¹ =
      rightDuplicationRhs t (rightEvenDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hb : Complex.Gamma (rightEvenDenominatorPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [rightEvenDenominatorPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hz : Complex.Gamma (rightQuarterPoint t + 1 / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [rightQuarterPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hinv := reflectedGamma_inverse hb hz
    (one_sub_rightEvenDenominatorPoint t)
  have hdup := Complex.Gamma_mul_Gamma_add_half (rightQuarterPoint t)
  rw [hinv]
  unfold rightDuplicationRhs
  field_simp [Real.pi_ne_zero]
  have hhalf : (rightQuarterPoint t * 2 + 1) / 2 =
      rightQuarterPoint t + 1 / 2 := by ring
  have htwo : rightQuarterPoint t * 2 = 2 * rightQuarterPoint t := by ring
  rw [hhalf, htwo]
  rw [hdup]
  ring

private theorem right_odd_ordinaryGamma_quotient_eq_duplicationRhs
    {t : ℝ} (ht : 2 ≤ |t|) :
    Complex.Gamma (rightQuarterPoint t + 1 / 2) *
        (Complex.Gamma (rightOddDenominatorPoint t))⁻¹ =
      rightDuplicationRhs t (rightOddDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hb : Complex.Gamma (rightOddDenominatorPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [rightOddDenominatorPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hz : Complex.Gamma (rightQuarterPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [rightQuarterPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hinv := reflectedGamma_inverse hb hz
    (one_sub_rightOddDenominatorPoint t)
  have hdup := Complex.Gamma_mul_Gamma_add_half (rightQuarterPoint t)
  rw [hinv]
  unfold rightDuplicationRhs
  field_simp [Real.pi_ne_zero]
  have hhalf : (rightQuarterPoint t * 2 + 1) / 2 =
      rightQuarterPoint t + 1 / 2 := by ring
  have htwo : rightQuarterPoint t * 2 = 2 * rightQuarterPoint t := by ring
  rw [hhalf, htwo]
  rw [show Complex.Gamma (rightQuarterPoint t + 1 / 2) *
      Complex.Gamma (rightQuarterPoint t) =
      Complex.Gamma (rightQuarterPoint t) *
        Complex.Gamma (rightQuarterPoint t + 1 / 2) by ring, hdup]
  ring

private theorem two_mul_rightQuarterPoint (t : ℝ) :
    2 * rightQuarterPoint t = MAPGammaOneSharpPower.twoPoint t := by
  apply Complex.ext <;>
    simp [rightQuarterPoint, MAPGammaOneSharpPower.twoPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem norm_rightDuplicationRhs_le
    {t : ℝ} (ht : 2 ≤ |t|) (b : ℂ) (hbim : b.im = -t / 2) :
    ‖rightDuplicationRhs t b‖ ≤
      8 * (1 + |t|) * Real.sqrt (1 + |t|) := by
  have htone : 1 ≤ |t| := by linarith
  have hgamma :
      ‖Complex.Gamma (2 * rightQuarterPoint t)‖ ≤
        4 * (1 + |t|) * Real.sqrt (1 + |t|) *
          Real.exp (-(Real.pi / 2) * |t|) := by
    rw [two_mul_rightQuarterPoint]
    exact MAPGammaOneSharpPower.norm_Gamma_twoPoint_le_three_halves htone
  have hpow :
      ‖(2 : ℂ) ^ (1 - 2 * rightQuarterPoint t)‖ ≤ 1 := by
    change ‖((2 : ℝ) : ℂ) ^ (1 - 2 * rightQuarterPoint t)‖ ≤ 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : (1 - 2 * rightQuarterPoint t).re = (-1 : ℝ) := by
      norm_num [rightQuarterPoint, GammaCompactStripScratch.stripPoint]
    rw [hre]
    calc
      Real.rpow (2 : ℝ) (-1) ≤ Real.rpow (2 : ℝ) 0 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 1 := by simp
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hsin :
      ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        Real.exp ((Real.pi / 2) * |t|) := by
    have hs := PLInteriorGrowth.norm_complex_sin_le_exp_abs_im
      ((Real.pi : ℂ) * b)
    have him : (((Real.pi : ℂ) * b).im) = -(Real.pi / 2) * t := by
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, hbim]
      ring
    rw [him] at hs
    have habs : |-(Real.pi / 2) * t| = (Real.pi / 2) * |t| := by
      rw [abs_mul, abs_neg,
        abs_of_pos (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2))]
    rw [habs] at hs
    exact hs
  have hexp : Real.exp (-(Real.pi / 2) * |t|) *
      Real.exp ((Real.pi / 2) * |t|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  unfold rightDuplicationRhs
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos Real.pi_pos]
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  calc
    ‖Complex.Gamma (2 * rightQuarterPoint t)‖ *
          ‖(2 : ℂ) ^ (1 - 2 * rightQuarterPoint t)‖ *
          Real.sqrt Real.pi *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ / Real.pi ≤
      ‖Complex.Gamma (2 * rightQuarterPoint t)‖ *
          ‖(2 : ℂ) ^ (1 - 2 * rightQuarterPoint t)‖ *
          Real.sqrt Real.pi *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ :=
        div_le_self (by positivity) hpi
    _ ≤ (4 * (1 + |t|) * Real.sqrt (1 + |t|) *
          Real.exp (-(Real.pi / 2) * |t|)) * 1 * 2 *
          Real.exp ((Real.pi / 2) * |t|) := by
      gcongr
    _ = 8 * (1 + |t|) * Real.sqrt (1 + |t|) := by
      rw [show
        (4 * (1 + |t|) * Real.sqrt (1 + |t|) *
            Real.exp (-(Real.pi / 2) * |t|)) * 1 * 2 *
            Real.exp ((Real.pi / 2) * |t|) =
          8 * (1 + |t|) * Real.sqrt (1 + |t|) *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp ((Real.pi / 2) * |t|)) by ring, hexp]
      ring

theorem even_ordinaryGamma_quotient_norm_rightLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma (rightQuarterPoint t) *
        (Complex.Gamma (rightEvenDenominatorPoint t))⁻¹‖ ≤
      8 * (1 + |t|) * Real.sqrt (1 + |t|) := by
  rw [right_even_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_rightDuplicationRhs_le ht
  simp [rightEvenDenominatorPoint, GammaCompactStripScratch.stripPoint]

theorem odd_ordinaryGamma_quotient_norm_rightLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma (rightQuarterPoint t + 1 / 2) *
        (Complex.Gamma (rightOddDenominatorPoint t))⁻¹‖ ≤
      8 * (1 + |t|) * Real.sqrt (1 + |t|) := by
  rw [right_odd_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_rightDuplicationRhs_le ht
  simp [rightOddDenominatorPoint, GammaCompactStripScratch.stripPoint]

private theorem right_even_num_geometry (t : ℝ) :
    rightLine t / 2 = rightQuarterPoint t := by
  apply Complex.ext <;>
    simp [rightLine, rightQuarterPoint, GammaCompactStripScratch.stripPoint] <;> ring

private theorem right_even_den_geometry (t : ℝ) :
    (1 - rightLine t) / 2 = rightEvenDenominatorPoint t := by
  apply Complex.ext <;>
    simp [rightLine, rightEvenDenominatorPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem right_odd_num_geometry (t : ℝ) :
    (rightLine t + 1) / 2 = rightQuarterPoint t + 1 / 2 := by
  apply Complex.ext <;>
    simp [rightLine, rightQuarterPoint, GammaCompactStripScratch.stripPoint] <;> ring

private theorem right_odd_den_geometry (t : ℝ) :
    (2 - rightLine t) / 2 = rightOddDenominatorPoint t := by
  apply Complex.ext <;>
    simp [rightLine, rightOddDenominatorPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

theorem even_gammaR_quotient_norm_rightLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (rightLine t) /
        Complex.Gammaℝ (1 - rightLine t)‖ ≤
      Real.rpow Real.pi (-3 / 2) *
        (8 * (1 + |t|) * Real.sqrt (1 + |t|)) := by
  rw [norm_GammaR_even_quotient_eq]
  have hre : 1 / 2 - (rightLine t).re = (-3 / 2 : ℝ) := by
    norm_num [rightLine]
  rw [hre, right_even_num_geometry, right_even_den_geometry]
  have hscaled := mul_le_mul_of_nonneg_left
    (even_ordinaryGamma_quotient_norm_rightLine_le ht)
    (Real.rpow_nonneg Real.pi_pos.le (-3 / 2))
  simpa [rightQuarterPoint, rightEvenDenominatorPoint, norm_mul, mul_assoc] using hscaled

theorem odd_gammaR_quotient_norm_rightLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (rightLine t + 1) /
        Complex.Gammaℝ (2 - rightLine t)‖ ≤
      Real.rpow Real.pi (-3 / 2) *
        (8 * (1 + |t|) * Real.sqrt (1 + |t|)) := by
  rw [norm_GammaR_odd_quotient_eq]
  have hre : 1 / 2 - (rightLine t).re = (-3 / 2 : ℝ) := by
    norm_num [rightLine]
  rw [hre, right_odd_num_geometry, right_odd_den_geometry]
  have hscaled := mul_le_mul_of_nonneg_left
    (odd_ordinaryGamma_quotient_norm_rightLine_le ht)
    (Real.rpow_nonneg Real.pi_pos.le (-3 / 2))
  simpa [rightQuarterPoint, rightOddDenominatorPoint, norm_mul, mul_assoc] using hscaled

/-- Even-parity GammaR quotient on Huxley's left line. -/
theorem even_gammaR_quotient_norm_leftLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (leftLine t) /
        Complex.Gammaℝ (1 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2 := by
  rw [norm_GammaR_even_quotient_eq]
  have hre : 1 / 2 - (leftLine t).re = (5 / 4 : ℝ) := by
    norm_num [leftLine]
  rw [hre, left_even_num_geometry, left_even_den_geometry]
  have hhalf := one_le_abs_half ht
  have hnum := MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
    (a := (-3 / 8 : ℝ)) (t := t / 2) (by norm_num) (by norm_num) hhalf
  have hden := MAPGammaInverseGrowthSharp.norm_inv_Gamma_positive_strip_le_exp_pi_half
    (a := (7 / 8 : ℝ)) (t := -t / 2) (by norm_num) (by norm_num)
      (by
        have hneg : -t / 2 = -(t / 2) := by ring
        rw [hneg, abs_neg]
        exact hhalf)
  have hprod := mul_le_mul hnum hden (norm_nonneg _) (by positivity)
  have hhalf_le := one_add_abs_half_le (t := t)
  have hrpow : 0 ≤ Real.rpow Real.pi (5 / 4) :=
    Real.rpow_nonneg Real.pi_pos.le _
  have hnegabs : |-t / 2| = |t / 2| := by
    have hneg : -t / 2 = -(t / 2) := by ring
    rw [hneg, abs_neg]
  have hexp : Real.exp (-(Real.pi / 2) * |t / 2|) *
      Real.exp ((Real.pi / 2) * |t / 2|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  calc
    Real.rpow Real.pi (5 / 4) *
        ‖Complex.Gamma (GammaCompactStripScratch.stripPoint (-3 / 8) (t / 2))‖ *
        ‖(Complex.Gamma
          (GammaCompactStripScratch.stripPoint (7 / 8) (-t / 2)))⁻¹‖ ≤
      Real.rpow Real.pi (5 / 4) *
        ((12 * (1 + |t / 2|) * Real.exp (-(Real.pi / 2) * |t / 2|)) *
         (12 * (1 + |-t / 2|) * Real.exp ((Real.pi / 2) * |-t / 2|))) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hrpow
    _ = Real.rpow Real.pi (5 / 4) * 144 * (1 + |t / 2|) ^ 2 := by
      rw [hnegabs]
      rw [show
        (12 * (1 + |t / 2|) * Real.exp (-(Real.pi / 2) * |t / 2|)) *
          (12 * (1 + |t / 2|) * Real.exp ((Real.pi / 2) * |t / 2|)) =
        144 * (1 + |t / 2|) ^ 2 *
          (Real.exp (-(Real.pi / 2) * |t / 2|) *
            Real.exp ((Real.pi / 2) * |t / 2|)) by ring, hexp]
      ring
    _ ≤ Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hhalf_le 2) (mul_nonneg hrpow (by norm_num))

/-- Odd-parity GammaR quotient on Huxley's left line. -/
theorem odd_gammaR_quotient_norm_leftLine_le
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gammaℝ (leftLine t + 1) /
        Complex.Gammaℝ (2 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2 := by
  rw [norm_GammaR_odd_quotient_eq]
  have hre : 1 / 2 - (leftLine t).re = (5 / 4 : ℝ) := by
    norm_num [leftLine]
  rw [hre, left_odd_num_geometry, left_odd_den_geometry]
  have hhalf := one_le_abs_half ht
  have hnum := MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
    (a := (1 / 8 : ℝ)) (t := t / 2) (by norm_num) (by norm_num) hhalf
  have hden := MAPGammaInverseGrowthSharp.norm_inv_Gamma_positive_strip_le_exp_pi_half
    (a := (11 / 8 : ℝ)) (t := -t / 2) (by norm_num) (by norm_num)
      (by
        have hneg : -t / 2 = -(t / 2) := by ring
        rw [hneg, abs_neg]
        exact hhalf)
  have hprod := mul_le_mul hnum hden (norm_nonneg _) (by positivity)
  have hhalf_le := one_add_abs_half_le (t := t)
  have hrpow : 0 ≤ Real.rpow Real.pi (5 / 4) :=
    Real.rpow_nonneg Real.pi_pos.le _
  have hnegabs : |-t / 2| = |t / 2| := by
    have hneg : -t / 2 = -(t / 2) := by ring
    rw [hneg, abs_neg]
  have hexp : Real.exp (-(Real.pi / 2) * |t / 2|) *
      Real.exp ((Real.pi / 2) * |t / 2|) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  calc
    Real.rpow Real.pi (5 / 4) *
        ‖Complex.Gamma (GammaCompactStripScratch.stripPoint (1 / 8) (t / 2))‖ *
        ‖(Complex.Gamma
          (GammaCompactStripScratch.stripPoint (11 / 8) (-t / 2)))⁻¹‖ ≤
      Real.rpow Real.pi (5 / 4) *
        ((12 * (1 + |t / 2|) * Real.exp (-(Real.pi / 2) * |t / 2|)) *
         (12 * (1 + |-t / 2|) * Real.exp ((Real.pi / 2) * |-t / 2|))) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hprod hrpow
    _ = Real.rpow Real.pi (5 / 4) * 144 * (1 + |t / 2|) ^ 2 := by
      rw [hnegabs]
      rw [show
        (12 * (1 + |t / 2|) * Real.exp (-(Real.pi / 2) * |t / 2|)) *
          (12 * (1 + |t / 2|) * Real.exp ((Real.pi / 2) * |t / 2|)) =
        144 * (1 + |t / 2|) ^ 2 *
          (Real.exp (-(Real.pi / 2) * |t / 2|) *
            Real.exp ((Real.pi / 2) * |t / 2|)) by ring, hexp]
      ring
    _ ≤ Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hhalf_le 2) (mul_nonneg hrpow (by norm_num))

private theorem inv_even {χ : DirichletCharacter ℂ q} (hχ : χ.Even) : χ⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hχ

private theorem inv_odd {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) : χ⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hχ

/-- Parity-independent right-line Gamma quotient with the source polynomial
degree `3/2`. -/
theorem gammaFactor_quotient_norm_rightLine_le
    (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖χ⁻¹.gammaFactor (rightLine t) /
        χ.gammaFactor (1 - rightLine t)‖ ≤
      Real.rpow Real.pi (-3 / 2) *
        (8 * (1 + |t|) * Real.sqrt (1 + |t|)) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even hχ).gammaFactor_def, hχ.gammaFactor_def]
    exact even_gammaR_quotient_norm_rightLine_le ht
  · rw [(inv_odd hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - rightLine t + 1 = 2 - rightLine t by ring]
    exact odd_gammaR_quotient_norm_rightLine_le ht

/-- Complete conductor/root-number/gamma multiplier on Huxley's right line.
Together with the cubic `J` estimate this gives a `|t|^(-3/2)` tail. -/
theorem huxleyFactor_norm_rightLine_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖(q : ℂ) ^ (rightLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (rightLine t) /
        χ.gammaFactor (1 - rightLine t)‖ ≤
      Real.rpow (q : ℝ) (3 / 2) *
        (Real.rpow Real.pi (-3 / 2) *
          (8 * (1 + |t|) * Real.sqrt (1 + |t|))) := by
  rw [show (q : ℂ) ^ (rightLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (rightLine t) /
          χ.gammaFactor (1 - rightLine t) =
        ((q : ℂ) ^ (rightLine t - 1 / 2) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (rightLine t) /
            χ.gammaFactor (1 - rightLine t)) by ring]
  rw [norm_mul]
  have hconductor :
      ‖(q : ℂ) ^ (rightLine t - 1 / 2) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) (3 / 2) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    norm_num [rightLine]
  rw [hconductor]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_quotient_norm_rightLine_le χ ht)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Parity-independent left-line gamma-factor quotient. -/
theorem gammaFactor_quotient_norm_leftLine_le
    (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖χ⁻¹.gammaFactor (leftLine t) /
        χ.gammaFactor (1 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even hχ).gammaFactor_def, hχ.gammaFactor_def]
    exact even_gammaR_quotient_norm_leftLine_le ht
  · rw [(inv_odd hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - leftLine t + 1 = 2 - leftLine t by ring]
    exact odd_gammaR_quotient_norm_leftLine_le ht

/-- Parity-independent constant left-line quotient obtained from
duplication. -/
theorem gammaFactor_quotient_norm_leftLine_le_constant
    (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖χ⁻¹.gammaFactor (leftLine t) /
        χ.gammaFactor (1 - leftLine t)‖ ≤
      Real.rpow Real.pi (5 / 4) * 144 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even hχ).gammaFactor_def, hχ.gammaFactor_def]
    exact even_gammaR_quotient_norm_leftLine_le_constant ht
  · rw [(inv_odd hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - leftLine t + 1 = 2 - leftLine t by ring]
    exact odd_gammaR_quotient_norm_leftLine_le_constant ht

/-- Complete conductor/root-number/gamma multiplier on Huxley's left line.
This is the fixed-line upper-bound part of (3.14) used in (3.24). -/
theorem huxleyFactor_norm_leftLine_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖(q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (leftLine t) /
        χ.gammaFactor (1 - leftLine t)‖ ≤
      Real.rpow (q : ℝ) (-5 / 4) *
        (Real.rpow Real.pi (5 / 4) * 144 * (1 + |t|) ^ 2) := by
  rw [show (q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (leftLine t) /
          χ.gammaFactor (1 - leftLine t) =
        ((q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (leftLine t) /
            χ.gammaFactor (1 - leftLine t)) by ring]
  rw [norm_mul]
  have hconductor :
      ‖(q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) (-5 / 4) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    norm_num [leftLine]
  rw [hconductor]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_quotient_norm_leftLine_le χ ht)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Integrable-strength complete multiplier bound on the left contour.
This is weaker than Huxley's sharp `|t|^(-5/4)` form but, unlike the generic
quadratic estimate above, is strong enough when multiplied by the certified
cubic decay of `J(1-s-u)`. -/
theorem huxleyFactor_norm_leftLine_le_constant
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖(q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (leftLine t) /
        χ.gammaFactor (1 - leftLine t)‖ ≤
      Real.rpow (q : ℝ) (-5 / 4) *
        (Real.rpow Real.pi (5 / 4) * 144) := by
  rw [show (q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (leftLine t) /
          χ.gammaFactor (1 - leftLine t) =
        ((q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (leftLine t) /
            χ.gammaFactor (1 - leftLine t)) by ring]
  rw [norm_mul]
  have hconductor :
      ‖(q : ℂ) ^ (leftLine t - 1 / 2) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) (-5 / 4) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    norm_num [leftLine]
  rw [hconductor]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_quotient_norm_leftLine_le_constant χ ht)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end

end MAPHuxleyGammaShiftedBounds

#print axioms MAPHuxleyGammaShiftedBounds.even_gammaR_quotient_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.odd_gammaR_quotient_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.even_ordinaryGamma_quotient_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.odd_ordinaryGamma_quotient_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.even_gammaR_quotient_norm_leftLine_le_constant
#print axioms MAPHuxleyGammaShiftedBounds.odd_gammaR_quotient_norm_leftLine_le_constant
#print axioms MAPHuxleyGammaShiftedBounds.gammaFactor_quotient_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.gammaFactor_quotient_norm_leftLine_le_constant
#print axioms MAPHuxleyGammaShiftedBounds.huxleyFactor_norm_leftLine_le
#print axioms MAPHuxleyGammaShiftedBounds.huxleyFactor_norm_leftLine_le_constant
#print axioms MAPHuxleyGammaShiftedBounds.even_ordinaryGamma_quotient_norm_rightLine_le
#print axioms MAPHuxleyGammaShiftedBounds.odd_ordinaryGamma_quotient_norm_rightLine_le
#print axioms MAPHuxleyGammaShiftedBounds.even_gammaR_quotient_norm_rightLine_le
#print axioms MAPHuxleyGammaShiftedBounds.odd_gammaR_quotient_norm_rightLine_le
#print axioms MAPHuxleyGammaShiftedBounds.gammaFactor_quotient_norm_rightLine_le
#print axioms MAPHuxleyGammaShiftedBounds.huxleyFactor_norm_rightLine_le
