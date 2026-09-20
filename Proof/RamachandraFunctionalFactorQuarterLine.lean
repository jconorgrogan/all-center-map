import RamachandraFunctionalFactorEnvelope
import HuxleyGammaShiftedBounds

/-!
# Sharp functional-factor bound on Ramachandra's long line

The shifted long contour has `Re(s+w)=-1/4` exactly.  Legendre duplication
pairs the two ordinary Gamma factors and gives the source-useful first power
of the height without invoking a variable-strip Stirling theorem.
-/

namespace RamachandraFunctionalFactorQuarterLine

open scoped LSeries.notation
open Complex DirichletCharacter Real
open BHPRamachandraMeanValueFromDyadicAFE

noncomputable section

variable {q : ℕ} [NeZero q]

private theorem inv_even (χ : DirichletCharacter ℂ q) (hχ : χ.Even) : χ⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hχ

private theorem inv_odd (χ : DirichletCharacter ℂ q) (hχ : χ.Odd) : χ⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hχ

/-- The fixed shifted long line `Re z=-1/4`. -/
def ramachandraQuarterLine (t : ℝ) : ℂ :=
  (-(1 / 4 : ℝ) : ℂ) + (t : ℂ) * I

private def aPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (5 / 8) (-t / 2)

private def evenDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (-1 / 8) (t / 2)

private def oddDenominatorPoint (t : ℝ) : ℂ :=
  GammaCompactStripScratch.stripPoint (3 / 8) (t / 2)

private def duplicationRhs (t : ℝ) (b : ℂ) : ℂ :=
  Complex.Gamma (2 * aPoint t) *
      (2 : ℂ) ^ (1 - 2 * aPoint t) * (Real.sqrt Real.pi : ℂ) *
      Complex.sin ((Real.pi : ℂ) * b) / Real.pi

private theorem even_num_geometry (t : ℝ) :
    (1 - ramachandraQuarterLine t) / 2 = aPoint t := by
  apply Complex.ext <;>
    simp [ramachandraQuarterLine, aPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem even_den_geometry (t : ℝ) :
    ramachandraQuarterLine t / 2 = evenDenominatorPoint t := by
  apply Complex.ext <;>
    simp [ramachandraQuarterLine, evenDenominatorPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem odd_num_geometry (t : ℝ) :
    (2 - ramachandraQuarterLine t) / 2 = aPoint t + 1 / 2 := by
  apply Complex.ext <;>
    simp [ramachandraQuarterLine, aPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem odd_den_geometry (t : ℝ) :
    (ramachandraQuarterLine t + 1) / 2 = oddDenominatorPoint t := by
  apply Complex.ext <;>
    simp [ramachandraQuarterLine, oddDenominatorPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem one_sub_evenDenominatorPoint (t : ℝ) :
    1 - evenDenominatorPoint t = aPoint t + 1 / 2 := by
  apply Complex.ext <;>
    simp [evenDenominatorPoint, aPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

private theorem one_sub_oddDenominatorPoint (t : ℝ) :
    1 - oddDenominatorPoint t = aPoint t := by
  apply Complex.ext <;>
    simp [oddDenominatorPoint, aPoint,
      GammaCompactStripScratch.stripPoint] <;> ring

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
    (hz : Complex.Gamma z ≠ 0) (hzb : 1 - b = z) :
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
    Complex.Gamma (aPoint t) *
        (Complex.Gamma (evenDenominatorPoint t))⁻¹ =
      duplicationRhs t (evenDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hb : Complex.Gamma (evenDenominatorPoint t) ≠ 0 :=
    Gamma_shiftedPoint_ne_zero (a := -1 / 8) ht0
  have hz : Complex.Gamma (aPoint t + 1 / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [aPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hinv := reflectedGamma_inverse hb hz (one_sub_evenDenominatorPoint t)
  have hdup := Complex.Gamma_mul_Gamma_add_half (aPoint t)
  rw [hinv]
  unfold duplicationRhs
  calc
    Complex.Gamma (aPoint t) *
        (Complex.Gamma (aPoint t + 1 / 2) *
          Complex.sin ((Real.pi : ℂ) * evenDenominatorPoint t) / Real.pi) =
      (Complex.Gamma (aPoint t) * Complex.Gamma (aPoint t + 1 / 2)) *
        Complex.sin ((Real.pi : ℂ) * evenDenominatorPoint t) / Real.pi := by ring
    _ = Complex.Gamma (2 * aPoint t) *
        (2 : ℂ) ^ (1 - 2 * aPoint t) * (Real.sqrt Real.pi : ℂ) *
        Complex.sin ((Real.pi : ℂ) * evenDenominatorPoint t) / Real.pi := by
          rw [hdup]

private theorem odd_ordinaryGamma_quotient_eq_duplicationRhs
    {t : ℝ} (ht : 2 ≤ |t|) :
    Complex.Gamma (aPoint t + 1 / 2) *
        (Complex.Gamma (oddDenominatorPoint t))⁻¹ =
      duplicationRhs t (oddDenominatorPoint t) := by
  have ht0 : 0 < |t| := lt_of_lt_of_le (by norm_num) ht
  have hb : Complex.Gamma (oddDenominatorPoint t) ≠ 0 :=
    Gamma_shiftedPoint_ne_zero (a := 3 / 8) ht0
  have hz : Complex.Gamma (aPoint t) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [aPoint, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have hinv := reflectedGamma_inverse hb hz (one_sub_oddDenominatorPoint t)
  have hdup := Complex.Gamma_mul_Gamma_add_half (aPoint t)
  rw [hinv]
  unfold duplicationRhs
  calc
    Complex.Gamma (aPoint t + 1 / 2) *
        (Complex.Gamma (aPoint t) *
          Complex.sin ((Real.pi : ℂ) * oddDenominatorPoint t) / Real.pi) =
      (Complex.Gamma (aPoint t) * Complex.Gamma (aPoint t + 1 / 2)) *
        Complex.sin ((Real.pi : ℂ) * oddDenominatorPoint t) / Real.pi := by ring
    _ = Complex.Gamma (2 * aPoint t) *
        (2 : ℂ) ^ (1 - 2 * aPoint t) * (Real.sqrt Real.pi : ℂ) *
        Complex.sin ((Real.pi : ℂ) * oddDenominatorPoint t) / Real.pi := by
          rw [hdup]

private theorem two_mul_aPoint (t : ℝ) :
    2 * aPoint t = GammaCompactStripScratch.stripPoint (5 / 4) (-t) := by
  apply Complex.ext <;>
    simp [aPoint, GammaCompactStripScratch.stripPoint] <;> ring

private theorem norm_duplicationRhs_le
    {t : ℝ} (ht : 2 ≤ |t|) (b : ℂ) (hbim : b.im = t / 2) :
    ‖duplicationRhs t b‖ ≤ 48 * (1 + |t|) := by
  have htone : 1 ≤ |-t| := by simpa [abs_neg] using (show 1 ≤ |t| by linarith)
  have hgamma : ‖Complex.Gamma (2 * aPoint t)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [two_mul_aPoint]
    simpa [abs_neg] using
      MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
        (a := (5 / 4 : ℝ)) (t := -t) (by norm_num) (by norm_num)
  have hpow : ‖(2 : ℂ) ^ (1 - 2 * aPoint t)‖ ≤ 2 := by
    change ‖((2 : ℝ) : ℂ) ^ (1 - 2 * aPoint t)‖ ≤ 2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hre : (1 - 2 * aPoint t).re = (-(1 / 4 : ℝ)) := by
      norm_num [aPoint, GammaCompactStripScratch.stripPoint]
    rw [hre]
    exact (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)).trans
      (by norm_num)
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith [Real.pi_le_four]
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
      Real.exp ((Real.pi / 2) * |t|) := by
    have hs := PLInteriorGrowth.norm_complex_sin_le_exp_abs_im
      ((Real.pi : ℂ) * b)
    have him : (((Real.pi : ℂ) * b).im) = (Real.pi / 2) * t := by
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, hbim]
      ring
    rw [him] at hs
    have habs : |(Real.pi / 2) * t| = (Real.pi / 2) * |t| := by
      rw [abs_mul, abs_of_pos (div_pos Real.pi_pos (by norm_num))]
    rw [habs] at hs
    exact hs
  have hsqrtNorm : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  unfold duplicationRhs
  rw [norm_div, norm_mul, norm_mul, norm_mul, hsqrtNorm]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hnum :
      ‖Complex.Gamma (2 * aPoint t)‖ * ‖(2 : ℂ) ^ (1 - 2 * aPoint t)‖ *
          Real.sqrt Real.pi * ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
        48 * (1 + |t|) := by
    calc
      _ ≤ (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * 2 * 2 *
          Real.exp ((Real.pi / 2) * |t|) := by gcongr
      _ = 48 * (1 + |t|) := by
        rw [show
          (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) * 2 * 2 *
              Real.exp ((Real.pi / 2) * |t|) =
            48 * (1 + |t|) *
              (Real.exp (-(Real.pi / 2) * |t|) *
                Real.exp ((Real.pi / 2) * |t|)) by ring,
          ← Real.exp_add]
        simp
  exact (div_le_self (by positivity) hpi).trans hnum

private theorem ordinaryGammaEven_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma ((1 - ramachandraQuarterLine t) / 2) *
        (Complex.Gamma (ramachandraQuarterLine t / 2))⁻¹‖ ≤
      48 * (1 + |t|) := by
  rw [even_num_geometry, even_den_geometry,
    even_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_duplicationRhs_le ht
  simp [evenDenominatorPoint, GammaCompactStripScratch.stripPoint]

private theorem ordinaryGammaOdd_le {t : ℝ} (ht : 2 ≤ |t|) :
    ‖Complex.Gamma ((2 - ramachandraQuarterLine t) / 2) *
        (Complex.Gamma ((ramachandraQuarterLine t + 1) / 2))⁻¹‖ ≤
      48 * (1 + |t|) := by
  rw [odd_num_geometry, odd_den_geometry,
    odd_ordinaryGamma_quotient_eq_duplicationRhs ht]
  apply norm_duplicationRhs_le ht
  simp [oddDenominatorPoint, GammaCompactStripScratch.stripPoint]

/-- Fixed-quarter-line archimedean quotient with the source-useful first
height power. -/
theorem gammaFactor_reflected_quotient_norm_quarterLine_le
    (χ : DirichletCharacter ℂ q) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖χ⁻¹.gammaFactor (1 - ramachandraQuarterLine t) /
        χ.gammaFactor (ramachandraQuarterLine t)‖ ≤
      Real.rpow Real.pi (-(3 / 4 : ℝ)) * (48 * (1 + |t|)) := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [RamachandraFunctionalFactorEnvelope.gammaREvenReflectedQuotientNormEq]
    have hre : (ramachandraQuarterLine t).re - 1 / 2 = -(3 / 4 : ℝ) := by
      norm_num [ramachandraQuarterLine]
    rw [hre]
    simpa [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (ordinaryGammaEven_le ht)
        (Real.rpow_nonneg Real.pi_pos.le _)
  · rw [(inv_odd χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - ramachandraQuarterLine t + 1 =
      2 - ramachandraQuarterLine t by ring]
    rw [RamachandraFunctionalFactorEnvelope.gammaROddReflectedQuotientNormEq]
    have hre : (ramachandraQuarterLine t).re - 1 / 2 = -(3 / 4 : ℝ) := by
      norm_num [ramachandraQuarterLine]
    rw [hre]
    simpa [norm_mul, mul_assoc] using
      mul_le_mul_of_nonneg_left (ordinaryGammaOdd_le ht)
        (Real.rpow_nonneg Real.pi_pos.le _)

/-- Complete primitive functional-factor bound on the literal long line. -/
theorem norm_ramachandraFunctionalFactor_quarterLine_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖ramachandraFunctionalFactor χ (ramachandraQuarterLine t)‖ ≤
      Real.rpow (q : ℝ) (3 / 4 : ℝ) *
        (Real.rpow Real.pi (-(3 / 4 : ℝ)) * (48 * (1 + |t|))) := by
  unfold ramachandraFunctionalFactor
  rw [show
      (q : ℂ) ^ (1 / 2 - ramachandraQuarterLine t) * χ.rootNumber *
          χ⁻¹.gammaFactor (1 - ramachandraQuarterLine t) /
            χ.gammaFactor (ramachandraQuarterLine t) =
        ((q : ℂ) ^ (1 / 2 - ramachandraQuarterLine t) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (1 - ramachandraQuarterLine t) /
            χ.gammaFactor (ramachandraQuarterLine t)) by ring,
    norm_mul]
  have hroot :
      ‖(q : ℂ) ^ (1 / 2 - ramachandraQuarterLine t) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) (3 / 4 : ℝ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    norm_num [ramachandraQuarterLine]
  rw [hroot]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_reflected_quotient_norm_quarterLine_le χ ht)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end
end RamachandraFunctionalFactorQuarterLine

#print axioms RamachandraFunctionalFactorQuarterLine.norm_ramachandraFunctionalFactor_quarterLine_le
