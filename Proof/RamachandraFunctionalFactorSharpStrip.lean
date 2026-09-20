import GammaSharpPositiveStripInterpolation

/-!
# Real-part sharp Ramachandra functional factor

The reflection and duplication formula reduce both parities to one copy of
`Gamma (1-z)`.  The preceding Gaussian three-lines bound then retains the
exact height exponent `1/2-Re z`; this is the exponent needed on both of
Ramachandra's shifted contours.
-/

namespace RamachandraFunctionalFactorSharpStrip

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

private def aPoint (z : ℂ) : ℂ := (1 - z) / 2

private def duplicationRhs (z b : ℂ) : ℂ :=
  Complex.Gamma (1 - z) * (2 : ℂ) ^ z * (Real.sqrt Real.pi : ℂ) *
    Complex.sin ((Real.pi : ℂ) * b) / Real.pi

private theorem Gamma_nonzero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma z ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro n h
  have him := congrArg Complex.im h
  simp at him
  exact hz him

private theorem reflectedGamma_inverse
    {b w : ℂ} (hb : Complex.Gamma b ≠ 0)
    (hw : Complex.Gamma w ≠ 0) (hwb : 1 - b = w) :
    (Complex.Gamma b)⁻¹ =
      Complex.Gamma w * Complex.sin ((Real.pi : ℂ) * b) / Real.pi := by
  have href := Complex.Gamma_mul_Gamma_one_sub b
  rw [hwb] at href
  have hsin : Complex.sin ((Real.pi : ℂ) * b) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at href
    exact (mul_ne_zero hb hw) href
  apply mul_left_cancel₀ hb
  rw [mul_inv_cancel₀ hb, mul_div_assoc, ← mul_assoc, href]
  field_simp [hsin, Real.pi_ne_zero]

private theorem even_ordinaryGamma_quotient_eq_duplicationRhs
    {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma ((1 - z) / 2) * (Complex.Gamma (z / 2))⁻¹ =
      duplicationRhs z (z / 2) := by
  have hbim : (z / 2).im ≠ 0 := by
    have him : (z / 2).im = z.im / 2 := by norm_num
    rw [him]
    exact div_ne_zero hz (by norm_num)
  have hwim : (aPoint z + 1 / 2).im ≠ 0 := by
    have him : (aPoint z + 1 / 2).im = -z.im / 2 := by simp [aPoint]
    rw [him]
    exact div_ne_zero (neg_ne_zero.mpr hz) (by norm_num)
  have hb := Gamma_nonzero_of_im_ne_zero hbim
  have hw := Gamma_nonzero_of_im_ne_zero hwim
  have hgeom : 1 - z / 2 = aPoint z + 1 / 2 := by
    unfold aPoint
    ring
  have hinv := reflectedGamma_inverse hb hw hgeom
  have hdup := Complex.Gamma_mul_Gamma_add_half (aPoint z)
  rw [show (1 - z) / 2 = aPoint z by rfl, hinv]
  have htwo : 2 * aPoint z = 1 - z := by unfold aPoint; ring
  have hpow : 1 - 2 * aPoint z = z := by unfold aPoint; ring
  calc
    Complex.Gamma (aPoint z) *
        (Complex.Gamma (aPoint z + 1 / 2) *
          Complex.sin ((Real.pi : ℂ) * (z / 2)) / Real.pi) =
      (Complex.Gamma (aPoint z) * Complex.Gamma (aPoint z + 1 / 2)) *
        Complex.sin ((Real.pi : ℂ) * (z / 2)) / Real.pi := by ring
    _ = Complex.Gamma (2 * aPoint z) *
        (2 : ℂ) ^ (1 - 2 * aPoint z) * (Real.sqrt Real.pi : ℂ) *
        Complex.sin ((Real.pi : ℂ) * (z / 2)) / Real.pi := by rw [hdup]
    _ = duplicationRhs z (z / 2) := by
      unfold duplicationRhs
      rw [hpow, htwo]

private theorem odd_ordinaryGamma_quotient_eq_duplicationRhs
    {z : ℂ} (hz : z.im ≠ 0) :
    Complex.Gamma ((2 - z) / 2) * (Complex.Gamma ((z + 1) / 2))⁻¹ =
      duplicationRhs z ((z + 1) / 2) := by
  have hbim : ((z + 1) / 2).im ≠ 0 := by
    have him : ((z + 1) / 2).im = z.im / 2 := by norm_num
    rw [him]
    exact div_ne_zero hz (by norm_num)
  have hawim : (aPoint z).im ≠ 0 := by
    have him : (aPoint z).im = -z.im / 2 := by simp [aPoint]
    rw [him]
    exact div_ne_zero (neg_ne_zero.mpr hz) (by norm_num)
  have hb := Gamma_nonzero_of_im_ne_zero hbim
  have haw := Gamma_nonzero_of_im_ne_zero hawim
  have hgeom : 1 - (z + 1) / 2 = aPoint z := by
    unfold aPoint
    ring
  have hinv := reflectedGamma_inverse hb haw hgeom
  have hdup := Complex.Gamma_mul_Gamma_add_half (aPoint z)
  have hnum : (2 - z) / 2 = aPoint z + 1 / 2 := by unfold aPoint; ring
  rw [hnum, hinv]
  have htwo : 2 * aPoint z = 1 - z := by unfold aPoint; ring
  have hpow : 1 - 2 * aPoint z = z := by unfold aPoint; ring
  calc
    Complex.Gamma (aPoint z + 1 / 2) *
        (Complex.Gamma (aPoint z) *
          Complex.sin ((Real.pi : ℂ) * ((z + 1) / 2)) / Real.pi) =
      (Complex.Gamma (aPoint z) * Complex.Gamma (aPoint z + 1 / 2)) *
        Complex.sin ((Real.pi : ℂ) * ((z + 1) / 2)) / Real.pi := by ring
    _ = Complex.Gamma (2 * aPoint z) *
        (2 : ℂ) ^ (1 - 2 * aPoint z) * (Real.sqrt Real.pi : ℂ) *
        Complex.sin ((Real.pi : ℂ) * ((z + 1) / 2)) / Real.pi := by rw [hdup]
    _ = duplicationRhs z ((z + 1) / 2) := by
      unfold duplicationRhs
      rw [hpow, htwo]

private theorem one_sub_geometry (z : ℂ) :
    1 - z = GammaCompactStripScratch.stripPoint (1 - z.re) (-z.im) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring

private theorem norm_duplicationRhs_le
    {z b : ℂ} (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hbim : |b.im| = |z.im| / 2) :
    ‖duplicationRhs z b‖ ≤
      4 * (Real.rpow 2000 (1 / 2 + z.re) *
        Real.rpow (2000 * (1 + |z.im|)) (1 / 2 - z.re)) := by
  have hgamma : ‖Complex.Gamma (1 - z)‖ ≤
      Real.rpow 2000 (1 / 2 + z.re) *
        Real.rpow (2000 * (1 + |z.im|)) (1 / 2 - z.re) *
        Real.exp (-(Real.pi / 2) * |z.im|) := by
    rw [one_sub_geometry]
    have h := GammaSharpPositiveStripInterpolation.norm_Gamma_positive_strip_le_interp
      (a := 1 - z.re) (t := -z.im) (by linarith) (by linarith)
    have he₁ : (3 / 2 : ℝ) - (1 - z.re) = 1 / 2 + z.re := by ring
    have he₂ : (1 - z.re) - 1 / 2 = 1 / 2 - z.re := by ring
    rw [he₁, he₂] at h
    simpa only [abs_neg] using h
  have hpow : ‖(2 : ℂ) ^ z‖ ≤ 2 := by
    change ‖((2 : ℝ) : ℂ) ^ z‖ ≤ 2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      Real.rpow 2 z.re ≤ Real.rpow 2 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := by norm_num
  have hsqrt : Real.sqrt Real.pi ≤ 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by nlinarith [Real.pi_le_four]⟩
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤
      Real.exp ((Real.pi / 2) * |z.im|) := by
    have hs := PLInteriorGrowth.norm_complex_sin_le_exp_abs_im
      ((Real.pi : ℂ) * b)
    have him : |((Real.pi : ℂ) * b).im| = (Real.pi / 2) * |z.im| := by
      rw [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, abs_mul,
        abs_of_pos Real.pi_pos, hbim]
      ring
    rwa [him] at hs
  have hsqrtNorm : ‖(Real.sqrt Real.pi : ℂ)‖ = Real.sqrt Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  let A := Real.rpow 2000 (1 / 2 + z.re) *
    Real.rpow (2000 * (1 + |z.im|)) (1 / 2 - z.re)
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  unfold duplicationRhs
  rw [norm_div, norm_mul, norm_mul, norm_mul, hsqrtNorm,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hnum :
      ‖Complex.Gamma (1 - z)‖ * ‖(2 : ℂ) ^ z‖ * Real.sqrt Real.pi *
          ‖Complex.sin ((Real.pi : ℂ) * b)‖ ≤ 4 * A := by
    calc
      _ ≤ (A * Real.exp (-(Real.pi / 2) * |z.im|)) * 2 * 2 *
          Real.exp ((Real.pi / 2) * |z.im|) := by gcongr
      _ = 4 * A := by
        rw [show (A * Real.exp (-(Real.pi / 2) * |z.im|)) * 2 * 2 *
            Real.exp ((Real.pi / 2) * |z.im|) =
          4 * A * (Real.exp (-(Real.pi / 2) * |z.im|) *
            Real.exp ((Real.pi / 2) * |z.im|)) by ring, ← Real.exp_add]
        simp
  exact (div_le_self (by positivity) hpi).trans hnum

/-- Sharp archimedean quotient on the full shifted strip. -/
theorem gammaFactor_reflected_quotient_norm_sharp_le
    (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 0 < |z.im|) :
    ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
      4 * (Real.rpow 2000 (1 / 2 + z.re) *
        Real.rpow (2000 * (1 + |z.im|)) (1 / 2 - z.re)) := by
  have hzine : z.im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hzim
    exact lt_irrefl 0 hzim
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [RamachandraFunctionalFactorEnvelope.gammaREvenReflectedQuotientNormEq,
      mul_assoc, ← norm_mul, even_ordinaryGamma_quotient_eq_duplicationRhs hzine]
    have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
      calc
        Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi) (by linarith)
        _ = 1 := by simp
    have hdup := norm_duplicationRhs_le hzlo hzhi (b := z / 2) (by
      have him : (z / 2).im = z.im / 2 := by norm_num
      rw [him, abs_div]
      norm_num)
    exact (mul_le_mul_of_nonneg_right hpi (norm_nonneg _)).trans
      (by simpa using hdup)
  · rw [(inv_odd χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - z + 1 = 2 - z by ring]
    rw [RamachandraFunctionalFactorEnvelope.gammaROddReflectedQuotientNormEq,
      mul_assoc, ← norm_mul, odd_ordinaryGamma_quotient_eq_duplicationRhs hzine]
    have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
      calc
        Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.pi_gt_three] : 1 ≤ Real.pi) (by linarith)
        _ = 1 := by simp
    have hdup := norm_duplicationRhs_le hzlo hzhi (b := (z + 1) / 2) (by
      have him : ((z + 1) / 2).im = z.im / 2 := by norm_num
      rw [him, abs_div]
      norm_num)
    exact (mul_le_mul_of_nonneg_right hpi (norm_nonneg _)).trans
      (by simpa using hdup)

/-- Complete sharp primitive functional-factor envelope. -/
theorem norm_ramachandraFunctionalFactor_sharp_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) {z : ℂ}
    (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 0 < |z.im|) :
    ‖ramachandraFunctionalFactor χ z‖ ≤
      Real.rpow (q : ℝ) (1 / 2 - z.re) *
        (4 * (Real.rpow 2000 (1 / 2 + z.re) *
          Real.rpow (2000 * (1 + |z.im|)) (1 / 2 - z.re))) := by
  unfold ramachandraFunctionalFactor
  rw [show
      (q : ℂ) ^ (1 / 2 - z) * χ.rootNumber *
          χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z =
        ((q : ℂ) ^ (1 / 2 - z) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z) by ring,
    norm_mul]
  have hroot :
      ‖(q : ℂ) ^ (1 / 2 - z) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) (1 / 2 - z.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    simp
  rw [hroot]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_reflected_quotient_norm_sharp_le χ hzlo hzhi hzim)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end
end RamachandraFunctionalFactorSharpStrip

#print axioms RamachandraFunctionalFactorSharpStrip.norm_ramachandraFunctionalFactor_sharp_le
