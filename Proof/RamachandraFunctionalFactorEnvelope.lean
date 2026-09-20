import RamachandraShiftedFunctionalEquationBridge
import HuxleyGammaShiftedBounds

/-!
# A polynomial envelope for Ramachandra's primitive functional factor

This file proves the no-exponential-loss bound required when the shifted
Ramachandra contour is moved through the strip `-1/4 ≤ Re z ≤ 1/2`.
The exponential decay and growth in the two ordinary Gamma factors cancel
exactly.  No fourth-moment or contour estimate is assumed.
-/

namespace RamachandraFunctionalFactorEnvelope

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

private theorem stripPoint_norm_le_one_add_abs
    {a t : ℝ} (ha : |a| ≤ 1) :
    ‖GammaCompactStripScratch.stripPoint a t‖ ≤ 1 + |t| := by
  calc
    ‖GammaCompactStripScratch.stripPoint a t‖ =
        ‖(a : ℂ) + (t : ℂ) * I‖ := by
      rfl
    _ ≤ ‖(a : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
    _ = |a| + |t| := by simp [Real.norm_eq_abs]
    _ ≤ 1 + |t| := by linarith

/-- Sharp exponential-rate Gamma bound on the slightly enlarged strip used by
both parities of the shifted functional equation. -/
theorem norm_Gamma_enlarged_strip_le
    {a t : ℝ} (ha : -(1 / 2 : ℝ) ≤ a) (ha' : a ≤ 3 / 2)
    (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
  by_cases hmid : a ≤ 1 / 2
  · exact MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
      ha hmid ht
  · exact MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
      (by linarith) ha'

/-- Reciprocal Gamma bound on the denominator strip.  Below `Re z = 1/2` we
use one exact Gamma recurrence and above it the existing positive-strip bound.
The recurrence costs one polynomial factor and no exponential loss. -/
theorem norm_inv_Gamma_denominator_strip_le
    {a t : ℝ} (ha : -(1 / 8 : ℝ) ≤ a) (ha' : a ≤ 3 / 4)
    (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      12 * (1 + |t|) ^ 2 * Real.exp ((Real.pi / 2) * |t|) := by
  by_cases hmid : 1 / 2 ≤ a
  · have hmain :=
      MAPGammaInverseGrowthSharp.norm_inv_Gamma_positive_strip_le_exp_pi_half
        hmid (by linarith : a ≤ 3 / 2) ht
    calc
      ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
          12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|) := hmain
      _ ≤ 12 * (1 + |t|) ^ 2 * Real.exp ((Real.pi / 2) * |t|) := by
        have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
        rw [pow_two]
        gcongr
        nlinarith [mul_nonneg (by positivity : 0 ≤ 1 + |t|) (abs_nonneg t)]
  · let w := GammaCompactStripScratch.stripPoint a t
    have hw : w ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp [w, GammaCompactStripScratch.stripPoint] at him
      subst t
      norm_num at ht
    have hGamma : Complex.Gamma w ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro n h
      have him := congrArg Complex.im h
      simp [w, GammaCompactStripScratch.stripPoint] at him
      subst t
      norm_num at ht
    have hrec := Complex.Gamma_add_one w hw
    have hshift : w + 1 =
        GammaCompactStripScratch.stripPoint (a + 1) t := by
      exact GammaCompactStripScratch.stripPoint_add_one a t
    have hinv : (Complex.Gamma w)⁻¹ =
        w * (Complex.Gamma (w + 1))⁻¹ := by
      rw [hrec, mul_inv_rev]
      field_simp [hw, hGamma]
    have hpositive :=
      MAPGammaInverseGrowthSharp.norm_inv_Gamma_positive_strip_le_exp_pi_half
        (a := a + 1) (t := t) (by linarith) (by linarith) ht
    have haw : |a| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have hwnorm : ‖w‖ ≤ 1 + |t| :=
      stripPoint_norm_le_one_add_abs haw
    rw [hinv, norm_mul, hshift]
    calc
      ‖w‖ * ‖(Complex.Gamma
          (GammaCompactStripScratch.stripPoint (a + 1) t))⁻¹‖ ≤
        (1 + |t|) *
          (12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|)) := by
            gcongr
      _ = 12 * (1 + |t|) ^ 2 *
          Real.exp ((Real.pi / 2) * |t|) := by ring

private theorem norm_GammaR_even_reflected_quotient_eq (z : ℂ) :
    ‖Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((1 - z) / 2)‖ *
        ‖(Complex.Gamma (z / 2))⁻¹‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv,
    mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-(1 - z) / 2)‖ =
      Real.rpow Real.pi (-(1 - z.re) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-z / 2))⁻¹‖ =
      Real.rpow Real.pi (z.re / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg (le_of_lt Real.pi_pos)]
    congr 1
    simp
    ring_nf
  rw [hnum, hden]
  rw [show
      Real.rpow Real.pi (-(1 - z.re) / 2) *
          ‖Complex.Gamma ((1 - z) / 2)‖ *
          (‖(Complex.Gamma (z / 2))⁻¹‖ *
            Real.rpow Real.pi (z.re / 2)) =
        (Real.rpow Real.pi (-(1 - z.re) / 2) *
          Real.rpow Real.pi (z.re / 2)) *
          ‖Complex.Gamma ((1 - z) / 2)‖ *
          ‖(Complex.Gamma (z / 2))⁻¹‖ by ring]
  have hp : Real.rpow Real.pi (-(1 - z.re) / 2) *
      Real.rpow Real.pi (z.re / 2) =
      Real.rpow Real.pi ((-(1 - z.re) / 2) + z.re / 2) := by
    exact (Real.rpow_add Real.pi_pos _ _).symm
  rw [hp]
  congr 2
  ring

private theorem norm_GammaR_odd_reflected_quotient_eq (z : ℂ) :
    ‖Complex.Gammaℝ (2 - z) / Complex.Gammaℝ (z + 1)‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((2 - z) / 2)‖ *
        ‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv,
    mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-(2 - z) / 2)‖ =
      Real.rpow Real.pi (-(2 - z.re) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-(z + 1) / 2))⁻¹‖ =
      Real.rpow Real.pi ((z.re + 1) / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg (le_of_lt Real.pi_pos)]
    congr 1
    simp
    ring_nf
  rw [hnum, hden]
  rw [show
      Real.rpow Real.pi (-(2 - z.re) / 2) *
          ‖Complex.Gamma ((2 - z) / 2)‖ *
          (‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ *
            Real.rpow Real.pi ((z.re + 1) / 2)) =
        (Real.rpow Real.pi (-(2 - z.re) / 2) *
          Real.rpow Real.pi ((z.re + 1) / 2)) *
          ‖Complex.Gamma ((2 - z) / 2)‖ *
          ‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ by ring]
  have hp : Real.rpow Real.pi (-(2 - z.re) / 2) *
      Real.rpow Real.pi ((z.re + 1) / 2) =
      Real.rpow Real.pi ((-(2 - z.re) / 2) + (z.re + 1) / 2) := by
    exact (Real.rpow_add Real.pi_pos _ _).symm
  rw [hp]
  congr 2
  ring

/-- Public algebraic form of the even reflected `Gammaℝ` quotient.  This
wrapper lets rational-line modules combine the exact conductor exponent with
line-specific ordinary-Gamma identities. -/
theorem gammaREvenReflectedQuotientNormEq (z : ℂ) :
    ‖Complex.Gammaℝ (1 - z) / Complex.Gammaℝ z‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((1 - z) / 2)‖ *
        ‖(Complex.Gamma (z / 2))⁻¹‖ :=
  norm_GammaR_even_reflected_quotient_eq z

/-- Public algebraic form of the odd reflected `Gammaℝ` quotient. -/
theorem gammaROddReflectedQuotientNormEq (z : ℂ) :
    ‖Complex.Gammaℝ (2 - z) / Complex.Gammaℝ (z + 1)‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((2 - z) / 2)‖ *
        ‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ :=
  norm_GammaR_odd_reflected_quotient_eq z

private theorem one_sub_geometry (z : ℂ) :
    (1 - z) / 2 = GammaCompactStripScratch.stripPoint
      ((1 - z.re) / 2) (-z.im / 2) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring

private theorem two_sub_geometry (z : ℂ) :
    (2 - z) / 2 = GammaCompactStripScratch.stripPoint
      ((2 - z.re) / 2) (-z.im / 2) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring

private theorem half_geometry (z : ℂ) :
    z / 2 = GammaCompactStripScratch.stripPoint
      (z.re / 2) (z.im / 2) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring

private theorem one_add_half_geometry (z : ℂ) :
    (z + 1) / 2 = GammaCompactStripScratch.stripPoint
      ((z.re + 1) / 2) (z.im / 2) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring

/-- The archimedean quotient in Ramachandra's functional factor has polynomial
size throughout the whole shifted strip.  The exponential Gamma rates cancel
rather than being discarded separately. -/
theorem gammaFactor_reflected_quotient_norm_le
    (χ : DirichletCharacter ℂ q) {z : ℂ}
    (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 2 ≤ |z.im|) :
    ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
      144 * (1 + |z.im|) ^ 3 := by
  have ht : 1 ≤ |z.im / 2| := by
    rw [abs_div]
    norm_num
    linarith
  have habsneg : |-z.im / 2| = |z.im / 2| := by
    rw [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]
  have hhalf : 1 + |z.im / 2| ≤ 1 + |z.im| := by
    rw [abs_div]
    norm_num
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [norm_GammaR_even_reflected_quotient_eq, one_sub_geometry,
      half_geometry]
    have hnum := norm_Gamma_enlarged_strip_le
      (a := (1 - z.re) / 2) (t := -z.im / 2)
      (by linarith) (by linarith) (by simpa [habsneg] using ht)
    have hden := norm_inv_Gamma_denominator_strip_le
      (a := z.re / 2) (t := z.im / 2)
      (by linarith) (by linarith) ht
    have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
      calc
        Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
            (by linarith)
        _ = 1 := by simp
    calc
      Real.rpow Real.pi (z.re - 1 / 2) *
          ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint ((1 - z.re) / 2)
              (-z.im / 2))‖ *
          ‖(Complex.Gamma
            (GammaCompactStripScratch.stripPoint (z.re / 2)
              (z.im / 2)))⁻¹‖ ≤
        1 *
          (12 * (1 + |z.im / 2|) *
            Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
          (12 * (1 + |z.im / 2|) ^ 2 *
            Real.exp ((Real.pi / 2) * |z.im / 2|)) := by
              gcongr
              simpa [habsneg] using hnum
      _ = 144 * (1 + |z.im / 2|) ^ 3 := by
        have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) *
              Real.exp ((Real.pi / 2) * |z.im / 2|) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        rw [show
          1 * (12 * (1 + |z.im / 2|) *
              Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
              (12 * (1 + |z.im / 2|) ^ 2 *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) =
            144 * (1 + |z.im / 2|) ^ 3 *
              (Real.exp (-(Real.pi / 2) * |z.im / 2|) *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) by ring,
          hexp, mul_one]
      _ ≤ 144 * (1 + |z.im|) ^ 3 := by gcongr
  · rw [(inv_odd χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - z + 1 = 2 - z by ring]
    rw [norm_GammaR_odd_reflected_quotient_eq, two_sub_geometry,
      one_add_half_geometry]
    have hnum := norm_Gamma_enlarged_strip_le
      (a := (2 - z.re) / 2) (t := -z.im / 2)
      (by linarith) (by linarith) (by simpa [habsneg] using ht)
    have hden := norm_inv_Gamma_denominator_strip_le
      (a := (z.re + 1) / 2) (t := z.im / 2)
      (by linarith) (by linarith) ht
    have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
      calc
        Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
            (by linarith)
        _ = 1 := by simp
    calc
      Real.rpow Real.pi (z.re - 1 / 2) *
          ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint ((2 - z.re) / 2)
              (-z.im / 2))‖ *
          ‖(Complex.Gamma
            (GammaCompactStripScratch.stripPoint ((z.re + 1) / 2)
              (z.im / 2)))⁻¹‖ ≤
        1 *
          (12 * (1 + |z.im / 2|) *
            Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
          (12 * (1 + |z.im / 2|) ^ 2 *
            Real.exp ((Real.pi / 2) * |z.im / 2|)) := by
              gcongr
              simpa [habsneg] using hnum
      _ = 144 * (1 + |z.im / 2|) ^ 3 := by
        have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) *
              Real.exp ((Real.pi / 2) * |z.im / 2|) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        rw [show
          1 * (12 * (1 + |z.im / 2|) *
              Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
              (12 * (1 + |z.im / 2|) ^ 2 *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) =
            144 * (1 + |z.im / 2|) ^ 3 *
              (Real.exp (-(Real.pi / 2) * |z.im / 2|) *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) by ring,
          hexp, mul_one]
      _ ≤ 144 * (1 + |z.im|) ^ 3 := by gcongr

/-- Complete primitive functional-factor envelope retaining the exact
conductor exponent.  This exact dependence is essential on Ramachandra's near
line, where replacing it by the strip maximum `q^(3/4)` would be fatal. -/
theorem norm_ramachandraFunctionalFactor_le_exactExponent
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) {z : ℂ}
    (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 2 ≤ |z.im|) :
    ‖ramachandraFunctionalFactor χ z‖ ≤
      Real.rpow (q : ℝ) (1 / 2 - z.re) *
        (144 * (1 + |z.im|) ^ 3) := by
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
    (gammaFactor_reflected_quotient_norm_le χ hzlo hzhi hzim)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Complete primitive functional-factor envelope on Ramachandra's shifted
strip.  In particular, it has no exponential loss in the ordinate. -/
theorem norm_ramachandraFunctionalFactor_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) {z : ℂ}
    (hzlo : -(1 / 4 : ℝ) ≤ z.re) (hzhi : z.re ≤ 1 / 2)
    (hzim : 2 ≤ |z.im|) :
    ‖ramachandraFunctionalFactor χ z‖ ≤
      Real.rpow (q : ℝ) (3 / 4) *
        (144 * (1 + |z.im|) ^ 3) := by
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
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hcond : Real.rpow (q : ℝ) (1 / 2 - z.re) ≤
      Real.rpow (q : ℝ) (3 / 4) :=
    Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
  exact mul_le_mul hcond
    (gammaFactor_reflected_quotient_norm_le χ hzlo hzhi hzim)
    (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-! ## The bounded-ordinate completion

The large-ordinate estimate above is the source-critical cancellation.  The
compact complementary range must nevertheless be covered explicitly before
one may integrate the whole vertical contour.  We isolate that compact step
here rather than silently treating the functional factor as bounded near the
origin. -/

/-- Ordinary Gamma is uniformly polynomially bounded on the positive strip
needed by both parity numerators, with no lower bound on the ordinate. -/
theorem norm_Gamma_quarter_nineEighth_le
    {a t : ℝ} (ha : (1 / 4 : ℝ) ≤ a) (ha' : a ≤ 9 / 8) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      48 * (1 + |t|) * Real.exp (-|t|) := by
  by_cases hhalf : 1 / 2 ≤ a
  · have hstrip := GammaCompactStripScratch.norm_Gamma_stripPoint_le_four_upper
      (s := a) (t := t) hhalf (by linarith : a ≤ 3 / 2)
    have htop := GammaCompactStripScratch.norm_Gamma_upperPoint_le_exp t
    calc
      ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
          4 * ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint (3 / 2) t)‖ := hstrip
      _ ≤ 4 * (3 * (1 + |t|) * Real.exp (-|t|)) := by gcongr
      _ ≤ 48 * (1 + |t|) * Real.exp (-|t|) := by
        have hfront : 0 ≤ (1 + |t|) * Real.exp (-|t|) := by positivity
        nlinarith
  · let z := GammaCompactStripScratch.stripPoint a t
    have hz : z ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [z, GammaCompactStripScratch.stripPoint] at hre
      linarith
    have hrec := Complex.Gamma_add_one z hz
    have hadd : z + 1 =
        GammaCompactStripScratch.stripPoint (a + 1) t := by
      exact GammaCompactStripScratch.stripPoint_add_one a t
    rw [hadd] at hrec
    have hshift := GammaCompactStripScratch.norm_Gamma_stripPoint_le_four_upper
      (s := a + 1) (t := t) (by linarith) (by linarith)
    have htop := GammaCompactStripScratch.norm_Gamma_upperPoint_le_exp t
    have hshiftBound :
        ‖Complex.Gamma
          (GammaCompactStripScratch.stripPoint (a + 1) t)‖ ≤
          12 * (1 + |t|) * Real.exp (-|t|) := by
      calc
        ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint (a + 1) t)‖ ≤
            4 * ‖Complex.Gamma
              (GammaCompactStripScratch.stripPoint (3 / 2) t)‖ := hshift
        _ ≤ 4 * (3 * (1 + |t|) * Real.exp (-|t|)) := by gcongr
        _ = 12 * (1 + |t|) * Real.exp (-|t|) := by ring
    have hnormRec := congrArg norm hrec
    rw [norm_mul] at hnormRec
    have hzlower : (1 / 4 : ℝ) ≤ ‖z‖ := by
      have hre := Complex.abs_re_le_norm z
      have hzre : z.re = a := by simp [z, GammaCompactStripScratch.stripPoint]
      rw [hzre, abs_of_nonneg (by linarith)] at hre
      exact ha.trans hre
    have hgamma0 : 0 ≤ ‖Complex.Gamma z‖ := norm_nonneg _
    have hB0 : 0 ≤ (1 + |t|) * Real.exp (-|t|) := by positivity
    change ‖Complex.Gamma z‖ ≤ 48 * (1 + |t|) * Real.exp (-|t|)
    nlinarith

/-- The reciprocal Gamma denominator is bounded on the compact small-height
rectangle.  This uses only that `1/Gamma` is entire; the returned constant is
absolute and independent of the character and conductor. -/
theorem exists_norm_inv_Gamma_denominator_compact_bound :
    ∃ Cinv : ℝ, 1 ≤ Cinv ∧
      ∀ a t : ℝ, -(1 / 8 : ℝ) ≤ a → a ≤ 3 / 4 → |t| ≤ 1 →
        ‖(Complex.Gamma
          (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤ Cinv := by
  let K : Set (ℝ × ℝ) :=
    Set.Icc (-(1 / 8 : ℝ)) (3 / 4) ×ˢ Set.Icc (-1 : ℝ) 1
  let f : ℝ × ℝ → ℂ := fun p =>
    (Complex.Gamma
      (GammaCompactStripScratch.stripPoint p.1 p.2))⁻¹
  have hf : Continuous f := by
    dsimp [f]
    apply Complex.differentiable_one_div_Gamma.continuous.comp
    unfold GammaCompactStripScratch.stripPoint
    fun_prop
  obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ x ∈ K, ‖f x‖ ≤ C₀ :=
    (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max 1 C₀, le_max_left _ _, ?_⟩
  intro a t ha ha' ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by
    exact (abs_le.mp ht)
  have hp : (a, t) ∈ K := by
    exact ⟨⟨ha, ha'⟩, ht'⟩
  exact (hC₀ (a, t) hp).trans (le_max_right _ _)

/-- Full bounded-ordinate completion of the archimedean quotient. -/
theorem exists_gammaFactor_reflected_quotient_norm_le_global :
    ∃ Cγ : ℝ, 144 ≤ Cγ ∧
      ∀ (χ : DirichletCharacter ℂ q) (z : ℂ),
        -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
        ‖χ⁻¹.gammaFactor (1 - z) / χ.gammaFactor z‖ ≤
          Cγ * (1 + |z.im|) ^ 3 := by
  obtain ⟨Cinv, hCinv, hInv⟩ :=
    exists_norm_inv_Gamma_denominator_compact_bound
  let Cγ : ℝ := max 144 (48 * Cinv)
  refine ⟨Cγ, le_max_left _ _, ?_⟩
  intro χ z hzlo hzhi
  by_cases hlarge : 2 ≤ |z.im|
  · exact (gammaFactor_reflected_quotient_norm_le χ hzlo hzhi hlarge).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by positivity : 0 ≤ (1 + |z.im|) ^ 3))
  · have hsmall : |z.im / 2| ≤ 1 := by
      rw [abs_div]
      norm_num
      linarith
    have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
      calc
        Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
          Real.rpow_le_rpow_of_exponent_le
            (by linarith [Real.pi_gt_three]) (by linarith)
        _ = 1 := by simp
    have hone : 1 ≤ 1 + |z.im| := by linarith [abs_nonneg z.im]
    have hpoly : 1 + |z.im / 2| ≤ (1 + |z.im|) ^ 3 := by
      have hhalf : |z.im / 2| ≤ |z.im| := by
        rw [abs_div]
        norm_num
      have hsq : 1 + |z.im| ≤ (1 + |z.im|) ^ 3 := by
        nlinarith [sq_nonneg (1 + |z.im|), mul_self_le_mul_self
          (by positivity : 0 ≤ (1 : ℝ)) hone]
      have hadd : 1 + |z.im / 2| ≤ 1 + |z.im| := by linarith
      exact hadd.trans hsq
    rcases χ.even_or_odd with hχ | hχ
    · rw [(inv_even χ hχ).gammaFactor_def, hχ.gammaFactor_def]
      rw [norm_GammaR_even_reflected_quotient_eq, one_sub_geometry,
        half_geometry]
      have hnum := norm_Gamma_quarter_nineEighth_le
        (a := (1 - z.re) / 2) (t := -z.im / 2)
        (by linarith) (by linarith)
      have hden := hInv (z.re / 2) (z.im / 2)
        (by linarith) (by linarith) hsmall
      have hexp : Real.exp (-|-z.im / 2|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
      have hnum' :
          ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint ((1 - z.re) / 2)
              (-z.im / 2))‖ ≤ 48 * (1 + |z.im / 2|) := by
        calc
          _ ≤ 48 * (1 + |-z.im / 2|) * Real.exp (-|-z.im / 2|) := hnum
          _ ≤ 48 * (1 + |-z.im / 2|) * 1 := by gcongr
          _ = 48 * (1 + |z.im / 2|) := by
            rw [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]
            ring
      calc
        Real.rpow Real.pi (z.re - 1 / 2) *
            ‖Complex.Gamma
              (GammaCompactStripScratch.stripPoint ((1 - z.re) / 2)
                (-z.im / 2))‖ *
            ‖(Complex.Gamma
              (GammaCompactStripScratch.stripPoint (z.re / 2)
                (z.im / 2)))⁻¹‖ ≤
          1 * (48 * (1 + |z.im / 2|)) * Cinv := by gcongr
        _ ≤ (48 * Cinv) * (1 + |z.im|) ^ 3 := by
          have hC0 : 0 ≤ Cinv := by linarith
          nlinarith
        _ ≤ Cγ * (1 + |z.im|) ^ 3 := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (by positivity)
    · rw [(inv_odd χ hχ).gammaFactor_def, hχ.gammaFactor_def]
      rw [show 1 - z + 1 = 2 - z by ring]
      rw [norm_GammaR_odd_reflected_quotient_eq, two_sub_geometry,
        one_add_half_geometry]
      have hnum := norm_Gamma_quarter_nineEighth_le
        (a := (2 - z.re) / 2) (t := -z.im / 2)
        (by linarith) (by linarith)
      have hden := hInv ((z.re + 1) / 2) (z.im / 2)
        (by linarith) (by linarith) hsmall
      have hexp : Real.exp (-|-z.im / 2|) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
      have hnum' :
          ‖Complex.Gamma
            (GammaCompactStripScratch.stripPoint ((2 - z.re) / 2)
              (-z.im / 2))‖ ≤ 48 * (1 + |z.im / 2|) := by
        calc
          _ ≤ 48 * (1 + |-z.im / 2|) * Real.exp (-|-z.im / 2|) := hnum
          _ ≤ 48 * (1 + |-z.im / 2|) * 1 := by gcongr
          _ = 48 * (1 + |z.im / 2|) := by
            rw [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]
            ring
      calc
        Real.rpow Real.pi (z.re - 1 / 2) *
            ‖Complex.Gamma
              (GammaCompactStripScratch.stripPoint ((2 - z.re) / 2)
                (-z.im / 2))‖ *
            ‖(Complex.Gamma
              (GammaCompactStripScratch.stripPoint ((z.re + 1) / 2)
                (z.im / 2)))⁻¹‖ ≤
          1 * (48 * (1 + |z.im / 2|)) * Cinv := by gcongr
        _ ≤ (48 * Cinv) * (1 + |z.im|) ^ 3 := by
          have hC0 : 0 ≤ Cinv := by linarith
          nlinarith
        _ ≤ Cγ * (1 + |z.im|) ^ 3 := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _)
            (by positivity)

/-- Global primitive functional-factor envelope, valid at every ordinate and
retaining the exact conductor exponent. -/
theorem exists_norm_ramachandraFunctionalFactor_le_global :
    ∃ Cγ : ℝ, 144 ≤ Cγ ∧
      ∀ (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ z : ℂ,
        -(1 / 4 : ℝ) ≤ z.re → z.re ≤ 1 / 2 →
        ‖ramachandraFunctionalFactor χ z‖ ≤
          Real.rpow (q : ℝ) (1 / 2 - z.re) *
            (Cγ * (1 + |z.im|) ^ 3) := by
  obtain ⟨Cγ, hCγ, hquot⟩ :=
    exists_gammaFactor_reflected_quotient_norm_le_global (q := q)
  refine ⟨Cγ, hCγ, ?_⟩
  intro χ hprim z hzlo hzhi
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
  exact mul_le_mul_of_nonneg_left (hquot χ z hzlo hzhi)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-! ## Exact rational line used by the shifted-contour workaround -/

/-- The fixed line `Re z=-1/2`.  On this line the ordinary Gamma factors
differ by exactly one, so recurrence gives the correct first power of the
height without any appeal to complex Stirling. -/
def ramachandraNegHalfLine (t : ℝ) : ℂ :=
  (-(1 / 2 : ℝ) : ℂ) + t * I

theorem gammaFactor_reflected_quotient_norm_negHalfLine_le
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖χ⁻¹.gammaFactor (1 - ramachandraNegHalfLine t) /
        χ.gammaFactor (ramachandraNegHalfLine t)‖ ≤
      1 + |t| := by
  let z : ℂ := ramachandraNegHalfLine t
  have hzre : z.re = -(1 / 2 : ℝ) := by
    simp [z, ramachandraNegHalfLine]
  have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
    rw [hzre]
    have hbase : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    convert Real.rpow_le_one_of_one_le_of_nonpos hbase
      (by norm_num : (-(1 : ℝ)) ≤ 0) using 1 <;> norm_num
  rcases χ.even_or_odd with hχ | hχ
  · rw [(inv_even χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [norm_GammaR_even_reflected_quotient_eq]
    let b : ℂ := z / 2
    have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one b
    have hnumConj : (1 - z) / 2 = star (b + 1) := by
      apply Complex.ext <;>
        simp [b, z, ramachandraNegHalfLine] <;> ring
    have hGammaNorm :
        ‖Complex.Gamma ((1 - z) / 2)‖ =
          ‖Complex.Gamma (b + 1)‖ := by
      rw [hnumConj]
      change ‖Complex.Gamma ((starRingEnd ℂ) (b + 1))‖ = _
      rw [Complex.Gamma_conj]
      exact Complex.norm_conj _
    have hGammaNe : Complex.Gamma (b + 1) ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      simp [b, z, ramachandraNegHalfLine] at hre
      linarith
    have hcancel :
        ‖Complex.Gamma ((1 - z) / 2)‖ *
          ‖(Complex.Gamma b)⁻¹‖ = ‖b‖ := by
      rw [hrec, norm_mul, hGammaNorm, norm_inv,
        inv_eq_one_div]
      field_simp [norm_ne_zero_iff.mpr hGammaNe]
    have hb : ‖b‖ ≤ 1 + |t| := by
      calc
        ‖b‖ = ‖z‖ / 2 := by simp [b]
        _ ≤ (|(z.re)| + |z.im|) / 2 := by
          gcongr
          exact Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + |t| := by
          simp [z, ramachandraNegHalfLine]
          linarith [abs_nonneg t]
    rw [show z / 2 = b by rfl, mul_assoc, hcancel]
    exact (mul_le_mul hpi hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
  · rw [(inv_odd χ hχ).gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - z + 1 = 2 - z by ring]
    rw [norm_GammaR_odd_reflected_quotient_eq]
    let b : ℂ := (z + 1) / 2
    let a : ℂ := (2 - z) / 2
    have ha : a = star b + 1 := by
      apply Complex.ext <;>
        simp [a, b, z, ramachandraNegHalfLine] <;> ring
    have hbstar : star b ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      simp [b, z, ramachandraNegHalfLine] at hre
      norm_num at hre
    have hrec := Complex.Gamma_add_one (star b) hbstar
    have hGammaNe : Complex.Gamma b ≠ 0 := by
      apply Complex.Gamma_ne_zero
      intro m hm
      have hre := congrArg Complex.re hm
      simp [b, z, ramachandraNegHalfLine] at hre
      linarith
    have hnum :
        ‖Complex.Gamma a‖ = ‖b‖ * ‖Complex.Gamma b‖ := by
      rw [ha, hrec, norm_mul]
      have hGammaStar : ‖Complex.Gamma (star b)‖ =
          ‖Complex.Gamma b‖ := by
        change ‖Complex.Gamma ((starRingEnd ℂ) b)‖ = _
        rw [Complex.Gamma_conj]
        exact Complex.norm_conj _
      rw [norm_star, hGammaStar]
    have hcancel :
        ‖Complex.Gamma a‖ * ‖(Complex.Gamma b)⁻¹‖ = ‖b‖ := by
      rw [hnum, norm_inv, inv_eq_one_div]
      field_simp [norm_ne_zero_iff.mpr hGammaNe]
    have hb : ‖b‖ ≤ 1 + |t| := by
      calc
        ‖b‖ ≤ |b.re| + |b.im| := Complex.norm_le_abs_re_add_abs_im b
        _ = (1 / 4 : ℝ) + |t| / 2 := by
          simp [b, z, ramachandraNegHalfLine, abs_div]
          norm_num
        _ ≤ 1 + |t| := by linarith [abs_nonneg t]
    rw [show (2 - z) / 2 = a by rfl, show (z + 1) / 2 = b by rfl,
      mul_assoc, hcancel]
    exact (mul_le_mul hpi hb (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)

/-- Complete functional-factor bound on `Re z=-1/2`, retaining the exact
conductor exponent and the sharp first height power. -/
theorem norm_ramachandraFunctionalFactor_negHalfLine_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ) :
    ‖ramachandraFunctionalFactor χ (ramachandraNegHalfLine t)‖ ≤
      Real.rpow (q : ℝ) 1 * (1 + |t|) := by
  unfold ramachandraFunctionalFactor
  rw [show
      (q : ℂ) ^ (1 / 2 - ramachandraNegHalfLine t) * χ.rootNumber *
          χ⁻¹.gammaFactor (1 - ramachandraNegHalfLine t) /
            χ.gammaFactor (ramachandraNegHalfLine t) =
        ((q : ℂ) ^ (1 / 2 - ramachandraNegHalfLine t) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (1 - ramachandraNegHalfLine t) /
            χ.gammaFactor (ramachandraNegHalfLine t)) by ring,
    norm_mul]
  have hroot :
      ‖(q : ℂ) ^ (1 / 2 - ramachandraNegHalfLine t) * χ.rootNumber‖ =
        Real.rpow (q : ℝ) 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim,
      mul_one]
    congr 2
    simp [ramachandraNegHalfLine]
    norm_num
  rw [hroot]
  exact mul_le_mul_of_nonneg_left
    (gammaFactor_reflected_quotient_norm_negHalfLine_le χ t)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

end

end RamachandraFunctionalFactorEnvelope

#print axioms RamachandraFunctionalFactorEnvelope.norm_Gamma_enlarged_strip_le
#print axioms RamachandraFunctionalFactorEnvelope.norm_inv_Gamma_denominator_strip_le
#print axioms RamachandraFunctionalFactorEnvelope.gammaFactor_reflected_quotient_norm_le
#print axioms RamachandraFunctionalFactorEnvelope.norm_ramachandraFunctionalFactor_le_exactExponent
#print axioms RamachandraFunctionalFactorEnvelope.norm_ramachandraFunctionalFactor_le
#print axioms RamachandraFunctionalFactorEnvelope.exists_norm_inv_Gamma_denominator_compact_bound
#print axioms RamachandraFunctionalFactorEnvelope.exists_norm_ramachandraFunctionalFactor_le_global
#print axioms RamachandraFunctionalFactorEnvelope.gammaFactor_reflected_quotient_norm_negHalfLine_le
#print axioms RamachandraFunctionalFactorEnvelope.norm_ramachandraFunctionalFactor_negHalfLine_le
