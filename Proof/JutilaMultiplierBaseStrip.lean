import JutilaMultiplierRecurrence
import GammaInverseGrowthSharp
import PrimitiveRootNumberNorm

/-!
# Polynomial base-strip bound for Jutila's multiplier

After the exact two-step recurrence, the terminal point lies in
`-2 ≤ Re z ≤ 0`.  This file certifies the high-ordinate bound on that fixed
strip.  Only one or two Gamma recurrences are needed, so the exponential
rates cancel exactly between the numerator and reciprocal denominator.
-/

namespace JutilaMultiplierBaseStrip

open Complex Real DirichletCharacter
open JutilaCriticalPartialTruncation
open MAPGammaCompactStripSharp MAPGammaInverseGrowthSharp

noncomputable section

private theorem stripPoint_norm_le_two_mul_one_add_abs
    {a t : ℝ} (ha : |a| ≤ 2) :
    ‖GammaCompactStripScratch.stripPoint a t‖ ≤ 2 * (1 + |t|) := by
  calc
    ‖GammaCompactStripScratch.stripPoint a t‖ ≤ |a| + |t| := by
      simpa [GammaCompactStripScratch.stripPoint] using
        Complex.norm_le_abs_re_add_abs_im
          (GammaCompactStripScratch.stripPoint a t)
    _ ≤ 2 + |t| := by linarith
    _ ≤ 2 * (1 + |t|) := by linarith [abs_nonneg t]

theorem norm_Gamma_half_two_le
    {a t : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 2) (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      24 * (1 + |t|) ^ 2 *
        Real.exp (-(Real.pi / 2) * |t|) := by
  by_cases hmid : a ≤ 3 / 2
  · have h := norm_Gamma_positive_strip_le_exp_pi_half (t := t) ha hmid
    have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hy0 : 0 ≤ 1 + |t| := by positivity
    have hpow : 1 + |t| ≤ (1 + |t|) ^ 2 := by
      have hm := mul_nonneg hy0 (sub_nonneg.mpr hone)
      nlinarith [hm]
    calc
      ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
          12 * (1 + |t|) *
            Real.exp (-(Real.pi / 2) * |t|) := h
      _ ≤ 24 * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith
  · let w := GammaCompactStripScratch.stripPoint (a - 1) t
    have hw : w ≠ 0 := by
      intro hzero
      have him := congrArg Complex.im hzero
      simp [w, GammaCompactStripScratch.stripPoint] at him
      subst t
      norm_num at ht
    have hrec := Complex.Gamma_add_one w hw
    have hadd : w + 1 = GammaCompactStripScratch.stripPoint a t := by
      apply Complex.ext <;> simp [w, GammaCompactStripScratch.stripPoint]
    rw [hadd] at hrec
    have hbase := norm_Gamma_positive_strip_le_exp_pi_half
      (a := a - 1) (t := t) (by linarith) (by linarith)
    have hwnorm : ‖w‖ ≤ 2 * (1 + |t|) := by
      apply stripPoint_norm_le_two_mul_one_add_abs
      rw [abs_le]
      constructor <;> linarith
    rw [hrec, norm_mul]
    calc
      ‖w‖ * ‖Complex.Gamma w‖ ≤
          (2 * (1 + |t|)) *
            (12 * (1 + |t|) *
              Real.exp (-(Real.pi / 2) * |t|)) := by
        gcongr
      _ = 24 * (1 + |t|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |t|) := by ring

theorem norm_inv_Gamma_neg_one_half_le
    {a t : ℝ} (ha : -1 ≤ a) (ha' : a ≤ 1 / 2) (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      48 * (1 + |t|) ^ 3 *
        Real.exp ((Real.pi / 2) * |t|) := by
  let w := GammaCompactStripScratch.stripPoint a t
  have hwNorm : ‖w‖ ≤ 2 * (1 + |t|) := by
    apply stripPoint_norm_le_two_mul_one_add_abs
    rw [abs_le]
    constructor <;> linarith
  by_cases hhalf : 1 / 2 ≤ a
  · have hbase := norm_inv_Gamma_positive_strip_le_exp_pi_half
      hhalf (by linarith : a ≤ 3 / 2) ht
    have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hy0 : 0 ≤ 1 + |t| := by positivity
    have hpow2 : 1 + |t| ≤ (1 + |t|) ^ 2 := by
      have hm := mul_nonneg hy0 (sub_nonneg.mpr hone)
      nlinarith [hm]
    have hpow3 : 1 + |t| ≤ (1 + |t|) ^ 3 := by
      calc
        1 + |t| ≤ (1 + |t|) ^ 2 := hpow2
        _ ≤ (1 + |t|) ^ 3 := by
          rw [pow_succ]
          exact le_mul_of_one_le_right (sq_nonneg _) hone
    calc
      ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
          12 * (1 + |t|) *
            Real.exp ((Real.pi / 2) * |t|) := hbase
      _ ≤ 48 * (1 + |t|) ^ 3 *
          Real.exp ((Real.pi / 2) * |t|) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        nlinarith
  · by_cases hminus : -(1 / 2 : ℝ) ≤ a
    · have hrec := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
      have hadd : w + 1 =
          GammaCompactStripScratch.stripPoint (a + 1) t := by
        exact GammaCompactStripScratch.stripPoint_add_one a t
      have hbase := norm_inv_Gamma_positive_strip_le_exp_pi_half
        (a := a + 1) (t := t) (by linarith) (by linarith) ht
      change ‖(Complex.Gamma w)⁻¹‖ ≤ _
      rw [hrec, norm_mul, hadd]
      calc
        ‖w‖ *
            ‖(Complex.Gamma
              (GammaCompactStripScratch.stripPoint (a + 1) t))⁻¹‖ ≤
          (2 * (1 + |t|)) *
            (12 * (1 + |t|) *
              Real.exp ((Real.pi / 2) * |t|)) := by gcongr
        _ ≤ 48 * (1 + |t|) ^ 3 *
            Real.exp ((Real.pi / 2) * |t|) := by
          have hone : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
          have hy0 : 0 ≤ 1 + |t| := by positivity
          have hpow : (1 + |t|) ^ 2 ≤ (1 + |t|) ^ 3 := by
            rw [pow_succ]
            exact le_mul_of_one_le_right (sq_nonneg _) hone
          rw [show 2 * (1 + |t|) *
              (12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|)) =
            (24 * (1 + |t|) ^ 2) *
              Real.exp ((Real.pi / 2) * |t|) by ring]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          nlinarith
    · let w1 := GammaCompactStripScratch.stripPoint (a + 1) t
      have hw1Norm : ‖w1‖ ≤ 2 * (1 + |t|) := by
        apply stripPoint_norm_le_two_mul_one_add_abs
        rw [abs_le]
        constructor <;> linarith
      have hrec0 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w
      have hrec1 := Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one w1
      have hadd0 : w + 1 = w1 := by
        exact GammaCompactStripScratch.stripPoint_add_one a t
      have hadd1 : w1 + 1 =
          GammaCompactStripScratch.stripPoint (a + 2) t := by
        apply Complex.ext <;>
          simp [w1, GammaCompactStripScratch.stripPoint] <;> ring
      have hbase := norm_inv_Gamma_positive_strip_le_exp_pi_half
        (a := a + 2) (t := t) (by linarith) (by linarith) ht
      change ‖(Complex.Gamma w)⁻¹‖ ≤ _
      rw [hrec0, hadd0, hrec1, norm_mul, norm_mul, hadd1]
      calc
        ‖w‖ * (‖w1‖ *
            ‖(Complex.Gamma
              (GammaCompactStripScratch.stripPoint (a + 2) t))⁻¹‖) =
          ‖w‖ * ‖w1‖ *
            ‖(Complex.Gamma
              (GammaCompactStripScratch.stripPoint (a + 2) t))⁻¹‖ := by ring
        _ ≤ (2 * (1 + |t|)) * (2 * (1 + |t|)) *
            (12 * (1 + |t|) *
              Real.exp ((Real.pi / 2) * |t|)) := by
          gcongr
        _ = 48 * (1 + |t|) ^ 3 *
            Real.exp ((Real.pi / 2) * |t|) := by ring

private theorem evenQuotient_norm_eq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.Even) (z : ℂ) :
    ‖chi⁻¹.gammaFactor (1 - z) / chi.gammaFactor z‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((1 - z) / 2)‖ *
        ‖(Complex.Gamma (z / 2))⁻¹‖ := by
  have hinv : chi⁻¹.Even := by
    simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
      congrArg (fun u : ℂ => u⁻¹) hchi
  rw [hinv.gammaFactor_def, hchi.gammaFactor_def,
    Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv, mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-(1 - z) / 2)‖ =
      Real.rpow Real.pi (-(1 - z.re) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-z / 2))⁻¹‖ =
      Real.rpow Real.pi (z.re / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg Real.pi_pos.le]
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

private theorem oddQuotient_norm_eq
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi.Odd) (z : ℂ) :
    ‖chi⁻¹.gammaFactor (1 - z) / chi.gammaFactor z‖ =
      Real.rpow Real.pi (z.re - 1 / 2) *
        ‖Complex.Gamma ((2 - z) / 2)‖ *
        ‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ := by
  have hinv : chi⁻¹.Odd := by
    simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
      inv_one] using congrArg (fun u : ℂ => u⁻¹) hchi
  rw [hinv.gammaFactor_def, hchi.gammaFactor_def]
  rw [show 1 - z + 1 = 2 - z by ring]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, div_eq_mul_inv, mul_inv_rev]
  simp only [norm_mul]
  have hnum : ‖(Real.pi : ℂ) ^ (-(2 - z) / 2)‖ =
      Real.rpow Real.pi (-(2 - z.re) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    simp
  have hden : ‖((Real.pi : ℂ) ^ (-(z + 1) / 2))⁻¹‖ =
      Real.rpow Real.pi ((z.re + 1) / 2) := by
    rw [norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      ← Real.rpow_neg Real.pi_pos.le]
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

/-- Uniform polynomial archimedean quotient on the recurrence base strip. -/
theorem gammaFactor_quotient_baseStrip_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hzlo : -2 ≤ z.re) (hzhi : z.re ≤ 0) (hzim : 2 ≤ |z.im|) :
    ‖chi⁻¹.gammaFactor (1 - z) / chi.gammaFactor z‖ ≤
      1152 * (1 + |z.im|) ^ 5 := by
  have ht : 1 ≤ |z.im / 2| := by
    rw [abs_div]
    norm_num
    linarith
  have hpi : Real.rpow Real.pi (z.re - 1 / 2) ≤ 1 := by
    calc
      Real.rpow Real.pi (z.re - 1 / 2) ≤ Real.rpow Real.pi 0 :=
        Real.rpow_le_rpow_of_exponent_le
          (by linarith [Real.pi_gt_three]) (by linarith)
      _ = 1 := by simp
  rcases chi.even_or_odd with hchi | hchi
  · rw [evenQuotient_norm_eq chi hchi z]
    have hnum := norm_Gamma_half_two_le
      (a := (1 - z.re) / 2) (t := -z.im / 2)
      (by linarith) (by linarith) (by
        simpa only [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]
          using ht)
    have hden := norm_inv_Gamma_neg_one_half_le
      (a := z.re / 2) (t := z.im / 2)
      (by linarith) (by linarith) ht
    have hgeom1 : (1 - z) / 2 =
        GammaCompactStripScratch.stripPoint ((1 - z.re) / 2) (-z.im / 2) := by
      apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring
    have hgeom2 : z / 2 =
        GammaCompactStripScratch.stripPoint (z.re / 2) (z.im / 2) := by
      apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
    rw [← hgeom1] at hnum
    rw [← hgeom2] at hden
    have hnum' : ‖Complex.Gamma ((1 - z) / 2)‖ ≤
        24 * (1 + |z.im / 2|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |z.im / 2|) := by
      simpa only [show |-z.im / 2| = |z.im / 2| by
        rw [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]] using hnum
    have habs : |z.im / 2| ≤ |z.im| := by
      rw [abs_div]
      norm_num
    calc
      Real.rpow Real.pi (z.re - 1 / 2) *
          ‖Complex.Gamma ((1 - z) / 2)‖ *
          ‖(Complex.Gamma (z / 2))⁻¹‖ ≤
        1 * (24 * (1 + |z.im / 2|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
          (48 * (1 + |z.im / 2|) ^ 3 *
            Real.exp ((Real.pi / 2) * |z.im / 2|)) := by
          gcongr
      _ ≤ 1152 * (1 + |z.im|) ^ 5 := by
        have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) *
            Real.exp ((Real.pi / 2) * |z.im / 2|) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        rw [show 1 * (24 * (1 + |z.im / 2|) ^ 2 *
              Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
              (48 * (1 + |z.im / 2|) ^ 3 *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) =
            1152 * (1 + |z.im / 2|) ^ 5 *
              (Real.exp (-(Real.pi / 2) * |z.im / 2|) *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) by ring,
          hexp, mul_one]
        have hp : (1 + |z.im / 2|) ^ 5 ≤ (1 + |z.im|) ^ 5 := by gcongr
        exact mul_le_mul_of_nonneg_left hp (by norm_num)

  · rw [oddQuotient_norm_eq chi hchi z]
    have hnum := norm_Gamma_half_two_le
      (a := (2 - z.re) / 2) (t := -z.im / 2)
      (by linarith) (by linarith) (by
        simpa only [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]
          using ht)
    have hden := norm_inv_Gamma_neg_one_half_le
      (a := (z.re + 1) / 2) (t := z.im / 2)
      (by linarith) (by linarith) ht
    have hgeom1 : (2 - z) / 2 =
        GammaCompactStripScratch.stripPoint ((2 - z.re) / 2) (-z.im / 2) := by
      apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring
    have hgeom2 : (z + 1) / 2 =
        GammaCompactStripScratch.stripPoint ((z.re + 1) / 2) (z.im / 2) := by
      apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint] <;> ring
    rw [← hgeom1] at hnum
    rw [← hgeom2] at hden
    have hnum' : ‖Complex.Gamma ((2 - z) / 2)‖ ≤
        24 * (1 + |z.im / 2|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |z.im / 2|) := by
      simpa only [show |-z.im / 2| = |z.im / 2| by
        rw [show -z.im / 2 = -(z.im / 2) by ring, abs_neg]] using hnum
    calc
      Real.rpow Real.pi (z.re - 1 / 2) *
          ‖Complex.Gamma ((2 - z) / 2)‖ *
          ‖(Complex.Gamma ((z + 1) / 2))⁻¹‖ ≤
        1 * (24 * (1 + |z.im / 2|) ^ 2 *
          Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
          (48 * (1 + |z.im / 2|) ^ 3 *
            Real.exp ((Real.pi / 2) * |z.im / 2|)) := by
          gcongr
      _ ≤ 1152 * (1 + |z.im|) ^ 5 := by
        have hexp : Real.exp (-(Real.pi / 2) * |z.im / 2|) *
            Real.exp ((Real.pi / 2) * |z.im / 2|) = 1 := by
          rw [← Real.exp_add]
          convert Real.exp_zero using 1 <;> ring
        rw [show 1 * (24 * (1 + |z.im / 2|) ^ 2 *
              Real.exp (-(Real.pi / 2) * |z.im / 2|)) *
              (48 * (1 + |z.im / 2|) ^ 3 *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) =
            1152 * (1 + |z.im / 2|) ^ 5 *
              (Real.exp (-(Real.pi / 2) * |z.im / 2|) *
                Real.exp ((Real.pi / 2) * |z.im / 2|)) by ring,
          hexp, mul_one]
        have habs : |z.im / 2| ≤ |z.im| := by
          rw [abs_div]
          norm_num
        have hp : (1 + |z.im / 2|) ^ 5 ≤ (1 + |z.im|) ^ 5 := by gcongr
        exact mul_le_mul_of_nonneg_left hp (by norm_num)

/-- Complete primitive multiplier bound on the recurrence terminal strip. -/
theorem norm_reflectedDualMultiplier_baseStrip_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) {z : ℂ}
    (hzlo : -2 ≤ z.re) (hzhi : z.re ≤ 0) (hzim : 2 ≤ |z.im|) :
    ‖reflectedDualMultiplier chi z‖ ≤
      1152 * Real.rpow (q : ℝ) (5 / 2) * (1 + |z.im|) ^ 5 := by
  have hquot := gammaFactor_quotient_baseStrip_le chi hzlo hzhi hzim
  have hroot : ‖chi.rootNumber‖ = 1 :=
    FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one chi hprim
  have hqnorm : ‖(q : ℂ) ^ ((1 : ℂ) / 2 - z)‖ =
      Real.rpow (q : ℝ) (1 / 2 - z.re) := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    congr 1
    simp
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have hq : Real.rpow (q : ℝ) (1 / 2 - z.re) ≤
      Real.rpow (q : ℝ) (5 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hqone (by linarith)
  unfold reflectedDualMultiplier
  rw [norm_mul, norm_mul, hqnorm, hroot, mul_one]
  calc
    Real.rpow (q : ℝ) (1 / 2 - z.re) *
        ‖chi⁻¹.gammaFactor (1 - z) / chi.gammaFactor z‖ ≤
      Real.rpow (q : ℝ) (5 / 2) *
        (1152 * (1 + |z.im|) ^ 5) := by
      exact mul_le_mul hq hquot (norm_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ = 1152 * Real.rpow (q : ℝ) (5 / 2) *
        (1 + |z.im|) ^ 5 := by ring

end

end JutilaMultiplierBaseStrip

#print axioms JutilaMultiplierBaseStrip.norm_Gamma_half_two_le
#print axioms JutilaMultiplierBaseStrip.norm_inv_Gamma_neg_one_half_le
#print axioms JutilaMultiplierBaseStrip.gammaFactor_quotient_baseStrip_le
#print axioms JutilaMultiplierBaseStrip.norm_reflectedDualMultiplier_baseStrip_le
