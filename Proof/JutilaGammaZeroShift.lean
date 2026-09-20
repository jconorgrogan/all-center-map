import JutilaHybridConvexityPrimitiveBoundary
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Exact zero-shift Gamma-ratio boundary for Jutila’s detector

Jutila’s Lemma 6 evaluates the functional-equation boundary on `Re s = 0`.
At this exact line Euler reflection gives parity-specific Gamma-ratio bounds
without a complex Stirling theorem.  This module proves the literal
`GammaRatioBoundAtShift 0 1` predicate.
-/

namespace MAPJutilaGammaZeroShift

open Complex DirichletCharacter
open MAPJutilaHybridConvexityPrimitiveBoundary

noncomputable section

theorem abs_sinh_le_cosh (x : ℝ) : |Real.sinh x| ≤ Real.cosh x := by
  rw [← sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos x).le]
  rw [sq_abs, Real.sinh_sq]
  linarith

private theorem conj_half_add_I (x : ℝ) :
    starRingEnd ℂ ((1 / 2 : ℂ) + (x : ℂ) * I) =
      (1 / 2 : ℂ) - (x : ℂ) * I := by
  apply Complex.ext <;> simp

private theorem one_sub_half_add_I (x : ℝ) :
    1 - ((1 / 2 : ℂ) + (x : ℂ) * I) =
      (1 / 2 : ℂ) - (x : ℂ) * I := by ring

private theorem conj_I (x : ℝ) :
    starRingEnd ℂ ((x : ℂ) * I) = -((x : ℂ) * I) := by simp

private theorem norm_Gamma_half_pair_sq (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ ^ 2 =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) *
        ((1 / 2 : ℂ) + (x : ℂ) * I))‖ := by
  let z : ℂ := (1 / 2 : ℂ) + (x : ℂ) * I
  have href := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  have hconj : 1 - z = starRingEnd ℂ z := by
    dsimp [z]
    rw [conj_half_add_I, one_sub_half_add_I]
  rw [hconj, Complex.Gamma_conj, norm_mul, RCLike.norm_conj,
    norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at href
  have hzconj : ‖Complex.Gamma z‖ =
      ‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ := by
    rw [← conj_half_add_I x, Complex.Gamma_conj, RCLike.norm_conj]
  rw [hzconj, ← pow_two] at href
  exact href

private theorem norm_Gamma_I_sq_mul_abs (x : ℝ) (hx : x ≠ 0) :
    ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 * |x| =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * ((x : ℂ) * I))‖ := by
  let z : ℂ := (x : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [z] at him
    exact hx him
  have href := congrArg norm (Complex.Gamma_mul_Gamma_one_sub z)
  have hrec : Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    rw [show 1 - z = (-z) + 1 by ring, Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)]
  have hminus : ‖Complex.Gamma (-z)‖ = ‖Complex.Gamma z‖ := by
    have hc : -z = starRingEnd ℂ z := by
      dsimp [z]
      rw [conj_I]
    rw [hc, Complex.Gamma_conj, RCLike.norm_conj]
  rw [hrec, norm_mul, norm_mul, norm_neg, hminus, norm_div,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at href
  have hnormz : ‖z‖ = |x| := by
    dsimp [z]
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormz] at href
  nlinarith [norm_nonneg (Complex.Gamma z), abs_nonneg x]

private theorem norm_sin_I_eq (x : ℝ) :
    ‖Complex.sin ((x : ℂ) * I)‖ = |Real.sinh x| := by
  rw [Complex.sin_mul_I]
  have hsinh : Complex.sinh (x : ℂ) = (Real.sinh x : ℂ) :=
    (Complex.ofReal_sinh x).symm
  rw [hsinh, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

private theorem norm_sin_half_add_I_eq (x : ℝ) :
    ‖Complex.sin ((Real.pi / 2 : ℝ) + (x : ℂ) * I)‖ = Real.cosh x := by
  push_cast
  rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
    one_mul, zero_mul, add_zero, Complex.cos_mul_I]
  have hcosh : Complex.cosh (x : ℂ) = (Real.cosh x : ℂ) :=
    (Complex.ofReal_cosh x).symm
  rw [hcosh, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos x)]

private theorem gamma_half_sq_le_abs_mul_gamma_I_sq (x : ℝ) (hx : x ≠ 0) :
    ‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ ^ 2 ≤
      |x| * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 := by
  have hA := norm_Gamma_half_pair_sq x
  have hB := norm_Gamma_I_sq_mul_abs x hx
  have hargI : (Real.pi : ℂ) * ((x : ℂ) * I) =
      ((Real.pi * x : ℝ) : ℂ) * I := by push_cast; ring
  have hargHalf : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * I) =
      ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hargI, norm_sin_I_eq] at hB
  rw [hargHalf, norm_sin_half_add_I_eq] at hA
  have hsinhPos : 0 < |Real.sinh (Real.pi * x)| := abs_pos.mpr <| by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero hx
  have hcoshPos : 0 < Real.cosh (Real.pi * x) := Real.cosh_pos _
  have hsine := abs_sinh_le_cosh (Real.pi * x)
  have hdiv : Real.pi / Real.cosh (Real.pi * x) ≤
      Real.pi / |Real.sinh (Real.pi * x)| := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le hsinhPos hsine
  rw [hA, mul_comm |x|, hB]
  exact hdiv

private theorem even_gammaR_zero_shift_sq_le (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I) /
        Complex.Gammaℝ ((t : ℂ) * I)‖ ^ 2 ≤ |t| / (2 * Real.pi) := by
  let x : ℝ := t / 2
  have hx : x ≠ 0 := div_ne_zero ht (by norm_num)
  have hgamma := gamma_half_sq_le_abs_mul_gamma_I_sq x hx
  have hdenGamma : ‖Complex.Gamma ((x : ℂ) * I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    simp at him
    exact hx him
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_div, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpi,
    Complex.norm_cpow_eq_rpow_re_of_pos hpi]
  have hnumarg : (((1 : ℂ) - (t : ℂ) * I) / 2) =
      (1 / 2 : ℂ) - (x : ℂ) * I := by
    dsimp [x]
    push_cast
    ring
  have hdenarg : (((t : ℂ) * I) / 2) = (x : ℂ) * I := by
    dsimp [x]
    push_cast
    ring
  rw [hnumarg, hdenarg]
  have hnumre : (-((1 : ℂ) - (t : ℂ) * I) / 2).re = (-1 / 2 : ℝ) := by simp
  have hdenre : (-((t : ℂ) * I) / 2).re = 0 := by simp
  rw [hnumre, hdenre, Real.rpow_zero, one_mul]
  have hpiRpowSq : (Real.rpow Real.pi (-1 / 2)) ^ (2 : ℕ) = Real.pi⁻¹ := by
    rw [← Real.rpow_natCast]
    calc
      Real.rpow (Real.rpow Real.pi (-1 / 2)) (2 : ℝ) =
          Real.rpow Real.pi ((-1 / 2) * (2 : ℝ)) :=
        (Real.rpow_mul hpi.le _ _).symm
      _ = Real.rpow Real.pi (-1) := by norm_num
      _ = Real.pi⁻¹ := Real.rpow_neg_one _
  change (Real.rpow Real.pi (-1 / 2) *
      ‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ /
      ‖Complex.Gamma ((x : ℂ) * I)‖) ^ (2 : ℕ) ≤ _
  rw [div_pow, mul_pow, hpiRpowSq]
  rw [div_eq_mul_inv]
  have hdenSqPos : 0 < ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 := sq_pos_of_ne_zero hdenGamma
  rw [div_eq_mul_inv] at hgamma ⊢
  have htAbs : |t| = 2 * |x| := by
    dsimp [x]
    rw [abs_div]
    norm_num
    ring
  rw [htAbs]
  have hpiNe : Real.pi ≠ 0 := Real.pi_ne_zero
  calc
    Real.pi⁻¹ *
          (‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ ^ 2) *
          (‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2)⁻¹ ≤
        Real.pi⁻¹ *
          (|x| * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2) *
          (‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2)⁻¹ := by
      gcongr
      convert hgamma using 1
    _ = (2 * |x|) * (2 * Real.pi)⁻¹ := by
      field_simp

private theorem cosh_le_sinh_add_one {y : ℝ} (hy : 0 ≤ y) :
    Real.cosh y ≤ Real.sinh y + 1 := by
  have he : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hy)
  have hn : -(y : ℂ) = ((-y : ℝ) : ℂ) := by
    exact (map_neg Complex.ofRealHom y).symm
  have hexpNeg : (Complex.exp (-(y : ℂ))).re = Real.exp (-y) := by
    rw [hn, Complex.exp_ofReal_re]
  have hcosh : Real.cosh y = (Real.exp y + Real.exp (-y)) / 2 := by
    rw [Real.cosh, Complex.cosh]
    norm_num [Complex.exp_ofReal_re, hexpNeg]
  have hsinh : Real.sinh y = (Real.exp y - Real.exp (-y)) / 2 := by
    rw [Real.sinh, Complex.sinh]
    norm_num [Complex.exp_ofReal_re, hexpNeg]
  rw [hcosh, hsinh]
  linarith

private theorem abs_mul_cosh_le_add_mul_abs_sinh (x : ℝ) :
    |x| * Real.cosh (Real.pi * x) ≤
      (|x| + 1) * |Real.sinh (Real.pi * x)| := by
  let y := Real.pi * |x|
  have hy : 0 ≤ y := mul_nonneg Real.pi_pos.le (abs_nonneg x)
  have hsinhLower : y ≤ Real.sinh y :=
    (Real.self_le_sinh_iff).mpr hy
  have hcosh := cosh_le_sinh_add_one hy
  have hcoshAbs : Real.cosh (Real.pi * x) = Real.cosh y := by
    dsimp [y]
    rw [← Real.cosh_abs]
    congr 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hsinhAbs : |Real.sinh (Real.pi * x)| = Real.sinh y := by
    rw [Real.abs_sinh]
    dsimp [y]
    congr 1
    rw [abs_mul, abs_of_pos Real.pi_pos]
  rw [hcoshAbs, hsinhAbs]
  have hxa : |x| ≤ Real.sinh y := by
    calc |x| ≤ Real.pi * |x| := by
          nlinarith [Real.pi_gt_three, abs_nonneg x]
      _ = y := rfl
      _ ≤ Real.sinh y := hsinhLower
  nlinarith [abs_nonneg x, (Real.sinh_nonneg_iff.mpr hy)]

private theorem gamma_one_I_sq (x : ℝ) (hx : x ≠ 0) :
    ‖Complex.Gamma ((1 : ℂ) - (x : ℂ) * I)‖ ^ 2 =
      x ^ 2 * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 := by
  let z : ℂ := (x : ℂ) * I
  have hz : z ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp [z] at him
    exact hx him
  have hrec : Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    rw [show 1 - z = (-z) + 1 by ring,
      Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hz)]
  have hminus : ‖Complex.Gamma (-z)‖ = ‖Complex.Gamma z‖ := by
    have hc : -z = starRingEnd ℂ z := by
      dsimp [z]
      simp
    rw [hc, Complex.Gamma_conj, RCLike.norm_conj]
  rw [show (1 : ℂ) - (x : ℂ) * I = 1 - z by rfl, hrec, norm_mul,
    norm_neg, hminus, mul_pow]
  have hnormz : ‖z‖ = |x| := by
    dsimp [z]
    rw [norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hnormz, sq_abs]

private theorem odd_gammaR_zero_shift_sq_le (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gammaℝ ((2 : ℂ) - (t : ℂ) * I) /
        Complex.Gammaℝ ((1 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤ 1 + |t| := by
  let x : ℝ := t / 2
  have hx : x ≠ 0 := div_ne_zero ht (by norm_num)
  have hA := norm_Gamma_half_pair_sq x
  have hB := norm_Gamma_I_sq_mul_abs x hx
  have hOne := gamma_one_I_sq x hx
  have hdenGamma : ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    apply Complex.Gamma_ne_zero
    intro n hn
    have hre := congrArg Complex.re hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    norm_num at hre
    linarith
  have hargI : (Real.pi : ℂ) * ((x : ℂ) * I) =
      ((Real.pi * x : ℝ) : ℂ) * I := by push_cast; ring
  have hargHalf : (Real.pi : ℂ) * ((1 / 2 : ℂ) + (x : ℂ) * I) =
      ((Real.pi / 2 : ℝ) : ℂ) + ((Real.pi * x : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [hargI, norm_sin_I_eq] at hB
  rw [hargHalf, norm_sin_half_add_I_eq] at hA
  have hsinhPos : 0 < |Real.sinh (Real.pi * x)| := abs_pos.mpr <| by
    rw [Real.sinh_ne_zero]
    exact mul_ne_zero Real.pi_ne_zero hx
  have hcoshPos : 0 < Real.cosh (Real.pi * x) := Real.cosh_pos _
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_div, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hpi,
    Complex.norm_cpow_eq_rpow_re_of_pos hpi]
  have hnumarg : (((2 : ℂ) - (t : ℂ) * I) / 2) =
      (1 : ℂ) - (x : ℂ) * I := by
    dsimp [x]
    push_cast
    ring
  have hdenarg : (((1 : ℂ) + (t : ℂ) * I) / 2) =
      (1 / 2 : ℂ) + (x : ℂ) * I := by
    dsimp [x]
    push_cast
    ring
  rw [hnumarg, hdenarg]
  have hnumre : (-((2 : ℂ) - (t : ℂ) * I) / 2).re = (-1 : ℝ) := by simp
  have hdenre : (-((1 : ℂ) + (t : ℂ) * I) / 2).re = (-1 / 2 : ℝ) := by simp
  rw [hnumre, hdenre]
  have hpiRpowRatioSq :
      (Real.rpow Real.pi (-1) / Real.rpow Real.pi (-1 / 2)) ^ (2 : ℕ) =
        Real.pi⁻¹ := by
    have hhalfSq : (Real.rpow Real.pi (-1 / 2)) ^ (2 : ℕ) = Real.pi⁻¹ := by
      rw [← Real.rpow_natCast]
      calc
        Real.rpow (Real.rpow Real.pi (-1 / 2)) (2 : ℝ) =
            Real.rpow Real.pi ((-1 / 2) * (2 : ℝ)) :=
          (Real.rpow_mul hpi.le _ _).symm
        _ = Real.rpow Real.pi (-1) := by norm_num
        _ = Real.pi⁻¹ := Real.rpow_neg_one _
    have hminusOne : Real.rpow Real.pi (-1) = Real.pi⁻¹ :=
      Real.rpow_neg_one _
    rw [div_pow, hminusOne, hhalfSq]
    field_simp
  change (Real.rpow Real.pi (-1) *
      ‖Complex.Gamma ((1 : ℂ) - (x : ℂ) * I)‖ /
      (Real.rpow Real.pi (-1 / 2) *
        ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖)) ^ (2 : ℕ) ≤ _
  rw [show Real.rpow Real.pi (-1) *
      ‖Complex.Gamma ((1 : ℂ) - (x : ℂ) * I)‖ /
      (Real.rpow Real.pi (-1 / 2) *
        ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖) =
      (Real.rpow Real.pi (-1) /
       Real.rpow Real.pi (-1 / 2)) *
      (‖Complex.Gamma ((1 : ℂ) - (x : ℂ) * I)‖ /
       ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖) by ring]
  rw [mul_pow, hpiRpowRatioSq, div_pow, hOne]
  rw [div_eq_mul_inv]
  have hdenSqPos : 0 < ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ ^ 2 :=
    sq_pos_of_ne_zero hdenGamma
  have hAplus : ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by
    have hc : ‖Complex.Gamma ((1 / 2 : ℂ) + (x : ℂ) * I)‖ =
        ‖Complex.Gamma ((1 / 2 : ℂ) - (x : ℂ) * I)‖ := by
      rw [← conj_half_add_I x, Complex.Gamma_conj, RCLike.norm_conj]
    rw [hc]
    exact hA
  have hB' : |x| * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 =
      Real.pi / |Real.sinh (Real.pi * x)| := by
    rw [mul_comm]
    exact hB
  have htAbs : |t| = 2 * |x| := by
    dsimp [x]
    rw [abs_div]
    norm_num
    ring
  rw [htAbs]
  have hhyper := abs_mul_cosh_le_add_mul_abs_sinh x
  rw [hAplus]
  rw [div_eq_mul_inv] at hB'
  have hBcross : |x| * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2 *
      |Real.sinh (Real.pi * x)| = Real.pi := by
    rw [hB']
    field_simp
  have hidentity :
      Real.pi⁻¹ * ((x ^ 2 * ‖Complex.Gamma ((x : ℂ) * I)‖ ^ 2) *
          (Real.pi / Real.cosh (Real.pi * x))⁻¹) =
        Real.pi⁻¹ *
          (|x| * Real.cosh (Real.pi * x) /
            |Real.sinh (Real.pi * x)|) := by
    have hx2 : x ^ 2 = |x| * |x| := by rw [← sq_abs, pow_two]
    rw [hx2]
    field_simp
    nlinarith [hBcross]
  rw [hidentity]
  have hpiInv : Real.pi⁻¹ ≤ 1 := by
    rw [inv_le_one₀ Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hratio : |x| * Real.cosh (Real.pi * x) /
      |Real.sinh (Real.pi * x)| ≤ |x| + 1 := by
    rw [div_le_iff₀ hsinhPos]
    exact hhyper
  calc
    Real.pi⁻¹ * (|x| * Real.cosh (Real.pi * x) /
        |Real.sinh (Real.pi * x)|) ≤
      1 * (|x| + 1) := by gcongr
    _ ≤ 1 + 2 * |x| := by nlinarith [abs_nonneg x]

private theorem inv_even {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi.Even) : chi⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hchi

private theorem inv_odd {q : ℕ} [NeZero q]
    {chi : DirichletCharacter ℂ q} (hchi : chi.Odd) : chi⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hchi

private theorem norm_le_rpow_half_of_sq_le {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ^ 2 ≤ b) :
    a ≤ Real.rpow b (1 / 2) := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
    _ = Real.rpow b (1 / 2) := Real.sqrt_eq_rpow b

private theorem even_gammaR_zero_shift_le (t : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I) /
        Complex.Gammaℝ ((t : ℂ) * I)‖ ≤
      Real.rpow (1 + |t|) (1 / 2) := by
  by_cases ht : t = 0
  · subst t
    simp [Complex.Gammaℝ_def]
  · apply norm_le_rpow_half_of_sq_le (norm_nonneg _)
    calc
      ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * I) /
          Complex.Gammaℝ ((t : ℂ) * I)‖ ^ 2 ≤
        |t| / (2 * Real.pi) := even_gammaR_zero_shift_sq_le t ht
      _ ≤ 1 + |t| := by
        have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
        have ht0 : 0 ≤ |t| := abs_nonneg t
        calc
          |t| / (2 * Real.pi) ≤ |t| := div_le_self ht0 hden
          _ ≤ 1 + |t| := by linarith

private theorem odd_gammaR_zero_shift_le (t : ℝ) :
    ‖Complex.Gammaℝ ((2 : ℂ) - (t : ℂ) * I) /
        Complex.Gammaℝ ((1 : ℂ) + (t : ℂ) * I)‖ ≤
      Real.rpow (1 + |t|) (1 / 2) := by
  by_cases ht : t = 0
  · subst t
    have hG2 : Complex.Gammaℝ (2 : ℂ) = (Real.pi : ℂ)⁻¹ := by
      rw [Complex.Gammaℝ_def]
      norm_num [Complex.Gamma_one, Complex.cpow_neg_one]
    norm_num only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero, abs_zero,
      add_zero, one_div, Real.rpow_one]
    rw [hG2, Complex.Gammaℝ_one, div_one, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    norm_num
    exact inv_le_one₀ Real.pi_pos |>.2 (by linarith [Real.pi_gt_three])
  · apply norm_le_rpow_half_of_sq_le (norm_nonneg _)
    exact odd_gammaR_zero_shift_sq_le t ht

/-- Exact zero-shift archimedean boundary needed by Jutila's Lemma 6. -/
theorem gammaRatioBoundAtShift_zero {q : ℕ} [NeZero q] :
    GammaRatioBoundAtShift (q := q) 0 1 := by
  refine ⟨by norm_num, ?_⟩
  intro chi t
  have hright : rightPoint 0 t = (1 : ℂ) - (t : ℂ) * I := by
    simp [rightPoint]
  rcases chi.even_or_odd with hchi | hchi
  · have hinv := inv_even hchi
    rw [hinv.gammaFactor_def, hchi.gammaFactor_def, hright]
    rw [show 1 - ((1 : ℂ) - (t : ℂ) * I) = (t : ℂ) * I by ring]
    simpa using even_gammaR_zero_shift_le t
  · have hinv := inv_odd hchi
    rw [hinv.gammaFactor_def, hchi.gammaFactor_def, hright]
    rw [show (1 : ℂ) - (t : ℂ) * I + 1 =
        (2 : ℂ) - (t : ℂ) * I by ring,
      show 1 - ((1 : ℂ) - (t : ℂ) * I) + 1 =
        (1 : ℂ) + (t : ℂ) * I by ring]
    simpa using odd_gammaR_zero_shift_le t


/-- Functional-equation reduction on the exact line used in Jutila's Lemma 6.
The only remaining analytic input is a bound for the nonprincipal L-function
on `Re s = 1`; no shifted Gamma ratio or complex Stirling estimate remains. -/
theorem norm_LFunction_imaginary_le_of_rightEdge
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (t B : ℝ)
    (hB0 : 0 ≤ B)
    (hRight : ‖DirichletCharacter.LFunction chi⁻¹
        ((1 : ℂ) - (t : ℂ) * I)‖ ≤ B) :
    ‖DirichletCharacter.LFunction chi ((t : ℂ) * I)‖ ≤
      B * Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |t|) (1 / 2) := by
  let u : ℂ := (1 : ℂ) - (t : ℂ) * I
  have huRe : 0 < u.re := by simp [u]
  have hreflect : 1 - u = (t : ℂ) * I := by
    dsimp [u]
    ring
  have hfe :=
    MAPHuxleyPrimitiveFunctionalEquation.LFunction_one_sub_eq_huxleyFactor
      hprim hchi (s := u) huRe
  have hqnorm : ‖(q : ℂ) ^ (u - 1 / 2)‖ =
      Real.rpow (q : ℝ) (1 / 2) := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    congr 1
    simp [u]
    ring
  have hroot : ‖chi.rootNumber‖ = 1 :=
    FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one chi hprim
  have hgamma := (gammaRatioBoundAtShift_zero (q := q)).2 chi t
  have huRight : u = (1 : ℂ) - (t : ℂ) * I := rfl
  rw [← hreflect, hfe]
  rw [show (q : ℂ) ^ (u - 1 / 2) * chi.rootNumber *
        DirichletCharacter.LFunction chi⁻¹ u *
          chi⁻¹.gammaFactor u / chi.gammaFactor (1 - u) =
      (((q : ℂ) ^ (u - 1 / 2) * chi.rootNumber) *
        DirichletCharacter.LFunction chi⁻¹ u) *
          (chi⁻¹.gammaFactor u / chi.gammaFactor (1 - u)) by ring]
  rw [norm_mul, norm_mul, norm_mul, hqnorm, hroot, mul_one]
  have hq0 : 0 ≤ Real.rpow (q : ℝ) (1 / 2) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hheight0 : 0 ≤ Real.rpow (1 + |t|) (1 / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hL : ‖DirichletCharacter.LFunction chi⁻¹ u‖ ≤ B := by
    simpa [u] using hRight
  have hG : ‖chi⁻¹.gammaFactor u / chi.gammaFactor (1 - u)‖ ≤
      Real.rpow (1 + |t|) (1 / 2) := by
    simpa [u, MAPJutilaHybridConvexityPrimitiveBoundary.rightPoint] using hgamma
  calc
    Real.rpow (q : ℝ) (1 / 2) *
          ‖DirichletCharacter.LFunction chi⁻¹ u‖ *
        ‖chi⁻¹.gammaFactor u / chi.gammaFactor (1 - u)‖ ≤
      Real.rpow (q : ℝ) (1 / 2) * B *
        Real.rpow (1 + |t|) (1 / 2) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hL hq0) hG (norm_nonneg _)
        (mul_nonneg hq0 hB0)
    _ = B * Real.rpow (q : ℝ) (1 / 2) *
        Real.rpow (1 + |t|) (1 / 2) := by ring

end

end MAPJutilaGammaZeroShift

#print axioms MAPJutilaGammaZeroShift.gammaRatioBoundAtShift_zero
#print axioms MAPJutilaGammaZeroShift.norm_LFunction_imaginary_le_of_rightEdge
