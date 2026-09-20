import GoldfeldComparisonArithmetic
import PrincipalZetaFixedStrip
import PrimitiveLFixedStripGrowthCertified

/-!
# Quantitative boundary bounds for the Goldfeld contour

The fixed-strip bounds have total height degree `6 + 3*2 = 12`.
At Riesz order `14`, the raw Mellin kernel has height decay `15`, leaving an
integrable cubic tail on the shifted vertical line and vanishing horizontal
sides.
-/

namespace MAPGoldfeldSiegel

open Set MeasureTheory Complex Filter
open scoped Topology Interval Real
open MAPAppendixA4RieszKernel

noncomputable section

set_option maxHeartbeats 800000

/-- The two independently constructed regularizations of zeta agree. -/
theorem regularizedRiemannZeta_eq_principalRegularized (s : ℂ) :
    regularizedRiemannZeta s =
      MAPPrincipalZetaFixedStrip.principalRegularized s := by
  by_cases hs : s = 1
  · subst s
    simp [MAPPrincipalZetaFixedStrip.principalRegularized,
      DirichletCharacter.LFunctionTrivChar₁]
  · rw [regularizedRiemannZeta_eq_mul hs,
      MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs]

/-- A convenient height norm bound throughout the shifted Goldfeld strip. -/
theorem norm_goldfeld_shift_add_three_le
    {beta sigma t : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2) :
    ‖((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3‖ ≤
      5 * (1 + |t|) := by
  calc
    ‖((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3‖ ≤
        |(((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3).re| +
          |(((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = |beta + sigma + 3| + |t| := by simp
    _ ≤ 5 + |t| := by
      rw [abs_of_nonneg]
      · linarith
      · linarith
    _ ≤ 5 * (1 + |t|) := by
      nlinarith [abs_nonneg t]

/-- Each nonprincipal Dirichlet L-factor has height degree two on the shifted
Goldfeld strip. -/
theorem norm_LFunction_goldfeld_shift_le
    {N : ℕ} [NeZero N] (theta : DirichletCharacter ℂ N) (htheta : theta ≠ 1)
    {beta sigma t : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2) :
    ‖DirichletCharacter.LFunction theta
        ((beta : ℂ) + ((sigma : ℂ) + t * I))‖ ≤
      5000 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by
  have hbase := PLInteriorGrowth.norm_LFunction_fixedStrip_le theta htheta
    (z := (beta : ℂ) + ((sigma : ℂ) + t * I))
    (by simp; linarith) (by simp; linarith)
  have hnorm := norm_goldfeld_shift_add_three_le hbetaLow hbetaHigh
    hsigmaLow hsigmaHigh (t := t)
  calc
    ‖DirichletCharacter.LFunction theta
        ((beta : ℂ) + ((sigma : ℂ) + t * I))‖ ≤
        200 * (N : ℝ) ^ 2 *
          ‖((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3‖ ^ 2 := hbase
    _ ≤ 200 * (N : ℝ) ^ 2 * (5 * (1 + |t|)) ^ 2 := by gcongr
    _ = 5000 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2 := by ring

/-- The regularized zeta factor has height degree six on the same strip. -/
theorem norm_regularizedRiemannZeta_goldfeld_shift_le
    {beta sigma t : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2) :
    ‖regularizedRiemannZeta
        ((beta : ℂ) + ((sigma : ℂ) + t * I))‖ ≤
      (1600 * 5 ^ 6) * (1 + |t|) ^ 6 := by
  rw [regularizedRiemannZeta_eq_principalRegularized]
  have hbase :=
    MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      (z := (beta : ℂ) + ((sigma : ℂ) + t * I))
      (by simp; linarith) (by simp; linarith)
  have hnorm := norm_goldfeld_shift_add_three_le hbetaLow hbetaHigh
    hsigmaLow hsigmaHigh (t := t)
  calc
    ‖MAPPrincipalZetaFixedStrip.principalRegularized
        ((beta : ℂ) + ((sigma : ℂ) + t * I))‖ ≤
        1600 * ‖((beta : ℂ) + ((sigma : ℂ) + t * I)) + 3‖ ^ 6 := hbase
    _ ≤ 1600 * (5 * (1 + |t|)) ^ 6 := by gcongr
    _ = (1600 * 5 ^ 6) * (1 + |t|) ^ 6 := by ring

/-- On the left line the translated zeta pole stays at real distance greater
than `1/2`, so de-regularization costs only a factor two. -/
theorem norm_riemannZeta_goldfeld_left_le
    {beta t : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1) :
    ‖riemannZeta ((beta : ℂ) + ((-1 / 2 : ℝ) + t * I))‖ ≤
      2 * ((1600 * 5 ^ 6) * (1 + |t|) ^ 6) := by
  let s : ℂ := (beta : ℂ) + ((-1 / 2 : ℝ) + t * I)
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s] at hre
    linarith
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hre : |(s - 1).re| ≤ ‖s - 1‖ := Complex.abs_re_le_norm _
    have habs : |(s - 1).re| = 3 / 2 - beta := by
      simp [s]
      rw [abs_of_nonpos] <;> linarith
    rw [habs] at hre
    linarith
  have hreg := norm_regularizedRiemannZeta_goldfeld_shift_le
    hbetaLow hbetaHigh (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 2)
      (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2) (t := t)
  have heq : regularizedRiemannZeta s = (s - 1) * riemannZeta s :=
    regularizedRiemannZeta_eq_mul hs1
  have hnon : 0 ≤ ‖riemannZeta s‖ := norm_nonneg _
  change ‖riemannZeta s‖ ≤ _
  calc
    ‖riemannZeta s‖ ≤ 2 * (‖s - 1‖ * ‖riemannZeta s‖) := by
      nlinarith [mul_nonneg (norm_nonneg (s - 1)) hnon]
    _ = 2 * ‖regularizedRiemannZeta s‖ := by rw [heq, norm_mul]
    _ ≤ 2 * ((1600 * 5 ^ 6) * (1 + |t|) ^ 6) := by
      gcongr

/-- The raw Riesz kernel is uniformly bounded on the shifted left line. -/
theorem norm_rieszMellinKernel_left_le_two_pow (t : ℝ) :
    ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (2 : ℝ) ^ 15 := by
  rw [rieszMellinKernel_eq_div_regularized, norm_div]
  have hreg := norm_regularizedRieszKernel_le_two_pow
    14 (-1 / 2) t (by norm_num)
  have hden : (1 / 2 : ℝ) ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    have hre := Complex.abs_re_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I)
    norm_num at hre ⊢
    exact hre
  calc
    ‖regularizedRieszKernel 14 (((-1 / 2 : ℝ) : ℂ) + t * I)‖ /
        ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        (2 : ℝ) ^ 14 / (1 / 2) :=
      div_le_div₀ (by norm_num) hreg (by norm_num) hden
    _ = (2 : ℝ) ^ 15 := by norm_num

/-- Away from height zero the raw order-14 kernel has degree-15 decay. -/
theorem norm_rieszMellinKernel_left_le_decay {t : ℝ} (ht : t ≠ 0) :
    ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (Nat.factorial 14 : ℝ) / |t| ^ 15 := by
  rw [rieszMellinKernel_eq_div_regularized, norm_div]
  have hreg := norm_regularizedRieszKernel_le 14 (-1 / 2) t ht
  have him : |t| ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    simpa using Complex.abs_im_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I)
  have htpos : 0 < |t| := abs_pos.mpr ht
  calc
    ‖regularizedRieszKernel 14 (((-1 / 2 : ℝ) : ℂ) + t * I)‖ /
        ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        ((Nat.factorial 14 : ℝ) / |t| ^ 14) / |t| :=
      div_le_div₀ (by positivity) hreg htpos him
    _ = (Nat.factorial 14 : ℝ) / |t| ^ 15 := by
      rw [show (15 : ℕ) = 14 + 1 by omega, pow_succ]
      field_simp

/-- The conductor and smoothing scale in the boundary majorants. -/
def goldfeldBoundaryScale (N : ℕ) (X : ℝ) : ℝ :=
  (2 * (1600 * 5 ^ 6)) * (5000 * (N : ℝ) ^ 2) ^ 3 * X ^ (-1 / 2 : ℝ)

theorem goldfeldBoundaryScale_pos
    {N : ℕ} [NeZero N] {X : ℝ} (hX : 0 < X) :
    0 < goldfeldBoundaryScale N X := by
  unfold goldfeldBoundaryScale
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hXp : 0 < X ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  positivity

/-- Before inserting the kernel decay, all four L-factors contribute exactly
height degree twelve. -/
theorem norm_goldfeldRaw_left_le_kernel
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ‖goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      goldfeldBoundaryScale N X *
        ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
          (1 + |t|) ^ 12 := by
  have hz := norm_riemannZeta_goldfeld_left_le hbetaLow hbetaHigh (t := t)
  have hz' : ‖riemannZeta (↑beta + ((-1 / 2 : ℝ) + ↑t * I))‖ ≤
      2 * (1600 * 5 ^ 6) * (1 + |t|) ^ 6 := by
    convert hz using 1 <;> ring
  have hchiL := norm_LFunction_goldfeld_shift_le chi hchi hbetaLow hbetaHigh
    (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 2) (by norm_num) (t := t)
  have hpsiL := norm_LFunction_goldfeld_shift_le psi hpsi hbetaLow hbetaHigh
    (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 2) (by norm_num) (t := t)
  have hmulL := norm_LFunction_goldfeld_shift_le (chi * psi) hmul
    hbetaLow hbetaHigh (by norm_num : (-1 / 2 : ℝ) ≤ -1 / 2)
      (by norm_num) (t := t)
  have hpow : ‖(X : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I)‖ =
      X ^ (-1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    norm_num
  unfold goldfeldRawIntegrand
  simp only [norm_mul, hpow]
  calc
    ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ *
        X ^ (-1 / 2 : ℝ) *
          (‖riemannZeta (↑beta + ((-1 / 2 : ℝ) + ↑t * I))‖ *
            ‖DirichletCharacter.LFunction chi
              (↑beta + ((-1 / 2 : ℝ) + ↑t * I))‖ *
            ‖DirichletCharacter.LFunction psi
              (↑beta + ((-1 / 2 : ℝ) + ↑t * I))‖ *
            ‖DirichletCharacter.LFunction (chi * psi)
              (↑beta + ((-1 / 2 : ℝ) + ↑t * I))‖) ≤
        ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ *
          X ^ (-1 / 2 : ℝ) *
          ((2 * (1600 * 5 ^ 6) * (1 + |t|) ^ 6) *
            (5000 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2) *
            (5000 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2) *
            (5000 * (N : ℝ) ^ 2 * (1 + |t|) ^ 2)) := by
      gcongr
    _ = goldfeldBoundaryScale N X *
        ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ *
          (1 + |t|) ^ 12 := by
      unfold goldfeldBoundaryScale
      ring

/-- A single explicit constant dominating both the compact and tail parts of
the shifted vertical line. -/
def goldfeldBoundaryConstant (N : ℕ) (X : ℝ) : ℝ :=
  goldfeldBoundaryScale N X *
    ((2 : ℝ) ^ 28 + (2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ))

theorem goldfeldBoundaryConstant_nonneg
    {N : ℕ} [NeZero N] {X : ℝ} (hX : 0 < X) :
    0 ≤ goldfeldBoundaryConstant N X := by
  unfold goldfeldBoundaryConstant
  exact mul_nonneg (goldfeldBoundaryScale_pos hX).le (by positivity)

/-- The literal shifted-line integrand is dominated by the standard integrable
majorant `(1+t²)⁻¹`.  This is where order `14` is quantitatively used. -/
theorem norm_goldfeldRaw_left_le_inv_one_add_sq
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) (t : ℝ) :
    ‖goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      goldfeldBoundaryConstant N X * (1 + t ^ 2)⁻¹ := by
  have hraw := norm_goldfeldRaw_left_le_kernel chi psi hchi hpsi hmul
    hbetaLow hbetaHigh hX t
  have hscale0 : 0 ≤ goldfeldBoundaryScale N X :=
    (goldfeldBoundaryScale_pos hX).le
  have hdenpos : 0 < 1 + t ^ 2 := by positivity
  rw [← div_eq_mul_inv, le_div_iff₀ hdenpos]
  by_cases ht : |t| ≤ 1
  · have hk := norm_rieszMellinKernel_left_le_two_pow t
    have hpoly : (1 + |t|) ^ 12 ≤ (2 : ℝ) ^ 12 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith [abs_nonneg t]
    have hden : 1 + t ^ 2 ≤ 2 := by
      have ht2abs := pow_le_pow_left₀ (abs_nonneg t) ht 2
      rw [sq_abs] at ht2abs
      linarith
    calc
      ‖goldfeldRawIntegrand chi psi beta 14 X
          (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ * (1 + t ^ 2) ≤
          (goldfeldBoundaryScale N X *
            ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ *
              (1 + |t|) ^ 12) * (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right hraw hdenpos.le
      _ ≤ (goldfeldBoundaryScale N X * (2 : ℝ) ^ 15 *
            (2 : ℝ) ^ 12) * 2 := by gcongr
      _ ≤ goldfeldBoundaryConstant N X := by
        unfold goldfeldBoundaryConstant
        have hfac : (0 : ℝ) ≤ Nat.factorial 14 := by positivity
        nlinarith
  · have htgt : 1 < |t| := lt_of_not_ge ht
    have htpos : 0 < |t| := lt_trans zero_lt_one htgt
    have ht0 : t ≠ 0 := abs_ne_zero.mp (ne_of_gt htpos)
    have hk := norm_rieszMellinKernel_left_le_decay ht0
    have hpoly : (1 + |t|) ^ 12 ≤ (2 * |t|) ^ 12 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hden : 1 + t ^ 2 ≤ 2 * |t| ^ 2 := by
      have htsq : 1 < t ^ 2 := by
        rw [← sq_abs]
        nlinarith [sq_nonneg (|t| - 1)]
      rw [sq_abs]
      linarith
    calc
      ‖goldfeldRawIntegrand chi psi beta 14 X
          (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ * (1 + t ^ 2) ≤
          (goldfeldBoundaryScale N X *
            ‖rieszMellinKernel 14 (((-1 / 2 : ℝ) : ℂ) + ↑t * I)‖ *
              (1 + |t|) ^ 12) * (1 + t ^ 2) :=
        mul_le_mul_of_nonneg_right hraw hdenpos.le
      _ ≤ (goldfeldBoundaryScale N X *
            ((Nat.factorial 14 : ℝ) / |t| ^ 15) *
              (2 * |t|) ^ 12) * (2 * |t| ^ 2) := by gcongr
      _ = goldfeldBoundaryScale N X *
          ((2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) / |t| := by
        field_simp
      _ ≤ goldfeldBoundaryScale N X *
          ((2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) := by
        apply (div_le_iff₀ htpos).2
        have hnum : 0 ≤ goldfeldBoundaryScale N X *
            ((2 : ℝ) ^ 13 * (Nat.factorial 14 : ℝ)) := by positivity
        nlinarith
      _ ≤ goldfeldBoundaryConstant N X := by
        unfold goldfeldBoundaryConstant
        nlinarith [hscale0]

/-- The pole-subtracted identity supplies continuity of the literal integrand
on the shifted line, including at height zero. -/
theorem continuous_goldfeldRaw_left
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaHigh : beta < 1) {X : ℝ} (hX : 0 < X) :
    Continuous (fun t : ℝ =>
      goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hfun : (fun t : ℝ =>
      goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)) =
      (fun t : ℝ =>
        goldfeldPoleRemainder chi psi beta 14 X
            (((-1 / 2 : ℝ) : ℂ) + t * I) +
          goldfeldPoleResidue chi psi beta 14 X *
            ((((-1 / 2 : ℝ) : ℂ) + t * I) - (1 - beta : ℝ))⁻¹) := by
    funext t
    apply goldfeldRawIntegrand_eq_remainder_add_principal chi psi hzero
    · intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
    · intro hz
      have hre := congrArg Complex.re hz
      simp at hre
      linarith
  rw [hfun]
  apply Continuous.add
  · rw [continuous_iff_continuousAt]
    intro t
    have hrem : ContinuousAt (goldfeldPoleRemainder chi psi beta 14 X)
        (((-1 / 2 : ℝ) : ℂ) + t * I) :=
      (analyticAt_goldfeldPoleRemainder chi psi hchi hpsi hmul
        (by linarith : beta < 2) hX (z := (((-1 / 2 : ℝ) : ℂ) + t * I))
          (by norm_num)).continuousAt
    have hline : ContinuousAt
        (fun u : ℝ => (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) t := by
      fun_prop
    simpa only [Function.comp_def] using
      hrem.comp (f := fun u : ℝ => (((-1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) hline
  · apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro t ht
    have hre := congrArg Complex.re ht
    simp at hre
    linarith

/-- The quantitative left-line integrability hypothesis required by the full
contour passage. -/
theorem integrable_goldfeldRaw_left
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ =>
      goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  refine Integrable.mono'
    (integrable_inv_one_add_sq.const_mul (goldfeldBoundaryConstant N X))
    (continuous_goldfeldRaw_left chi psi hchi hpsi hmul hzero hbetaHigh hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  exact norm_goldfeldRaw_left_le_inv_one_add_sq chi psi hchi hpsi hmul
    hbetaLow hbetaHigh hX t

/-- The smoothing power is uniformly bounded as its real exponent traverses
the compact contour strip. -/
theorem norm_cpow_goldfeld_horizontal_le
    {X sigma B : ℝ} (hX : 0 < X)
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2) :
    ‖(X : ℂ) ^ (((sigma : ℂ) + B * I))‖ ≤
      X ^ (-1 / 2 : ℝ) + X ^ (1 / 2 : ℝ) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, mul_one, sub_zero, add_zero]
  by_cases hXone : 1 ≤ X
  · have h := Real.rpow_le_rpow_of_exponent_le hXone hsigmaHigh
    linarith [Real.rpow_pos_of_pos hX (-1 / 2 : ℝ)]
  · have hXle : X ≤ 1 := le_of_not_ge hXone
    have h := Real.rpow_le_rpow_of_exponent_ge hX hXle hsigmaLow
    linarith [Real.rpow_pos_of_pos hX (1 / 2 : ℝ)]

/-- On a nonzero horizontal side, removing the zeta regularization costs the
inverse height. -/
theorem norm_riemannZeta_goldfeld_horizontal_le
    {beta sigma B : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2)
    (hB : B ≠ 0) :
    ‖riemannZeta ((beta : ℂ) + ((sigma : ℂ) + B * I))‖ ≤
      ((1600 * 5 ^ 6) * (1 + |B|) ^ 6) / |B| := by
  let s : ℂ := (beta : ℂ) + ((sigma : ℂ) + B * I)
  have hBpos : 0 < |B| := abs_pos.mpr hB
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s] at him
    exact hB him
  have hden : |B| ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    simpa [s] using him
  have hreg := norm_regularizedRiemannZeta_goldfeld_shift_le
    hbetaLow hbetaHigh hsigmaLow hsigmaHigh (t := B)
  have heq : regularizedRiemannZeta s = (s - 1) * riemannZeta s :=
    regularizedRiemannZeta_eq_mul hs1
  apply (le_div_iff₀ hBpos).2
  calc
    ‖riemannZeta s‖ * |B| ≤ ‖riemannZeta s‖ * ‖s - 1‖ := by gcongr
    _ = ‖regularizedRiemannZeta s‖ := by rw [heq, norm_mul]; ring
    _ ≤ (1600 * 5 ^ 6) * (1 + |B|) ^ 6 := hreg

/-- The raw order-14 kernel decays as height to the power `-15`, uniformly in
the horizontal coordinate. -/
theorem norm_rieszMellinKernel_horizontal_le_decay
    (sigma : ℝ) {B : ℝ} (hB : B ≠ 0) :
    ‖rieszMellinKernel 14 ((sigma : ℂ) + B * I)‖ ≤
      (Nat.factorial 14 : ℝ) / |B| ^ 15 := by
  rw [rieszMellinKernel_eq_div_regularized, norm_div]
  have hreg := norm_regularizedRieszKernel_le 14 sigma B hB
  have him : |B| ≤ ‖(sigma : ℂ) + B * I‖ := by
    simpa using Complex.abs_im_le_norm ((sigma : ℂ) + B * I)
  have hBpos : 0 < |B| := abs_pos.mpr hB
  calc
    ‖regularizedRieszKernel 14 ((sigma : ℂ) + B * I)‖ /
        ‖(sigma : ℂ) + B * I‖ ≤
        ((Nat.factorial 14 : ℝ) / |B| ^ 14) / |B| :=
      div_le_div₀ (by positivity) hreg hBpos him
    _ = (Nat.factorial 14 : ℝ) / |B| ^ 15 := by
      rw [show (15 : ℕ) = 14 + 1 by omega, pow_succ]
      field_simp

/-- The explicit constant for the horizontal sides. -/
def goldfeldHorizontalScale (N : ℕ) (X : ℝ) : ℝ :=
  (1600 * 5 ^ 6) * (5000 * (N : ℝ) ^ 2) ^ 3 *
    (X ^ (-1 / 2 : ℝ) + X ^ (1 / 2 : ℝ)) *
      (Nat.factorial 14 : ℝ)

theorem goldfeldHorizontalScale_nonneg
    {N : ℕ} [NeZero N] {X : ℝ} (hX : 0 < X) :
    0 ≤ goldfeldHorizontalScale N X := by
  unfold goldfeldHorizontalScale
  have hXm : 0 < X ^ (-1 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  have hXp : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hX _
  positivity

/-- Before elementary power absorption, the horizontal side has denominator
height power sixteen and numerator degree twelve. -/
theorem norm_goldfeldRaw_horizontal_le
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) {sigma B : ℝ}
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2)
    (hB : B ≠ 0) :
    ‖goldfeldRawIntegrand chi psi beta 14 X ((sigma : ℂ) + B * I)‖ ≤
      goldfeldHorizontalScale N X * (1 + |B|) ^ 12 / |B| ^ 16 := by
  have hk := norm_rieszMellinKernel_horizontal_le_decay sigma hB
  have hpow := norm_cpow_goldfeld_horizontal_le hX hsigmaLow hsigmaHigh
    (B := B)
  have hz := norm_riemannZeta_goldfeld_horizontal_le hbetaLow hbetaHigh
    hsigmaLow hsigmaHigh hB
  have hchiL := norm_LFunction_goldfeld_shift_le chi hchi hbetaLow hbetaHigh
    hsigmaLow hsigmaHigh (t := B)
  have hpsiL := norm_LFunction_goldfeld_shift_le psi hpsi hbetaLow hbetaHigh
    hsigmaLow hsigmaHigh (t := B)
  have hmulL := norm_LFunction_goldfeld_shift_le (chi * psi) hmul
    hbetaLow hbetaHigh hsigmaLow hsigmaHigh (t := B)
  unfold goldfeldRawIntegrand
  simp only [norm_mul]
  calc
    ‖rieszMellinKernel 14 (↑sigma + ↑B * I)‖ *
        ‖((X : ℂ) ^ (↑sigma + ↑B * I))‖ *
          (‖riemannZeta (↑beta + (↑sigma + ↑B * I))‖ *
            ‖DirichletCharacter.LFunction chi
              (↑beta + (↑sigma + ↑B * I))‖ *
            ‖DirichletCharacter.LFunction psi
              (↑beta + (↑sigma + ↑B * I))‖ *
            ‖DirichletCharacter.LFunction (chi * psi)
              (↑beta + (↑sigma + ↑B * I))‖) ≤
        ((Nat.factorial 14 : ℝ) / |B| ^ 15) *
          (X ^ (-1 / 2 : ℝ) + X ^ (1 / 2 : ℝ)) *
          ((((1600 * 5 ^ 6) * (1 + |B|) ^ 6) / |B|) *
            (5000 * (N : ℝ) ^ 2 * (1 + |B|) ^ 2) *
            (5000 * (N : ℝ) ^ 2 * (1 + |B|) ^ 2) *
            (5000 * (N : ℝ) ^ 2 * (1 + |B|) ^ 2)) := by
      gcongr
    _ = goldfeldHorizontalScale N X * (1 + |B|) ^ 12 / |B| ^ 16 := by
      unfold goldfeldHorizontalScale
      have hBabs : |B| ≠ 0 := ne_of_gt (abs_pos.mpr hB)
      field_simp

/-- The four powers of spare decay are reduced to the simple inverse-height
majorant used for the limit. -/
theorem norm_goldfeldRaw_horizontal_le_inv_height
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) {sigma B : ℝ}
    (hsigmaLow : -1 / 2 ≤ sigma) (hsigmaHigh : sigma ≤ 1 / 2)
    (hB : 1 ≤ |B|) :
    ‖goldfeldRawIntegrand chi psi beta 14 X ((sigma : ℂ) + B * I)‖ ≤
      (goldfeldHorizontalScale N X * (2 : ℝ) ^ 12) / |B| := by
  have hBpos : 0 < |B| := lt_of_lt_of_le zero_lt_one hB
  have hraw := norm_goldfeldRaw_horizontal_le chi psi hchi hpsi hmul
    hbetaLow hbetaHigh hX hsigmaLow hsigmaHigh (abs_ne_zero.mp hBpos.ne')
  have hpoly : (1 + |B|) ^ 12 ≤ (2 * |B|) ^ 12 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have hscale0 := goldfeldHorizontalScale_nonneg (N := N) hX
  calc
    ‖goldfeldRawIntegrand chi psi beta 14 X (↑sigma + ↑B * I)‖ ≤
        goldfeldHorizontalScale N X * (1 + |B|) ^ 12 / |B| ^ 16 := hraw
    _ ≤ goldfeldHorizontalScale N X * (2 * |B|) ^ 12 / |B| ^ 16 := by
      gcongr
    _ = (goldfeldHorizontalScale N X * (2 : ℝ) ^ 12) / |B| ^ 4 := by
      field_simp
    _ ≤ (goldfeldHorizontalScale N X * (2 : ℝ) ^ 12) / |B| := by
      apply div_le_div_of_nonneg_left (by positivity) hBpos
      simpa only [pow_one] using
        (pow_le_pow_right₀ hB (show (1 : ℕ) ≤ 4 by norm_num))

/-- Uniform norm bound for either oriented horizontal interval. -/
theorem norm_goldfeld_horizontal_interval_le_inv_height
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) {B : ℝ} (hB : 1 ≤ |B|) :
    ‖∫ x : ℝ in (-1 / 2)..(1 / 2),
        goldfeldRawIntegrand chi psi beta 14 X ((x : ℂ) + B * I)‖ ≤
      (goldfeldHorizontalScale N X * (2 : ℝ) ^ 12) / |B| := by
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (C := (goldfeldHorizontalScale N X * (2 : ℝ) ^ 12) / |B|)
    (f := fun x : ℝ =>
      goldfeldRawIntegrand chi psi beta 14 X ((x : ℂ) + B * I))
    (fun x hx => by
      have hx' : x ∈ Set.Icc (-1 / 2 : ℝ) (1 / 2 : ℝ) := by
        have hxu : x ∈ Set.uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ) :=
          Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at hxu
        exact hxu
      exact norm_goldfeldRaw_horizontal_le_inv_height chi psi hchi hpsi hmul
        hbetaLow hbetaHigh hX hx'.1 hx'.2 hB)
  norm_num at hbound ⊢
  exact hbound

/-- The upper horizontal side vanishes as its height tends to infinity. -/
theorem tendsto_goldfeld_horizontal_plus
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (-1 / 2)..(1 / 2),
        goldfeldRawIntegrand chi psi beta 14 X (x + B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := goldfeldHorizontalScale N X * (2 : ℝ) ^ 12
  have hlim : Tendsto (fun B : ℝ => C * B⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝 0))
  refine squeeze_zero' (Eventually.of_forall fun B => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hbound := norm_goldfeld_horizontal_interval_le_inv_height
    chi psi hchi hpsi hmul hbetaLow hbetaHigh hX
      (B := B) (by simpa [abs_of_nonneg hB0] using hB)
  simpa [C, abs_of_nonneg hB0, div_eq_mul_inv] using hbound

/-- The lower horizontal side vanishes as its height tends to infinity. -/
theorem tendsto_goldfeld_horizontal_minus
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (-1 / 2)..(1 / 2),
        goldfeldRawIntegrand chi psi beta 14 X (x - B * I))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let C : ℝ := goldfeldHorizontalScale N X * (2 : ℝ) ^ 12
  have hlim : Tendsto (fun B : ℝ => C * B⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_inv_atTop_zero : Tendsto (fun B : ℝ => B⁻¹) atTop (𝓝 0))
  refine squeeze_zero' (Eventually.of_forall fun B => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with B hB
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hbound := norm_goldfeld_horizontal_interval_le_inv_height
    chi psi hchi hpsi hmul hbetaLow hbetaHigh hX
      (B := -B) (by simpa [abs_of_nonneg hB0] using hB)
  have heq : (fun x : ℝ =>
      goldfeldRawIntegrand chi psi beta 14 X (x - B * I)) =
      (fun x : ℝ =>
        goldfeldRawIntegrand chi psi beta 14 X (x + (-B) * I)) := by
    funext x
    congr 1
    push_cast
    ring
  rw [heq]
  simpa [C, abs_of_nonneg hB0, div_eq_mul_inv] using hbound

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.regularizedRiemannZeta_eq_principalRegularized
#print axioms MAPGoldfeldSiegel.norm_goldfeld_shift_add_three_le
