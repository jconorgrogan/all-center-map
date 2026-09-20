import BHPEquation336PolylogKernel
import PerronKernel

/-!
# The corrected positive-offset Perron kernel below BHP (3.36)

The right Perron integral in Baker--Harman--Pintz Lemma 9 contains `1 / w`.
Moving it literally to `Re w = 0` makes the new vertical integrand singular at
`w = 0`; the displayed definition of `J` then drops this factor.  A rigorous
repair is to stop at `Re w = delta > 0`.  This file certifies the exact kernel
cost of that repair.  It does not assume a contour identity or an L-function
estimate.

The key output is `norm_shiftedLeftLineIntegral_le`: the retained `1 / w`
costs precisely `1 + delta⁻¹`, and the left line is
`Re s = 1/2 + delta`.  Thus `delta = 1 / log x` costs one fixed logarithm,
but also exposes the shifted-line fourth-moment transfer that the printed
argument suppresses.
-/

namespace MAPBHPCorrectedPerronKernel

open scoped BigOperators
open MAPMRTCorollary25Minkowski

noncomputable section

/-- Norm of the Dirichlet L-function on the honest positive-offset line. -/
def shiftedCriticalLineLNorm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (delta t : ℝ) : ℝ :=
  ‖DirichletCharacter.LFunction chi
    ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) + t * Complex.I)‖

/-- The retained Perron integrand on `Re w = delta`. -/
def shiftedLeftLineIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X delta t u : ℝ) : ℂ :=
  DirichletCharacter.LFunction chi
      ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) + (t + u) * Complex.I) *
    PerronKernel.verticalPower X delta u /
      ((delta : ℂ) + Complex.I * u)

/-- Normalized vertical integral after stopping the contour at
`Re w = delta > 0`. -/
def shiftedLeftLineIntegral {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (X delta T t : ℝ) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
    ∫ u in (-T)..T, shiftedLeftLineIntegrand chi X delta t u

/-- The exact elementary majorant for the retained factor `1 / w`.
It is the quantitative reason that a positive offset costs one logarithm. -/
theorem norm_inv_delta_add_I_mul_le_perronWeight
    {delta u : ℝ} (hdelta : 0 < delta) :
    ‖(((delta : ℂ) + Complex.I * u)⁻¹)‖ ≤
      (1 + delta⁻¹) * perronWeight u := by
  have hdenpos : 0 < ‖(delta : ℂ) + Complex.I * u‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hdeltaDen : delta ≤ ‖(delta : ℂ) + Complex.I * u‖ := by
    calc
      delta = |(((delta : ℂ) + Complex.I * u).re)| := by
        simp [abs_of_pos hdelta]
      _ ≤ ‖(delta : ℂ) + Complex.I * u‖ := Complex.abs_re_le_norm _
  have huDen : |u| ≤ ‖(delta : ℂ) + Complex.I * u‖ := by
    calc
      |u| = |(((delta : ℂ) + Complex.I * u).im)| := by simp
      _ ≤ ‖(delta : ℂ) + Complex.I * u‖ := Complex.abs_im_le_norm _
  have hone : 1 ≤ delta⁻¹ * ‖(delta : ℂ) + Complex.I * u‖ := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hdelta).2 (by simpa using hdeltaDen)
  have hsum : 1 + |u| ≤
      (1 + delta⁻¹) * ‖(delta : ℂ) + Complex.I * u‖ := by
    nlinarith
  have hweightDen : 0 < 1 + |u| := by positivity
  calc
    ‖(((delta : ℂ) + Complex.I * u)⁻¹)‖ =
        1 / ‖(delta : ℂ) + Complex.I * u‖ := by
          rw [norm_inv, one_div]
    _ ≤ (1 + delta⁻¹) / (1 + |u|) := by
      exact (div_le_div_iff₀ hdenpos hweightDen).2 (by simpa using hsum)
    _ = (1 + delta⁻¹) * perronWeight u := by
      unfold perronWeight
      ring

/-- Pointwise norm bound for the corrected integrand. -/
theorem norm_shiftedLeftLineIntegrand_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X delta t u : ℝ} (hX : 0 < X) (hdelta : 0 < delta) :
    ‖shiftedLeftLineIntegrand chi X delta t u‖ ≤
      X ^ delta * (1 + delta⁻¹) *
        (perronWeight u * shiftedCriticalLineLNorm chi delta (t + u)) := by
  rw [shiftedLeftLineIntegrand, norm_div, norm_mul,
    PerronKernel.norm_verticalPower hX]
  have hk := norm_inv_delta_add_I_mul_le_perronWeight
    (u := u) hdelta
  rw [norm_inv] at hk
  have hL0 : 0 ≤ shiftedCriticalLineLNorm chi delta (t + u) := norm_nonneg _
  have hpow0 : 0 ≤ X ^ delta := Real.rpow_nonneg hX.le _
  have hLrewrite :
      ‖DirichletCharacter.LFunction chi
          ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
            ((t : ℂ) + (u : ℂ)) * Complex.I)‖ =
        shiftedCriticalLineLNorm chi delta (t + u) := by
    unfold shiftedCriticalLineLNorm
    congr 3
    push_cast
    rfl
  rw [hLrewrite]
  change shiftedCriticalLineLNorm chi delta (t + u) * X ^ delta /
      ‖(delta : ℂ) + Complex.I * u‖ ≤ _
  rw [div_eq_mul_inv]
  calc
    shiftedCriticalLineLNorm chi delta (t + u) * X ^ delta *
        ‖(delta : ℂ) + Complex.I * u‖⁻¹ ≤
      X ^ delta * shiftedCriticalLineLNorm chi delta (t + u) *
        ((1 + delta⁻¹) * perronWeight u) := by
          rw [mul_comm (shiftedCriticalLineLNorm chi delta (t + u))]
          exact mul_le_mul_of_nonneg_left hk (mul_nonneg hpow0 hL0)
    _ = X ^ delta * (1 + delta⁻¹) *
        (perronWeight u * shiftedCriticalLineLNorm chi delta (t + u)) := by
          ring

/-- Continuity of the corrected integrand away from both the Perron pole and
the possible principal-character pole.  The latter is excluded by
`delta < 1/2`. -/
theorem continuous_shiftedLeftLineIntegrand
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X delta t : ℝ} (hdelta : 0 < delta)
    (hdeltaHalf : delta < 1 / 2) :
    Continuous (shiftedLeftLineIntegrand chi X delta t) := by
  unfold shiftedLeftLineIntegrand PerronKernel.verticalPower
  apply Continuous.div
  · apply Continuous.mul
    · rw [continuous_iff_continuousAt]
      intro u
      have harg :
          ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
              (t + u) * Complex.I) ≠ 1 := by
        intro h
        have hre := congrArg Complex.re h
        norm_num at hre
        linarith
      have houter := (DirichletCharacter.differentiableAt_LFunction chi _
        (.inl harg)).continuousAt
      have hinner : ContinuousAt
          (fun v : ℝ => ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
            (t + v) * Complex.I)) u := by fun_prop
      exact ContinuousAt.comp_of_eq houter hinner rfl
    · fun_prop
  · fun_prop
  · intro u h
    have hre := congrArg Complex.re h
    simp at hre
    linarith

/-- Exact norm estimate for the honest positive-offset vertical integral.
No contour movement and no L-function bound is hidden in this theorem. -/
theorem norm_shiftedLeftLineIntegral_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X delta T t : ℝ} (hX : 0 < X) (hdelta : 0 < delta)
    (hdeltaHalf : delta < 1 / 2) (hT : 0 ≤ T) :
    ‖shiftedLeftLineIntegral chi X delta T t‖ ≤
      (X ^ delta * (1 + delta⁻¹) / (2 * Real.pi)) *
        perronConvolution (shiftedCriticalLineLNorm chi delta) T t := by
  have hcont := continuous_shiftedLeftLineIntegrand
    (X := X) (t := t) chi hdelta hdeltaHalf
  have hshiftedNorm : Continuous (shiftedCriticalLineLNorm chi delta) := by
    unfold shiftedCriticalLineLNorm
    apply Continuous.norm
    rw [continuous_iff_continuousAt]
    intro s
    have harg :
        ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) + s * Complex.I) ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      norm_num at hre
      linarith
    have houter := (DirichletCharacter.differentiableAt_LFunction chi _
      (.inl harg)).continuousAt
    have hinner : ContinuousAt
        (fun x : ℝ => ((((1 / 2 : ℝ) + delta : ℝ) : ℂ) +
          x * Complex.I)) s := by fun_prop
    exact ContinuousAt.comp_of_eq houter hinner rfl
  let g : ℝ → ℝ := fun u =>
    X ^ delta * (1 + delta⁻¹) *
      (perronWeight u * shiftedCriticalLineLNorm chi delta (t + u))
  have hgcont : Continuous g := by
    dsimp only [g]
    exact continuous_const.mul
      (continuous_perronWeight.mul
        (hshiftedNorm.comp (continuous_const.add continuous_id)))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le
    (μ := MeasureTheory.volume)
    (by linarith : -T ≤ T)
    (Filter.Eventually.of_forall fun u hu =>
      norm_shiftedLeftLineIntegrand_le chi hX hdelta)
    (hgcont.intervalIntegrable (-T) T)
  rw [shiftedLeftLineIntegral, norm_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hconst : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ u in (-T)..T, shiftedLeftLineIntegrand chi X delta t u‖ ≤
      (2 * Real.pi)⁻¹ *
        ∫ u in (-T)..T,
          X ^ delta * (1 + delta⁻¹) *
            (perronWeight u *
              shiftedCriticalLineLNorm chi delta (t + u)) := by
        exact mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (by positivity))
    _ = (X ^ delta * (1 + delta⁻¹) / (2 * Real.pi)) *
        perronConvolution (shiftedCriticalLineLNorm chi delta) T t := by
      rw [intervalIntegral.integral_const_mul]
      unfold perronConvolution
      ring

/-- Paper-scale specialization `delta = 1 / log X`.  The retained Perron
kernel has exactly one logarithmic loss; `X^delta` is the absolute constant
`exp 1`.  The explicit half-line hypothesis merely keeps the possible
principal-character pole off the new vertical contour. -/
theorem norm_paperOffsetLeftLineIntegral_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T t : ℝ} (hX : 1 < X)
    (hoffset : (Real.log X)⁻¹ < 1 / 2) (hT : 0 ≤ T) :
    ‖shiftedLeftLineIntegral chi X (Real.log X)⁻¹ T t‖ ≤
      (Real.exp 1 * (1 + Real.log X) / (2 * Real.pi)) *
        perronConvolution
          (shiftedCriticalLineLNorm chi (Real.log X)⁻¹) T t := by
  have hlog : 0 < Real.log X := Real.log_pos hX
  have hbase := norm_shiftedLeftLineIntegral_le (t := t) chi
    (lt_trans zero_lt_one hX) (inv_pos.mpr hlog) hoffset hT
  have hrpow : X ^ (Real.log X)⁻¹ = Real.exp 1 :=
    Real.rpow_inv_log (lt_trans zero_lt_one hX) hX.ne'
  have hinv : ((Real.log X)⁻¹)⁻¹ = Real.log X := inv_inv _
  simpa only [hrpow, hinv] using hbase

/-- Scaled ambient-offset ledger.  This is the reusable form for endpoint-safe
contours: `A = 200` matches a height-`T` Ramachandra window, while `A = 400`
also covers the clean height-`2T` contour and its ensuing height-`4T` fourth
moment. -/
theorem norm_scaledAmbientOffsetLeftLineIntegral_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {A X T t x0 : ℝ} (hA : 4 ≤ A)
    (hX : 2 ≤ X) (hXx : X ≤ x0) (hT : 0 ≤ T) :
    ‖shiftedLeftLineIntegral chi X (A * Real.log x0)⁻¹ T t‖ ≤
      (Real.exp (1 / A) * (1 + A * Real.log x0) /
          (2 * Real.pi)) *
        perronConvolution
          (shiftedCriticalLineLNorm chi (A * Real.log x0)⁻¹) T t := by
  have hApos : 0 < A := lt_of_lt_of_le (by norm_num) hA
  have hXone : 1 < X := lt_of_lt_of_le (by norm_num) hX
  have hx0one : 1 < x0 := hXone.trans_le hXx
  have hx0pos : 0 < x0 := lt_trans zero_lt_one hx0one
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hden : 0 < A * Real.log x0 := mul_pos hApos hlog
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hx0pos
      (hX.trans hXx)
  have hoffset : (A * Real.log x0)⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_lt_iff_one_lt_mul₀ hden]
    nlinarith [mul_le_mul hA hlog2le (Real.log_pos (by norm_num)).le
      hApos.le]
  have hbase := norm_shiftedLeftLineIntegral_le (t := t) chi
    (lt_trans zero_lt_one hXone) (inv_pos.mpr hden) hoffset hT
  have hdelta0 : 0 ≤ (A * Real.log x0)⁻¹ := (inv_pos.mpr hden).le
  have hpowMono : X ^ (A * Real.log x0)⁻¹ ≤
      x0 ^ (A * Real.log x0)⁻¹ :=
    Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one hXone)) hXx hdelta0
  have hx0pow : x0 ^ (A * Real.log x0)⁻¹ = Real.exp (1 / A) := by
    rw [Real.rpow_def_of_pos hx0pos]
    congr 1
    field_simp [hApos.ne', hlog.ne']
  have hpow : X ^ (A * Real.log x0)⁻¹ ≤ Real.exp (1 / A) :=
    hpowMono.trans_eq hx0pow
  have hinv : ((A * Real.log x0)⁻¹)⁻¹ = A * Real.log x0 := inv_inv _
  have hfactor0 : 0 ≤ 1 + A * Real.log x0 := by positivity
  have hconv0 : 0 ≤ perronConvolution
      (shiftedCriticalLineLNorm chi (A * Real.log x0)⁻¹) T t :=
    perronConvolution_nonneg (fun _ => norm_nonneg _) hT
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  calc
    ‖shiftedLeftLineIntegral chi X (A * Real.log x0)⁻¹ T t‖ ≤
        (X ^ (A * Real.log x0)⁻¹ *
            (1 + ((A * Real.log x0)⁻¹)⁻¹) / (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (A * Real.log x0)⁻¹) T t := hbase
    _ = (X ^ (A * Real.log x0)⁻¹ *
            (1 + A * Real.log x0) / (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (A * Real.log x0)⁻¹) T t := by
      rw [hinv]
    _ ≤ (Real.exp (1 / A) *
            (1 + A * Real.log x0) / (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (A * Real.log x0)⁻¹) T t := by
      apply mul_le_mul_of_nonneg_right _ hconv0
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hfactor0) hpi.le

/-- Canonical BHP/Ramachandra offset.  Taking
`delta = 1 / (200 log x0)` simultaneously keeps the retained Perron kernel
polylogarithmic and lies inside Ramachandra's Theorem 6 strip whenever
`q,T ≤ x0` (the latter range check is recorded separately).  This theorem
certifies the complete kernel ledger: `X^delta` is bounded by the absolute
constant `exp (1/200)`, and the reciprocal offset is exactly `200 log x0`. -/
theorem norm_ambientOffsetLeftLineIntegral_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {X T t x0 : ℝ} (hX : 2 ≤ X) (hXx : X ≤ x0) (hT : 0 ≤ T) :
    ‖shiftedLeftLineIntegral chi X (200 * Real.log x0)⁻¹ T t‖ ≤
      (Real.exp (1 / 200 : ℝ) * (1 + 200 * Real.log x0) /
          (2 * Real.pi)) *
        perronConvolution
          (shiftedCriticalLineLNorm chi (200 * Real.log x0)⁻¹) T t := by
  have hXone : 1 < X := lt_of_lt_of_le (by norm_num) hX
  have hx0one : 1 < x0 := hXone.trans_le hXx
  have hx0pos : 0 < x0 := lt_trans zero_lt_one hx0one
  have hlog : 0 < Real.log x0 := Real.log_pos hx0one
  have hden : 0 < 200 * Real.log x0 := mul_pos (by norm_num) hlog
  have hlog2half : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2le : Real.log 2 ≤ Real.log x0 :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hx0pos
      (hX.trans hXx)
  have hoffset : (200 * Real.log x0)⁻¹ < (1 / 2 : ℝ) := by
    rw [inv_lt_iff_one_lt_mul₀ hden]
    nlinarith
  have hbase := norm_shiftedLeftLineIntegral_le (t := t) chi
    (lt_trans zero_lt_one hXone) (inv_pos.mpr hden) hoffset hT
  have hdelta0 : 0 ≤ (200 * Real.log x0)⁻¹ := (inv_pos.mpr hden).le
  have hpowMono : X ^ (200 * Real.log x0)⁻¹ ≤
      x0 ^ (200 * Real.log x0)⁻¹ :=
    Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one hXone)) hXx hdelta0
  have hx0pow : x0 ^ (200 * Real.log x0)⁻¹ =
      Real.exp (1 / 200 : ℝ) := by
    rw [Real.rpow_def_of_pos hx0pos]
    congr 1
    field_simp [hlog.ne']
  have hpow : X ^ (200 * Real.log x0)⁻¹ ≤
      Real.exp (1 / 200 : ℝ) := hpowMono.trans_eq hx0pow
  have hinv : ((200 * Real.log x0)⁻¹)⁻¹ =
      200 * Real.log x0 := inv_inv _
  have hfactor0 : 0 ≤ 1 + 200 * Real.log x0 := by positivity
  have hconv0 : 0 ≤ perronConvolution
      (shiftedCriticalLineLNorm chi (200 * Real.log x0)⁻¹) T t :=
    perronConvolution_nonneg (fun _ => norm_nonneg _) hT
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  calc
    ‖shiftedLeftLineIntegral chi X (200 * Real.log x0)⁻¹ T t‖ ≤
        (X ^ (200 * Real.log x0)⁻¹ *
            (1 + ((200 * Real.log x0)⁻¹)⁻¹) /
              (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (200 * Real.log x0)⁻¹) T t := hbase
    _ = (X ^ (200 * Real.log x0)⁻¹ *
            (1 + 200 * Real.log x0) / (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (200 * Real.log x0)⁻¹) T t := by
      rw [hinv]
    _ ≤ (Real.exp (1 / 200 : ℝ) *
            (1 + 200 * Real.log x0) / (2 * Real.pi)) *
          perronConvolution
            (shiftedCriticalLineLNorm chi (200 * Real.log x0)⁻¹) T t := by
      apply mul_le_mul_of_nonneg_right _ hconv0
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow hfactor0) hpi.le

/-- Elementary range check placing the canonical offset inside the exact
near-critical strip of Ramachandra Theorem 6. -/
theorem ambientOffset_le_ramachandraWindow
    {q : ℕ} [NeZero q] {T x0 : ℝ}
    (hT : 2 ≤ T) (hqx : (q : ℝ) ≤ x0) (hTx : T ≤ x0) :
    (200 * Real.log x0)⁻¹ ≤
      (100 * Real.log ((q : ℝ) * T))⁻¹ := by
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hqone
  have hTpos : 0 < T := by linarith
  have hx0pos : 0 < x0 := hTpos.trans_le hTx
  have hTone : 1 < T := lt_of_lt_of_le (by norm_num) hT
  have hx0one : 1 < x0 := hTone.trans_le hTx
  have hprodOne : 1 < (q : ℝ) * T := by
    calc
      1 ≤ (q : ℝ) := hqone
      _ = (q : ℝ) * 1 := by ring
      _ < (q : ℝ) * T := mul_lt_mul_of_pos_left hTone hqpos
  have hlogprod : 0 < Real.log ((q : ℝ) * T) := Real.log_pos hprodOne
  have hlogx : 0 < Real.log x0 := Real.log_pos hx0one
  have hprodLe : (q : ℝ) * T ≤ x0 ^ 2 := by
    nlinarith [mul_le_mul hqx hTx hTpos.le hx0pos.le]
  have hlogLe : Real.log ((q : ℝ) * T) ≤ 2 * Real.log x0 := by
    have hmono := Real.strictMonoOn_log.monotoneOn
      (mul_pos hqpos hTpos) (sq_pos_of_pos hx0pos) hprodLe
    rw [Real.log_pow] at hmono
    simpa using hmono
  rw [inv_le_inv₀ (mul_pos (by norm_num) hlogx)
    (mul_pos (by norm_num) hlogprod)]
  nlinarith

end
end MAPBHPCorrectedPerronKernel

#print axioms MAPBHPCorrectedPerronKernel.norm_inv_delta_add_I_mul_le_perronWeight
#print axioms MAPBHPCorrectedPerronKernel.norm_shiftedLeftLineIntegral_le
#print axioms MAPBHPCorrectedPerronKernel.norm_paperOffsetLeftLineIntegral_le
#print axioms MAPBHPCorrectedPerronKernel.norm_scaledAmbientOffsetLeftLineIntegral_le
#print axioms MAPBHPCorrectedPerronKernel.norm_ambientOffsetLeftLineIntegral_le
#print axioms MAPBHPCorrectedPerronKernel.ambientOffset_le_ramachandraWindow
