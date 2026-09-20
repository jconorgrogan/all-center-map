import DirichletLQuantitativeFoundation

/-!
# Sharp polynomial power on `Gamma(1+it)`

The existing quantitative Gamma module retains the correct exponential rate
but replaces the square-root polynomial factor by a linear one.  Huxley's
right contour needs the square-root power.  For `|t| >= 1` it follows
directly from the already certified exact square norm and the elementary
lower bound `sinh x >= exp x / 4`.
-/

namespace MAPGammaOneSharpPower

open Complex Real

noncomputable section

def onePoint (t : ℝ) : ℂ := (1 : ℂ) + (t : ℂ) * I

def twoPoint (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * I

/-- Exact square norm, re-exposed with a public point definition. -/
theorem norm_Gamma_onePoint_sq (t : ℝ) (ht : t ≠ 0) :
    ‖Complex.Gamma (onePoint t)‖ ^ 2 =
      Real.pi * |t| / |Real.sinh (Real.pi * t)| := by
  simpa [onePoint] using
    MAPDirichletLQuantitative.norm_Gamma_one_add_mul_I_sq t ht

/-- Sharp square-root polynomial bound for `Gamma(1+it)` at large height. -/
theorem norm_Gamma_onePoint_le_sqrt
    {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (onePoint t)‖ ≤
      4 * Real.sqrt (1 + |t|) *
        Real.exp (-(Real.pi / 2) * |t|) := by
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    norm_num at ht
  let u : ℝ := |t|
  have hu : 0 < u := lt_of_lt_of_le (by norm_num) ht
  have hsq := norm_Gamma_onePoint_sq t ht0
  have habssinh : |Real.sinh (Real.pi * t)| =
      Real.sinh (Real.pi * u) := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos Real.pi_pos]
  rw [habssinh] at hsq
  let x : ℝ := Real.pi * u
  have hx : 0 < x := mul_pos Real.pi_pos hu
  have hx4 : 4 ≤ Real.exp x := by
    calc
      4 ≤ x + 1 := by dsimp [x, u]; nlinarith [Real.pi_gt_three]
      _ ≤ Real.exp x := Real.add_one_le_exp x
  have hneg_le_one : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hsinh_lower : Real.exp x / 4 ≤ Real.sinh x := by
    rw [Real.sinh_eq]
    nlinarith
  have hsinh_pos : 0 < Real.sinh x := by positivity
  have hsq_exp :
      ‖Complex.Gamma (onePoint t)‖ ^ 2 ≤
        4 * Real.pi * u * Real.exp (-x) := by
    rw [hsq]
    change Real.pi * u / Real.sinh x ≤ _
    have hdiv : Real.pi * u / Real.sinh x ≤
        Real.pi * u / (Real.exp x / 4) := by
      exact div_le_div_of_nonneg_left (mul_nonneg Real.pi_pos.le hu.le)
        (by positivity) hsinh_lower
    calc
      Real.pi * u / Real.sinh x ≤
          Real.pi * u / (Real.exp x / 4) := hdiv
      _ = 4 * Real.pi * u * Real.exp (-x) := by
        rw [Real.exp_neg]
        field_simp
  have hsqrt_sq : Real.sqrt (1 + u) ^ 2 = 1 + u := by
    rw [sq_sqrt]
    linarith
  have hsq_final :
      ‖Complex.Gamma (onePoint t)‖ ^ 2 ≤
        (4 * Real.sqrt (1 + u) *
          Real.exp (-(Real.pi / 2) * u)) ^ 2 := by
    calc
      ‖Complex.Gamma (onePoint t)‖ ^ 2 ≤
          4 * Real.pi * u * Real.exp (-x) := hsq_exp
      _ ≤ 16 * (1 + u) * Real.exp (-x) := by
        have hcoef : 4 * Real.pi * u ≤ 16 * (1 + u) := by
          nlinarith [Real.pi_le_four]
        gcongr
      _ = (4 * Real.sqrt (1 + u) *
          Real.exp (-(Real.pi / 2) * u)) ^ 2 := by
        dsimp [x]
        rw [show -(Real.pi * u) =
          (-(Real.pi / 2) * u) + (-(Real.pi / 2) * u) by ring,
          Real.exp_add]
        calc
          16 * (1 + u) *
              (Real.exp (-(Real.pi / 2) * u) *
                Real.exp (-(Real.pi / 2) * u)) =
            16 * Real.sqrt (1 + u) ^ 2 *
              (Real.exp (-(Real.pi / 2) * u) *
                Real.exp (-(Real.pi / 2) * u)) := by rw [hsqrt_sq]
          _ = (4 * Real.sqrt (1 + u) *
              Real.exp (-(Real.pi / 2) * u)) ^ 2 := by ring
  have hrhs : 0 ≤ 4 * Real.sqrt (1 + u) *
      Real.exp (-(Real.pi / 2) * u) := by positivity
  have hroot := (sq_le_sq₀ (norm_nonneg _) hrhs).mp hsq_final
  simpa [u] using hroot

private theorem twoPoint_eq (t : ℝ) :
    Complex.Gamma (twoPoint t) =
      onePoint t * Complex.Gamma (onePoint t) := by
  have hne : onePoint t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [onePoint] at hre
  convert Complex.Gamma_add_one (onePoint t) hne using 1 <;>
    simp [twoPoint, onePoint] <;> ring

private theorem norm_onePoint_le (t : ℝ) :
    ‖onePoint t‖ ≤ 1 + |t| := by
  calc
    ‖onePoint t‖ ≤ |(onePoint t).re| + |(onePoint t).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ = 1 + |t| := by simp [onePoint]

/-- The corresponding `Gamma(2+it)` bound with polynomial degree `3/2`. -/
theorem norm_Gamma_twoPoint_le_three_halves
    {t : ℝ} (ht : 1 ≤ |t|) :
    ‖Complex.Gamma (twoPoint t)‖ ≤
      4 * (1 + |t|) * Real.sqrt (1 + |t|) *
        Real.exp (-(Real.pi / 2) * |t|) := by
  rw [twoPoint_eq, norm_mul]
  calc
    ‖onePoint t‖ * ‖Complex.Gamma (onePoint t)‖ ≤
      (1 + |t|) *
        (4 * Real.sqrt (1 + |t|) *
          Real.exp (-(Real.pi / 2) * |t|)) := by
      exact mul_le_mul (norm_onePoint_le t)
        (norm_Gamma_onePoint_le_sqrt ht) (norm_nonneg _) (by positivity)
    _ = 4 * (1 + |t|) * Real.sqrt (1 + |t|) *
        Real.exp (-(Real.pi / 2) * |t|) := by ring

end

end MAPGammaOneSharpPower

#print axioms MAPGammaOneSharpPower.norm_Gamma_onePoint_sq
#print axioms MAPGammaOneSharpPower.norm_Gamma_onePoint_le_sqrt
#print axioms MAPGammaOneSharpPower.norm_Gamma_twoPoint_le_three_halves
