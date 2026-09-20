import PrincipalZetaFixedStrip

namespace MAPPrincipalZetaA5

open Complex Real Set Metric
open scoped Real
open DirichletZeros MAPLocalZeroWindow

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private theorem abs_im_le_abs_t_add_three {t : ℝ} {z : ℂ}
    (hz : z ∈ sphere (jensenCenter t) |jensenOuterRadius|) :
    |z.im| ≤ |t| + 3 := by
  have hdist : dist z (jensenCenter t) = 17 / 10 := by
    rw [mem_sphere] at hz
    norm_num [jensenOuterRadius] at hz
    exact hz
  have himdiff : |z.im - (t + 1 / 2)| ≤ 17 / 10 := by
    calc
      |z.im - (t + 1 / 2)| = |(z - jensenCenter t).im| := by
        simp [jensenCenter]
      _ ≤ ‖z - jensenCenter t‖ := Complex.abs_im_le_norm _
      _ = 17 / 10 := by simpa [dist_eq_norm] using hdist
  calc
    |z.im| = |(z.im - (t + 1 / 2)) + (t + 1 / 2)| := by ring_nf
    _ ≤ |z.im - (t + 1 / 2)| + |t + 1 / 2| := abs_add_le _ _
    _ ≤ 17 / 10 + (|t| + 1 / 2) := by
      gcongr
      exact (abs_add_le t (1 / 2)).trans_eq (by norm_num)
    _ ≤ |t| + 3 := by linarith

private theorem principal_regularized_eq (z : ℂ) :
    regularizedLFunction (1 : DirichletCharacter ℂ 1) z =
      MAPPrincipalZetaFixedStrip.principalRegularized z := by
  simp [regularizedLFunction, MAPPrincipalZetaFixedStrip.principalRegularized]

private theorem principal_outerCircle_bound (t : ℝ) :
    ∀ z ∈ sphere (jensenCenter t) |jensenOuterRadius|,
      ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) z‖ ≤
        25000000 * (|t| + 2) ^ 6 := by
  intro z hz
  have hzrange := MAPPrimitiveLFixedStrip.jensenOuterCircle_re_mem hz
  have him := abs_im_le_abs_t_add_three hz
  have hshift : ‖z + 3‖ ≤ 5 * (|t| + 2) := by
    have hreadd : |(z + 3).re| ≤ 7 := by
      rw [abs_of_nonneg]
      · simp; linarith [hzrange.1]
      · simp; linarith [hzrange.1]
    calc
      ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 7 + (|t| + 3) := by simpa using add_le_add hreadd him
      _ ≤ 5 * (|t| + 2) := by nlinarith [abs_nonneg t]
  rw [principal_regularized_eq]
  by_cases hre : z.re ≤ 2
  · have hF := MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
      (by linarith [hzrange.1]) hre
    calc
      ‖MAPPrincipalZetaFixedStrip.principalRegularized z‖ ≤
          1600 * ‖z + 3‖ ^ 6 := hF
      _ ≤ 1600 * (5 * (|t| + 2)) ^ 6 := by gcongr
      _ = 25000000 * (|t| + 2) ^ 6 := by ring
  · have hre2 : 2 ≤ z.re := le_of_not_ge hre
    have hz1 : z ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hzeta : ‖riemannZeta z‖ < 3 := by
      have h := MAPPrimitiveLFixedStrip.norm_LFunction_lt_three_of_two_le_re
        (1 : DirichletCharacter ℂ 1) hre2
      simpa [DirichletCharacter.LFunction_modOne_eq] using h
    have hsub : ‖z - 1‖ ≤ 3 * (|t| + 2) := by
      calc
        ‖z - 1‖ ≤ |(z - 1).re| + |(z - 1).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |z.re - 1| + |z.im| := by simp
        _ ≤ 3 + (|t| + 3) := by
          gcongr
          rw [abs_of_nonneg (by linarith)]
          linarith [hzrange.2]
        _ ≤ 3 * (|t| + 2) := by nlinarith [abs_nonneg t]
    rw [MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hz1,
      norm_mul]
    have hscale : 1 ≤ |t| + 2 := by linarith [abs_nonneg t]
    calc
      ‖z - 1‖ * ‖riemannZeta z‖ ≤
          (3 * (|t| + 2)) * 3 :=
        mul_le_mul hsub hzeta.le (norm_nonneg _) (by positivity)
      _ ≤ 25000000 * (|t| + 2) ^ 6 := by
        have hp : |t| + 2 ≤ (|t| + 2) ^ 6 := by
          have h5 : 1 ≤ (|t| + 2) ^ 5 := one_le_pow₀ hscale
          calc
            |t| + 2 ≤ (|t| + 2) * (|t| + 2) ^ 5 := by
              simpa using mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ |t| + 2)
            _ = (|t| + 2) ^ 6 := by ring
        nlinarith

private theorem principal_center_lower (t : ℝ) :
    (1 / 3 : ℝ) ≤
      ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ := by
  let y := t + 1 / 2
  have hL := MAPPrimitiveLFixedStrip.one_third_le_norm_LFunction_two_add
    (1 : DirichletCharacter ℂ 1) y
  rw [DirichletCharacter.LFunction_modOne_eq] at hL
  have hc : jensenCenter t = 2 + Complex.I * y := by
    simp [jensenCenter, y, mul_comm]
  have hc1 : jensenCenter t ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [jensenCenter] at this
  rw [principal_regularized_eq,
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hc1,
    norm_mul]
  have hfactor : 1 ≤ ‖jensenCenter t - 1‖ := by
    have : (1 : ℝ) ≤ |(jensenCenter t - 1).re| := by
      norm_num [jensenCenter]
    exact this.trans (Complex.abs_re_le_norm _)
  have hzeta : (1 / 3 : ℝ) ≤ ‖riemannZeta (jensenCenter t)‖ := by
    simpa [hc] using hL
  nlinarith [mul_le_mul hfactor hzeta (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (norm_nonneg _)]

/-- Upper-half local count for the conductor-one regularized zeta function. -/
theorem principal_upper_closedUnitWindowCount_le (t : ℝ) :
    (closedUnitWindowCount (1 : DirichletCharacter ℂ 1) (1 / 2) t : ℝ) ≤
      561 * Real.log (|t| + 2) := by
  let M : ℝ := 25000000 * (|t| + 2) ^ 6
  have hscale : 2 ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hM : 1 ≤ M := by
    dsimp [M]
    have hp : 1 ≤ (|t| + 2) ^ 6 := one_le_pow₀ (by linarith)
    nlinarith
  have hj := MAPLocalZeroWindow.closedUnitWindowCount_le_jensen
    (1 : DirichletCharacter ℂ 1)
    (t := t) (M := M) (by norm_num : (1 / 2 : ℝ) ≤ 1 / 2) hM
    (principal_outerCircle_bound t)
  have hcenter := principal_center_lower t
  have hcenterPos : 0 <
      ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ := by
    linarith
  have hratio : M /
      ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ ≤
      3 * M := by
    apply (div_le_iff₀ hcenterPos).2
    have h3 : 1 ≤ 3 *
        ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ := by
      linarith
    calc
      M = M * 1 := by ring
      _ ≤ M * (3 *
          ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 * M *
          ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ := by ring
  have hlogratio : Real.log (M /
      ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖) ≤
      33 * Real.log (|t| + 2) := by
    have hratioPos : 0 < M /
        ‖regularizedLFunction (1 : DirichletCharacter ℂ 1) (jensenCenter t)‖ :=
      div_pos (lt_of_lt_of_le zero_lt_one hM) hcenterPos
    have hlog := Real.log_le_log hratioPos hratio
    have hconst : (3 * 25000000 : ℝ) ≤ 2 ^ (27 : ℕ) := by norm_num
    have hconstPos : (0 : ℝ) < 3 * 25000000 := by norm_num
    have hlogConst : Real.log (3 * 25000000 : ℝ) ≤
        27 * Real.log 2 := by
      calc
        Real.log (3 * 25000000 : ℝ) ≤ Real.log (2 ^ (27 : ℕ) : ℝ) :=
          Real.log_le_log hconstPos (by norm_num)
        _ = 27 * Real.log 2 := by rw [Real.log_pow]; norm_num
    have hlog2 : Real.log 2 ≤ Real.log (|t| + 2) :=
      Real.log_le_log (by norm_num) hscale
    have hMlog : Real.log (3 * M) =
        Real.log (3 * 25000000 : ℝ) + 6 * Real.log (|t| + 2) := by
      dsimp [M]
      rw [show 3 * (25000000 * (|t| + 2) ^ 6) =
          (3 * 25000000) * (|t| + 2) ^ 6 by ring,
        Real.log_mul (by norm_num : (3 * 25000000 : ℝ) ≠ 0)
          (pow_ne_zero _ (by linarith : |t| + 2 ≠ 0)),
        Real.log_pow]
      norm_num
    calc
      Real.log (M / ‖regularizedLFunction (1 : DirichletCharacter ℂ 1)
          (jensenCenter t)‖) ≤ Real.log (3 * M) := hlog
      _ = Real.log (3 * 25000000 : ℝ) + 6 * Real.log (|t| + 2) := hMlog
      _ ≤ 33 * Real.log (|t| + 2) := by nlinarith
  have hden : (1 / 17 : ℝ) ≤
      Real.log (jensenOuterRadius / jensenInnerRadius) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < jensenOuterRadius / jensenInnerRadius by
        norm_num [jensenOuterRadius, jensenInnerRadius])
    norm_num [jensenOuterRadius, jensenInnerRadius] at h ⊢
    exact h
  refine hj.trans ?_
  apply (div_le_iff₀ MAPLocalZeroWindow.jensenDenominator_pos).2
  have hlogscale : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hmul : 33 * Real.log (|t| + 2) ≤
      561 * Real.log (|t| + 2) *
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
    nlinarith
  exact hlogratio.trans hmul

#print axioms principal_upper_closedUnitWindowCount_le

end
end MAPPrincipalZetaA5
