import AppendixA45GrowthConnector

/-!
# Explicit radius-three Dirichlet-L disk growth

This packages every existing quantitative input needed before the classical
finite Blaschke decomposition: a polynomial upper bound on the full circle
centered at `2+it`, and a conductor-uniform lower bound at its center.
-/

namespace WideDiskLFunctionGrowth

open Complex Set Metric DirichletZeros MAPLocalZeroWindow

noncomputable section

def wideCenter (t : ℝ) : ℂ := 2 + Complex.I * t

def wideRadius : ℝ := 3

@[simp] theorem wideCenter_re (t : ℝ) : (wideCenter t).re = 2 := by
  simp [wideCenter]

@[simp] theorem wideCenter_im (t : ℝ) : (wideCenter t).im = t := by
  simp [wideCenter]

theorem wideCircle_coordinates {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (wideCenter t) wideRadius) :
    -1 ≤ z.re ∧ z.re ≤ 5 ∧ |z.im| ≤ |t| + 3 := by
  have hdist : ‖z - wideCenter t‖ = 3 := by
    simpa [Metric.mem_sphere, dist_eq_norm, wideRadius] using hz
  have hre : |z.re - 2| ≤ 3 := by
    calc
      |z.re - 2| = |(z - wideCenter t).re| := by simp
      _ ≤ ‖z - wideCenter t‖ := Complex.abs_re_le_norm _
      _ = 3 := hdist
  have himdiff : |z.im - t| ≤ 3 := by
    calc
      |z.im - t| = |(z - wideCenter t).im| := by simp
      _ ≤ ‖z - wideCenter t‖ := Complex.abs_im_le_norm _
      _ = 3 := hdist
  have him : |z.im| ≤ |t| + 3 := by
    calc
      |z.im| = |(z.im - t) + t| := by ring_nf
      _ ≤ |z.im - t| + |t| := abs_add_le _ _
      _ ≤ |t| + 3 := by linarith
  rw [abs_le] at hre
  exact ⟨by linarith, by linarith, him⟩

/-- The promoted fixed-strip estimate and the absolutely convergent right
half-plane combine into one explicit bound on the radius-three circle. -/
theorem norm_regularizedLFunction_wideCircle_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (wideCenter t) wideRadius) :
    ‖regularizedLFunction χ z‖ ≤
      7200 * (arithmeticScale q t) ^ 2 := by
  have hcoord := wideCircle_coordinates hz
  rw [regularizedLFunction, if_neg hχ]
  by_cases hzright : 2 ≤ z.re
  · have hright := MAPPrimitiveLFixedStrip.norm_LFunction_lt_three_of_two_le_re
      χ hzright
    have hqnat : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast hqnat
    have hscale : 1 ≤ arithmeticScale q t :=
      MAPPrimitiveLFixedStrip.one_le_arithmeticScale t
    exact hright.le.trans (by nlinarith [sq_nonneg (arithmeticScale q t - 1)])
  · have hzle : z.re ≤ 2 := le_of_not_ge hzright
    have hL := PLInteriorGrowth.norm_LFunction_fixedStrip_le χ hχ hcoord.1 hzle
    have hreadd : |(z + 3).re| ≤ 8 := by
      rw [show (z + 3).re = z.re + 3 by norm_num]
      rw [abs_of_nonneg (by linarith [hcoord.1])]
      linarith [hcoord.2.1]
    have himadd : |(z + 3).im| ≤ |t| + 3 := by
      simpa using hcoord.2.2
    have hshift : ‖z + 3‖ ≤ 6 * (|t| + 2) := by
      calc
        ‖z + 3‖ ≤ |(z + 3).re| + |(z + 3).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ ≤ 8 + (|t| + 3) := add_le_add hreadd himadd
        _ ≤ 6 * (|t| + 2) := by nlinarith [abs_nonneg t]
    have hqnonneg : (0 : ℝ) ≤ q := by positivity
    calc
      ‖DirichletCharacter.LFunction χ z‖ ≤
          200 * (q : ℝ) ^ 2 * ‖z + 3‖ ^ 2 := hL
      _ ≤ 200 * (q : ℝ) ^ 2 * (6 * (|t| + 2)) ^ 2 := by
        gcongr
      _ = 7200 * (arithmeticScale q t) ^ 2 := by
        simp only [arithmeticScale]
        ring

/-- Exact center lower bound, inherited from the Euler-product inverse. -/
theorem one_third_le_norm_regularizedLFunction_wideCenter
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) :
    (1 / 3 : ℝ) ≤ ‖regularizedLFunction χ (wideCenter t)‖ := by
  rw [regularizedLFunction, if_neg hχ]
  simpa [wideCenter, mul_comm] using
    MAPPrimitiveLFixedStrip.one_third_le_norm_LFunction_two_add χ t

/-- The resulting explicit numerator growth ratio on the wide circle.  A
finite Blaschke decomposition would transfer this bound unchanged to the
zero-deflated analytic factor. -/
theorem log_regularizedLFunction_wideCircle_ratio_le
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {t : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (wideCenter t) wideRadius) :
    Real.log
        (‖regularizedLFunction χ z‖ /
          ‖regularizedLFunction χ (wideCenter t)‖) ≤
      Real.log 21600 + 2 * Real.log (arithmeticScale q t) := by
  have hupper := norm_regularizedLFunction_wideCircle_le χ hχ hz
  have hlower := one_third_le_norm_regularizedLFunction_wideCenter χ hχ t
  have hcenterPos : 0 < ‖regularizedLFunction χ (wideCenter t)‖ := by
    linarith
  have hratio :
      ‖regularizedLFunction χ z‖ /
          ‖regularizedLFunction χ (wideCenter t)‖ ≤
        21600 * (arithmeticScale q t) ^ 2 := by
    apply (div_le_iff₀ hcenterPos).2
    have hone : 1 ≤ 3 * ‖regularizedLFunction χ (wideCenter t)‖ := by
      linarith
    calc
      ‖regularizedLFunction χ z‖ ≤
          7200 * (arithmeticScale q t) ^ 2 := hupper
      _ ≤ (21600 * (arithmeticScale q t) ^ 2) *
          ‖regularizedLFunction χ (wideCenter t)‖ := by
        nlinarith [sq_nonneg (arithmeticScale q t)]
  have hscale : 0 < arithmeticScale q t :=
    lt_of_lt_of_le zero_lt_one
      (MAPPrimitiveLFixedStrip.one_le_arithmeticScale t)
  have hrightPos : 0 < 21600 * (arithmeticScale q t) ^ 2 := by positivity
  have hlogeq :
      Real.log (21600 * (arithmeticScale q t) ^ 2) =
        Real.log 21600 + 2 * Real.log (arithmeticScale q t) := by
    rw [Real.log_mul (by norm_num : (21600 : ℝ) ≠ 0)
      (pow_ne_zero 2 hscale.ne'), Real.log_pow]
    norm_num
  by_cases hz0 : ‖regularizedLFunction χ z‖ = 0
  · rw [hz0, zero_div, Real.log_zero]
    rw [← hlogeq]
    exact Real.log_nonneg (by
      have hsone : 1 ≤ arithmeticScale q t :=
        MAPPrimitiveLFixedStrip.one_le_arithmeticScale t
      nlinarith [sq_nonneg (arithmeticScale q t - 1)])
  · calc
      Real.log
          (‖regularizedLFunction χ z‖ /
            ‖regularizedLFunction χ (wideCenter t)‖) ≤
          Real.log (21600 * (arithmeticScale q t) ^ 2) :=
        Real.log_le_log (div_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz0))
          hcenterPos) hratio
      _ = Real.log 21600 + 2 * Real.log (arithmeticScale q t) := hlogeq

end

end WideDiskLFunctionGrowth
