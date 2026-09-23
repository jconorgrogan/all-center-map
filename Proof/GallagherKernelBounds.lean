import NearCollarGallagherFiniteUnion
import Mathlib.Analysis.Real.Pi.Bounds

namespace MAPNearCollarGallagher

open MeasureTheory Set
noncomputable section

/-- The interval multiplier produced by sliding `(x,x+y]`, with the positive
phase forced by Mathlib's negative-sign Fourier convention in `x`. -/
def gallagherWindowKernel (y beta : ℝ) : ℂ :=
  ∫ u in 0..y, Complex.exp (2 * Real.pi * Complex.I * (beta * u))

theorem continuous_gallagherWindowKernel (y : ℝ) :
    Continuous (gallagherWindowKernel y) := by
  unfold gallagherWindowKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  fun_prop

@[simp] theorem gallagherWindowKernel_zero (y : ℝ) :
    gallagherWindowKernel y 0 = y := by
  unfold gallagherWindowKernel
  convert intervalIntegral.integral_const (a := (0 : ℝ)) (b := y) (1 : ℂ) using 1 <;>
    simp

/-- On the manuscript band `|beta| ≤ 1/(8y)`, every phase across a positive
window has absolute value at most one. -/
theorem abs_gallagher_phase_le_one
    {y beta u : ℝ} (hy : 0 < y) (hu : u ∈ Set.Icc (0 : ℝ) y)
    (hbeta : |beta| ≤ 1 / (8 * y)) :
    |2 * Real.pi * beta * u| ≤ 1 := by
  have hden : 0 < 8 * y := by positivity
  have hbnonneg : 0 ≤ 1 / (8 * y) := by positivity
  have hu0 : 0 ≤ u := hu.1
  have huy : u ≤ y := hu.2
  have habs_u : |u| = u := abs_of_nonneg hu0
  calc
    |2 * Real.pi * beta * u| = 2 * Real.pi * |beta| * u := by
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), habs_u]
    _ ≤ 2 * Real.pi * (1 / (8 * y)) * y := by
      gcongr
    _ = Real.pi / 4 := by field_simp; ring
    _ ≤ 1 := by linarith [Real.pi_le_four]

/-- The real part of the Gallagher kernel is at least half its window length
on the exact `1/(8y)` band. -/
theorem half_window_le_re_gallagherWindowKernel
    {y beta : ℝ} (hy : 0 < y)
    (hbeta : |beta| ≤ 1 / (8 * y)) :
    y / 2 ≤ (gallagherWindowKernel y beta).re := by
  have hcontCos : Continuous (fun u : ℝ => Real.cos (2 * Real.pi * beta * u)) := by
    fun_prop
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) y,
      (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * beta * u) := by
    intro u hu
    have hphase := abs_gallagher_phase_le_one hy hu hbeta
    have hsq : (2 * Real.pi * beta * u) ^ 2 ≤ 1 := by
      have hm : |2 * Real.pi * beta * u| ^ 2 ≤ (1 : ℝ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hphase 2
      rw [sq_abs] at hm
      simpa using hm
    have hcos := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * beta * u)
    nlinarith
  have hmono :
      (∫ u in (0 : ℝ)..y, (1 / 2 : ℝ)) ≤
        ∫ u in (0 : ℝ)..y, Real.cos (2 * Real.pi * beta * u) := by
    apply intervalIntegral.integral_mono_on hy.le
    · exact continuous_const.intervalIntegrable _ _
    · exact hcontCos.intervalIntegrable _ _
    · intro u hu
      simpa using hpoint u hu
  have hre :
      (gallagherWindowKernel y beta).re =
        ∫ u in (0 : ℝ)..y, Real.cos (2 * Real.pi * beta * u) := by
    unfold gallagherWindowKernel
    have hint : IntervalIntegrable
        (fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * (beta * u)))
        volume 0 y := (by fun_prop : Continuous
          (fun u : ℝ => Complex.exp (2 * Real.pi * Complex.I * (beta * u)))).intervalIntegrable _ _
    rw [← Complex.reCLM_apply,
      ← ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hint]
    apply intervalIntegral.integral_congr
    intro u hu
    simp only [Complex.reCLM_apply]
    convert Complex.exp_ofReal_mul_I_re (2 * Real.pi * beta * u) using 1 <;>
      push_cast <;> ring
  rw [hre]
  simpa [intervalIntegral.integral_const, div_eq_mul_inv] using hmono

/-- Exact multiplier lower bound used by Gallagher--Plancherel. -/
theorem half_window_le_norm_gallagherWindowKernel
    {y beta : ℝ} (hy : 0 < y)
    (hbeta : |beta| ≤ 1 / (8 * y)) :
    y / 2 ≤ ‖gallagherWindowKernel y beta‖ := by
  exact (half_window_le_re_gallagherWindowKernel hy hbeta).trans
    ((le_abs_self _).trans (Complex.abs_re_le_norm _))

/-- Squared form with a deliberately simple constant. -/
theorem window_sq_le_four_mul_kernel_norm_sq
    {y beta : ℝ} (hy : 0 < y)
    (hbeta : |beta| ≤ 1 / (8 * y)) :
    y ^ 2 ≤ 4 * ‖gallagherWindowKernel y beta‖ ^ 2 := by
  have h := half_window_le_norm_gallagherWindowKernel hy hbeta
  nlinarith [sq_nonneg (‖gallagherWindowKernel y beta‖ - y / 2)]

end
end MAPNearCollarGallagher
