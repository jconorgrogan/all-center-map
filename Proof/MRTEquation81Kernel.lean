import MRTSchurTest
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Real.Pi.Bounds

/-! The literal Cauchy-decay kernel and its Schur mass in MRT equation (81). -/

namespace MAPMRTEquation81Kernel

open MeasureTheory

noncomputable section

/-- The decay kernel printed in equations (81)--(82). -/
def equation81Kernel (R x y : ℝ) : ℝ :=
  1 / (1 + |x - y| / R) ^ 2

theorem equation81Kernel_nonneg {R x y : ℝ} :
    0 ≤ equation81Kernel R x y := by
  unfold equation81Kernel
  positivity

theorem continuous_equation81Kernel {R : ℝ} (hR : 0 < R) :
    Continuous fun z : ℝ × ℝ ↦ equation81Kernel R z.1 z.2 := by
  unfold equation81Kernel
  apply Continuous.div continuous_const
  · fun_prop
  · intro z
    positivity

/-- Comparison with the standard Cauchy kernel. -/
theorem equation81Kernel_le_inv_one_add_sq
    {R x y : ℝ} (hR : 0 < R) :
    equation81Kernel R x y ≤ (1 + ((y - x) / R) ^ 2)⁻¹ := by
  let u : ℝ := |x - y| / R
  have hu : 0 ≤ u := by unfold u; positivity
  have hsq : ((y - x) / R) ^ 2 = u ^ 2 := by
    unfold u
    rw [← sq_abs]
    simp [abs_div, abs_of_pos hR, abs_sub_comm]
  have hden : 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
  unfold equation81Kernel
  rw [show |x - y| / R = u by rfl, hsq]
  simpa only [one_div] using
    (one_div_le_one_div_of_le (by positivity) hden)

/-- Each row of the equation-(81) kernel is integrable. -/
theorem integrable_equation81Kernel
    {R x : ℝ} (hR : 0 < R) :
    Integrable fun y ↦ equation81Kernel R x y := by
  let f : ℝ → ℝ := fun u ↦ (1 + u ^ 2)⁻¹
  let g : ℝ → ℝ := fun y ↦ f ((y - x) / R)
  have hf : Integrable f := by
    simpa [f] using integrable_inv_one_add_sq
  have hu : Integrable fun y ↦ f (y / R) := hf.comp_div hR.ne'
  have hg : Integrable g := by
    have ht := hu.comp_add_right (-x)
    simpa [g, sub_eq_add_neg] using ht
  apply hg.mono'
  · have hc : Continuous (fun y ↦ equation81Kernel R x y) :=
      (continuous_equation81Kernel hR).comp (continuous_const.prodMk continuous_id)
    exact hc.aestronglyMeasurable
  · filter_upwards with y
    change |equation81Kernel R x y| ≤ g y
    rw [abs_of_nonneg equation81Kernel_nonneg]
    simpa [g, f] using equation81Kernel_le_inv_one_add_sq (R := R) (x := x) (y := y) hR

/-- The row mass is at most `4R`.  The proof compares to the standard Cauchy
kernel, whose whole-line integral is `πR`, and uses `π<4`. -/
theorem integral_equation81Kernel_le_four
    {R x : ℝ} (hR : 0 < R) :
    (∫ y : ℝ, equation81Kernel R x y) ≤ 4 * R := by
  let f : ℝ → ℝ := fun u ↦ (1 + u ^ 2)⁻¹
  let u : ℝ → ℝ := fun y ↦ f (y / R)
  let g : ℝ → ℝ := fun y ↦ f ((y - x) / R)
  have hf : Integrable f := by simpa [f] using integrable_inv_one_add_sq
  have hu : Integrable u := by simpa [u] using hf.comp_div hR.ne'
  have hg : Integrable g := by
    have ht := hu.comp_add_right (-x)
    simpa [g, u, sub_eq_add_neg] using ht
  have hkg := integrable_equation81Kernel (x := x) hR
  have hmono : (∫ y : ℝ, equation81Kernel R x y) ≤ ∫ y : ℝ, g y := by
    apply integral_mono hkg hg
    intro y
    exact equation81Kernel_le_inv_one_add_sq hR
  have htrans : (∫ y : ℝ, g y) = ∫ y : ℝ, u y := by
    simpa [g, u, sub_eq_add_neg] using integral_add_right_eq_self u (-x)
  have huval : (∫ y : ℝ, u y) = R * Real.pi := by
    have hs := Measure.integral_comp_mul_left f (1 / R)
    calc
      (∫ y : ℝ, u y) = Real.pi * |R| := by
        simpa [u, div_eq_mul_inv, f, integral_univ_inv_one_add_sq,
          smul_eq_mul, mul_comm] using hs
      _ = R * Real.pi := by rw [abs_of_pos hR]; ring
  calc
    (∫ y : ℝ, equation81Kernel R x y) ≤ ∫ y : ℝ, g y := hmono
    _ = R * Real.pi := htrans.trans huval
    _ ≤ 4 * R := by
      nlinarith [Real.pi_lt_four, hR]

/-- ENNReal row mass, in the form consumed by the first-principles Schur
lemma. -/
theorem lintegral_equation81Kernel_le_four
    {R x : ℝ} (hR : 0 < R) :
    (∫⁻ y : ℝ, ENNReal.ofReal (equation81Kernel R x y)) ≤
      ENNReal.ofReal (4 * R) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_equation81Kernel hR)
    (Filter.Eventually.of_forall fun y ↦ equation81Kernel_nonneg)]
  exact ENNReal.ofReal_le_ofReal (integral_equation81Kernel_le_four hR)

/-- The column mass is the same row mass by symmetry. -/
theorem lintegral_equation81Kernel_column_le_four
    {R y : ℝ} (hR : 0 < R) :
    (∫⁻ x : ℝ, ENNReal.ofReal (equation81Kernel R x y)) ≤
      ENNReal.ofReal (4 * R) := by
  have hsymm : ∀ x, equation81Kernel R x y = equation81Kernel R y x := by
    intro x
    simp [equation81Kernel, abs_sub_comm]
  simp_rw [hsymm]
  exact lintegral_equation81Kernel_le_four hR

#print axioms integral_equation81Kernel_le_four
#print axioms lintegral_equation81Kernel_le_four
#print axioms lintegral_equation81Kernel_column_le_four

end
end MAPMRTEquation81Kernel
