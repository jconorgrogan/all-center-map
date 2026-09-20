import GuthMaynardDiscreteHalfAngle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
namespace GuthMaynardDiscreteCotBound

theorem cot_half_le_pi_div {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    Real.cot (d / 2) ≤ Real.pi / d := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sin (d / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_gt_three])
  have hsin := Real.mul_le_sin (x := d / 2) (by linarith) (by nlinarith [Real.pi_gt_three])
  have hs' : d ≤ Real.pi * Real.sin (d / 2) := by
    have hh := (div_le_iff₀ hpi).mp (show d / Real.pi ≤ Real.sin (d / 2) by
      convert hsin using 1 <;> ring)
    nlinarith
  rw [Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hs hd0).2
  have hc := mul_le_mul_of_nonneg_right (Real.cos_le_one (d / 2)) hd0.le
  nlinarith
end GuthMaynardDiscreteCotBound
#print axioms GuthMaynardDiscreteCotBound.cot_half_le_pi_div
