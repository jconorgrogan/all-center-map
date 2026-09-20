import GuthMaynardDiscreteFirstDerivative

namespace GuthMaynardDiscreteInverseVariation

open Set

/-- Cotangent is antitone on the unit interval.  This is the real-variable
monotonicity needed for the imaginary part of the first-derivative inverse
coefficient. -/
theorem cot_antitone_on_unit :
    AntitoneOn Real.cot (Set.Ioc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  have hsx : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by nlinarith [Real.pi_gt_three, hx.2])
  have hsy : 0 < Real.sin y :=
    Real.sin_pos_of_pos_of_lt_pi hy.1 (by nlinarith [Real.pi_gt_three, hy.2])
  apply (div_le_div_iff₀ hsy hsx).2
  have hd0 : 0 ≤ y - x := sub_nonneg.mpr hxy
  have hdp : y - x ≤ Real.pi := by
    nlinarith [hy.2, hx.1, Real.pi_gt_three]
  have hs : 0 ≤ Real.sin (y - x) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hd0 hdp
  rw [Real.sin_sub] at hs
  linarith

theorem cot_nonneg_on_unit {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ Real.cot x := by
  rw [Real.cot_eq_cos_div_sin]
  have hs : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 (by nlinarith [Real.pi_gt_three, hx.2])
  have hc : 0 ≤ Real.cos x := by
    exact Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos, hx.1], by
      nlinarith [Real.pi_gt_three, hx.2]⟩
  positivity

end GuthMaynardDiscreteInverseVariation

#print axioms GuthMaynardDiscreteInverseVariation.cot_antitone_on_unit
#print axioms GuthMaynardDiscreteInverseVariation.cot_nonneg_on_unit
