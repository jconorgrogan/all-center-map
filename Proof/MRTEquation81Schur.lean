import MRTEquation81Kernel

/-! Schur specialization for the exact decay kernel in MRT equation (81). -/

namespace MAPMRTEquation81Schur

open MeasureTheory
open MAPMRTSchurTest MAPMRTEquation81Kernel

noncomputable section

/-- The first-principles Schur bound for the literal equation-(81) kernel.
The factor is `2·4R`: `4R` is the proved row/column mass, and `2` comes from
the elementary bilinear proof in `MRTSchurTest`. -/
theorem equation81_kernel_schur
    {R : ℝ} {A : ℝ → NNReal} (hR : 0 < R)
    (hA : Measurable fun x ↦ (A x : ENNReal)) :
    (∫⁻ z : ℝ × ℝ,
      (A z.1 : ENNReal) * (A z.2 : ENNReal) *
        ENNReal.ofReal (equation81Kernel R z.1 z.2) ∂volume.prod volume) ≤
      2 * ENNReal.ofReal (4 * R) *
        (∫⁻ x : ℝ, (A x : ENNReal) ^ 2) := by
  apply lintegral_bilinear_le_two_mul_of_schur
    (μ := volume)
    (K := fun x y ↦ ENNReal.ofReal (equation81Kernel R x y))
    (M := ENNReal.ofReal (4 * R)) hA
  · exact (continuous_equation81Kernel hR).measurable.ennreal_ofReal
  · exact ENNReal.ofReal_ne_top
  · intro x
    exact lintegral_equation81Kernel_le_four hR
  · intro y
    exact lintegral_equation81Kernel_column_le_four hR

#print axioms equation81_kernel_schur

end
end MAPMRTEquation81Schur
