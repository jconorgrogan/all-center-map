import JutilaP53PrincipalRResidueAggregation

/-!
# Exact integration of the p.53 source rectangle budgets
-/

namespace MAPJutilaP53SourceScaleIntegration

open MeasureTheory Real

noncomputable section

/-- A scale-independent pointwise residue budget acquires exactly the area
of Jutila's logarithmic `(xi,upsilon)` rectangle. -/
theorem sourceRectangle_integral_const
    (epsilon z1 x K : ℝ) :
    (∫ xi in (1 - epsilon) * Real.log z1..Real.log z1,
      ∫ upsilon in Real.log x..(1 + epsilon) * Real.log x, K) =
      epsilon ^ 2 * Real.log z1 * Real.log x * K := by
  simp only [intervalIntegral.integral_const]
  ring

/-- Monotone integration over the exact source rectangle.  This packages
the deterministic last step once a pointwise nonnegative residue envelope
has been established. -/
theorem sourceRectangle_integral_le_const
    {F : ℝ → ℝ → ℝ} {epsilon z1 x K : ℝ}
    (heps : 0 ≤ epsilon) (hz : 1 ≤ z1) (hx : 1 ≤ x)
    (hOuterInt : IntervalIntegrable
      (fun xi => ∫ upsilon in Real.log x..(1 + epsilon) * Real.log x,
        F xi upsilon) volume
      ((1 - epsilon) * Real.log z1) (Real.log z1))
    (hFint : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      IntervalIntegrable (F xi) volume (Real.log x)
        ((1 + epsilon) * Real.log x))
    (hF : ∀ xi ∈ Set.Icc ((1 - epsilon) * Real.log z1) (Real.log z1),
      ∀ upsilon ∈ Set.Icc (Real.log x) ((1 + epsilon) * Real.log x),
        F xi upsilon ≤ K) :
    (∫ xi in (1 - epsilon) * Real.log z1..Real.log z1,
      ∫ upsilon in Real.log x..(1 + epsilon) * Real.log x,
        F xi upsilon) ≤
      epsilon ^ 2 * Real.log z1 * Real.log x * K := by
  have hzlog : 0 ≤ Real.log z1 := Real.log_nonneg hz
  have hxlog : 0 ≤ Real.log x := Real.log_nonneg hx
  have hout : (1 - epsilon) * Real.log z1 ≤ Real.log z1 := by
    nlinarith
  have hin : Real.log x ≤ (1 + epsilon) * Real.log x := by
    nlinarith
  calc
    _ ≤ ∫ xi in (1 - epsilon) * Real.log z1..Real.log z1,
        (∫ _upsilon in Real.log x..(1 + epsilon) * Real.log x, K) := by
      apply intervalIntegral.integral_mono_on hout
      · exact hOuterInt
      · exact intervalIntegrable_const
      · intro xi hxi
        apply intervalIntegral.integral_mono_on hin
        · exact hFint xi hxi
        · exact intervalIntegrable_const
        · intro upsilon hups
          exact hF xi hxi upsilon hups
    _ = _ := sourceRectangle_integral_const epsilon z1 x K

end

end MAPJutilaP53SourceScaleIntegration

#print axioms MAPJutilaP53SourceScaleIntegration.sourceRectangle_integral_const
#print axioms MAPJutilaP53SourceScaleIntegration.sourceRectangle_integral_le_const
