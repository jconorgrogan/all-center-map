import GuthMaynardAffineSmoothingSubpower
import GuthMaynardLemma92ConcreteBump

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Source-faithful profile loss for the Lemma 9.2 plateau bump

The source cutoff is one-bounded and has subpower support.  Its mass is not
one: the literal radius-`B` bump has mass at most `4B`.  These theorems keep
the resulting sup, `L¹`, and squared-`L²` losses explicit for the
Proposition 9.1 induction.
-/

theorem sourceAdmissibleProfile_affineSmoothing_sourceBump_subpower
    {T S F B : ℝ} {f : ℝ → ℝ} (hT : 0 < T)
    (hf : SourceAdmissibleProfile T S F f) (hB : 0 < B) :
    SourceAdmissibleProfile T ((4 * B) * S) (F + (2 * B) / T)
      (affineSmoothing T (fun z => sourceBump B hB z) f) := by
  exact sourceAdmissibleProfile_affineSmoothing_mass hT
    (fun z => sourceBump B hB z) f hf
    (sourceBump_nonneg B hB) (sourceBump_le_one B hB)
    (fun z hz => sourceBump_supported_two_mul hB hz)
    (sourceBump B hB).integrable (sourceBump_contDiff B hB).continuous
    (integral_sourceBump_le_four_mul hB)

theorem integral_affineSmoothing_sourceBump_le_four_mul
    {T B : ℝ} {f : ℝ → ℝ} (hT : 0 < T) (hB : 0 < B)
    (hf0 : ∀ u, 0 ≤ f u) (hf : Integrable f) :
    (∫ x : ℝ,
      affineSmoothing T (fun z => sourceBump B hB z) f x) ≤
      (4 * B) * ∫ u : ℝ, f u := by
  exact integral_affineSmoothing_le_mass_of_integrable hT
    (fun z => sourceBump B hB z) f hf0
    (integral_sourceBump_le_four_mul hB) (sourceBump B hB).integrable hf

theorem integral_sq_affineSmoothing_sourceBump_le_sixteen_mul
    {T B : ℝ} {f : ℝ → ℝ} (hT : 0 < T) (hB : 0 < B)
    (hf0 : ∀ u, 0 ≤ f u) (hf : Integrable f)
    (hf2 : Integrable (fun u : ℝ => f u ^ 2)) :
    (∫ x : ℝ,
      affineSmoothing T (fun z => sourceBump B hB z) f x ^ 2) ≤
      (4 * B) ^ 2 * ∫ u : ℝ, f u ^ 2 := by
  exact integral_sq_affineSmoothing_le_mass_of_integrable hT
    (fun z => sourceBump B hB z) f (sourceBump_nonneg B hB) hf0
    (integral_sourceBump_le_four_mul hB) (sourceBump B hB).integrable hf hf2

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceAdmissibleProfile_affineSmoothing_sourceBump_subpower
#print axioms GuthMaynardJIteration.integral_affineSmoothing_sourceBump_le_four_mul
#print axioms GuthMaynardJIteration.integral_sq_affineSmoothing_sourceBump_le_sixteen_mul
