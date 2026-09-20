import MRTProposition61TypeIIComponentCauchyV3
import MAPFinishDynamicLowTypesRefinedV3

/-! # Refined fixed-weight collection of dynamic Type-II components -/

namespace MRTProposition61TypeIIComponentCauchyRefinedV3

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicThreeTypeTrace
open MAPFinishDynamicLowTypesRefinedV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215HBExpansion

noncomputable section

theorem dynamicBranchTypeIIMassRefined_le_rawComponents
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchTypeIIMassRefinedV3
        p delta H₀ hX hdelta component branch ≤
      dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
        (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
          (branch : ℕ) : ℝ) *
        dynamicRawLowComponentMassV3
          p delta H₀ branch .typeII component := by
  have hraw :=
    componentIntegral_dynamicRawBranchRemainderCoeffV3_le_components
      (delta := delta) (H₀ := H₀) hp branch
      HBPerronPacketIndexedSourceV2.HBRemainderKind.typeII component
  have hw : 0 ≤ dynamicBranchLowWeightRefinedV3
      (K := hbOrder delta) := by
    unfold dynamicBranchLowWeightRefinedV3
    positivity
  unfold dynamicBranchTypeIIMassRefinedV3
  have hmul := mul_le_mul_of_nonneg_left hraw hw
  simpa [mul_assoc] using hmul

theorem dynamicAllTypeIIMassRefined_le_rawComponents
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllTypeIIMassRefinedV3 p delta H₀ hX hdelta component ≤
      ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          dynamicRawLowComponentMassV3
            p delta H₀ branch .typeII component := by
  unfold dynamicAllTypeIIMassRefinedV3
  exact Finset.sum_le_sum fun branch hbranch =>
    dynamicBranchTypeIIMassRefined_le_rawComponents
      hp hX hdelta component branch

end
end MRTProposition61TypeIIComponentCauchyRefinedV3

#print axioms MRTProposition61TypeIIComponentCauchyRefinedV3.dynamicAllTypeIIMassRefined_le_rawComponents
