import GuthMaynardTheorem11FinalGlue
import MAPCertifiedTwoSourceEndpointWeakTheta

/-!
# Final local-source endpoint reduction

The fixed-weight Proposition 3.1 estimate is the remaining local GM input.
The canonical D12 two-source endpoint supplies all other endpoint slots,
including the active packet budget.  This module is only a reduction and does
not assert either source premise unconditionally.
-/
namespace GuthMaynardFixedWeightEndpointWeakTheta

open GuthMaynardTheorem11FinalGlue
open GuthMaynardSmoothedProp31Consumer
open MAPPrimitiveRegularHighSavingFixedTheta

theorem certifiedMAPEndpoint_of_fixedWeightProp31_and_anyFixedTheta
    {w : ℝ → ℝ} (hlocal : FixedWeightProp31 w)
    (hHighSaving : FixedThetaWeakHighSavingAny) :
    PrimePairEndpoints.CertifiedMAPEndpoint := by
  exact MAPCertifiedTwoSourceEndpointWeakTheta.certifiedMAPEndpoint_of_canonical_d12_and_anyFixedTheta
    (guthMaynardTheorem11_of_fixedWeightProp31 hlocal) hHighSaving

end GuthMaynardFixedWeightEndpointWeakTheta

#print axioms GuthMaynardFixedWeightEndpointWeakTheta.certifiedMAPEndpoint_of_fixedWeightProp31_and_anyFixedTheta
