import GuthMaynardProp31Actual
import GuthMaynardFixedWeightEndpointWeakTheta

namespace GuthMaynardActualEndpointWeakTheta

/-- The global GM interface, with the concrete local estimate supplied. -/
theorem actual_guthMaynardTheorem11 : CGLProofDAG.GuthMaynardTheorem11 :=
  GuthMaynardTheorem11FinalGlue.guthMaynardTheorem11_of_fixedWeightProp31
    GuthMaynardProp31Actual.actual_fixedWeightProp31

/-- Only the fixed-theta high-saving source remains an input at this endpoint.
This is deliberately a conditional endpoint, not an unconditional MAP claim. -/
theorem certifiedMAPEndpoint_of_anyFixedTheta
    (hHighSaving : MAPPrimitiveRegularHighSavingFixedTheta.FixedThetaWeakHighSavingAny) :
    PrimePairEndpoints.CertifiedMAPEndpoint :=
  GuthMaynardFixedWeightEndpointWeakTheta.certifiedMAPEndpoint_of_fixedWeightProp31_and_anyFixedTheta
    GuthMaynardProp31Actual.actual_fixedWeightProp31 hHighSaving

end GuthMaynardActualEndpointWeakTheta
#print axioms GuthMaynardActualEndpointWeakTheta.actual_guthMaynardTheorem11
#print axioms GuthMaynardActualEndpointWeakTheta.certifiedMAPEndpoint_of_anyFixedTheta
