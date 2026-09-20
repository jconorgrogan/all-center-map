import MAPCertifiedThreeSourceEndpointWeakTheta
import MRTDynamicD12CanonicalUniformBudget
import MRTProposition61HighCertificateBridgeV3

/-!
# Canonical two-source endpoint wrapper

The canonical D12 producer supplies the uniform active-packet bridge, and the
checked active-bridge consumer supplies the public packet budget.  Consequently
the endpoint exposes only the GM theorem and the fixed-`theta` high-saving
source; all selected P53, compact/bulk density, D12, and packet slots are
constructed internally.  This is an endpoint wrapper only and makes no new
claim about the analytic truth of those source theorems.
-/
namespace MAPCertifiedTwoSourceEndpointWeakTheta

open MAPPrimitiveRegularHighSavingFixedTheta
open MAPPacketIndexedFarBudgetConsumerV2

theorem certifiedMAPEndpoint_of_canonical_d12_and_fixedTheta
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hHighSaving : FixedThetaWeakHighSaving)
    : PrimePairEndpoints.CertifiedMAPEndpoint := by
  have hbridge :
      MRTProposition61HighCertificateBridgeV3.UniformActivePacketCertificateBridge :=
    MRTDynamicD12CanonicalUniformBudget.uniform_active_packet_bridge_of_canonical_producer
  have hpacket : UniformPacketIndexedPaddedFarBudget :=
    MRTProposition61HighCertificateBridgeV3.uniformPacketIndexedPaddedFarBudget_of_activeBridge
      hbridge
  exact MAPCertifiedThreeSourceEndpointWeakTheta.certifiedMAPEndpoint_of_remainingSources_fixedTheta
    hGM hHighSaving hpacket

theorem certifiedMAPEndpoint_of_canonical_d12_and_anyFixedTheta
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hHighSaving : FixedThetaWeakHighSavingAny)
    : PrimePairEndpoints.CertifiedMAPEndpoint := by
  have hbridge :
      MRTProposition61HighCertificateBridgeV3.UniformActivePacketCertificateBridge :=
    MRTDynamicD12CanonicalUniformBudget.uniform_active_packet_bridge_of_canonical_producer
  have hpacket : UniformPacketIndexedPaddedFarBudget :=
    MRTProposition61HighCertificateBridgeV3.uniformPacketIndexedPaddedFarBudget_of_activeBridge
      hbridge
  exact MAPCertifiedThreeSourceEndpointWeakTheta.certifiedMAPEndpoint_of_remainingSources_anyFixedTheta
    hGM hHighSaving hpacket

end MAPCertifiedTwoSourceEndpointWeakTheta

#print axioms MAPCertifiedTwoSourceEndpointWeakTheta.certifiedMAPEndpoint_of_canonical_d12_and_fixedTheta
#print axioms MAPCertifiedTwoSourceEndpointWeakTheta.certifiedMAPEndpoint_of_canonical_d12_and_anyFixedTheta
