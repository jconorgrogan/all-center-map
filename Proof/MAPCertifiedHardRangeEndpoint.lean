import MAPReducedEndpointWeld
import MRTFaithfulProjectionAssembly

/-! The faithful low, medium and high projections now supply MAP's hard-range
estimate internally.  The two remaining inputs are stated explicitly below. -/

namespace MAPCertifiedHardRangeEndpoint

theorem certifiedMAPEndpoint_of_zeroMass_and_packetBudget
    (hzero : MAPFixedScaleAPZeroRoute.APWeightedZeroMassLogSaving)
    (hpacket : MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint :=
  MAPReducedEndpointWeld.certifiedMAPEndpoint_of_reducedPacketLeaves
    { weightedZeroMass := hzero
      mapLambdaHardRange := MAPMRTFaithfulProjectionAssembly.faithful_mapLambdaCorollary53HardRange
      packetFarBudget := hpacket }

end MAPCertifiedHardRangeEndpoint

#print axioms MAPCertifiedHardRangeEndpoint.certifiedMAPEndpoint_of_zeroMass_and_packetBudget
