import MAPCertifiedHardRangeEndpoint
import APWeightedZeroMassPolylogLowStripWeld
import MontgomeryPolylogLowStripSource

/-! Montgomery's low-strip density and MRT's hard-range estimate are supplied
internally. The remaining analytic inputs stay explicit; this is not yet an
unconditional MAP theorem. -/

namespace MAPCertifiedMontgomeryEndpoint

theorem certifiedMAPEndpoint_of_remainingSources
    (hpowered : CGLProofDAG.BudgetedFixedCharacterPoweredLargeValueBridge)
    (hjutila : MAPAPRegularNearLogSaving.JutilaEquation17OneTenthEventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap)
    (hpacket : MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint :=
  MAPCertifiedHardRangeEndpoint.certifiedMAPEndpoint_of_zeroMass_and_packetBudget
    (MAPAPWeightedZeroMassPolylogLowStripWeld.apWeightedZeroMassLogSaving_of_lowStrip_and_remainingSources
      MAPMontgomeryPolylogLowStripSource.polylogLowStripDensity_proved
      hpowered hjutila hhighGap)
    hpacket

end MAPCertifiedMontgomeryEndpoint

#print axioms MAPCertifiedMontgomeryEndpoint.certifiedMAPEndpoint_of_remainingSources
