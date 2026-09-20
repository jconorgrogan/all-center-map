import MAPCertifiedMontgomeryEndpoint
import MAPNearOneBulkBypassDensity
import MAPNearOneBulkBypassGappedConsumer

/-! The verified Montgomery source, actual powered bulk density, and MRT hard
range are supplied internally. Only the GM source, the two literal selected
Jutila collar estimates, the high gap, and the packet budget remain inputs. -/

namespace MAPCertifiedBulkBypassEndpoint

theorem certifiedMAPEndpoint_of_remainingSources
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hP53 : MAPJutilaGappedCollarSelectedP53Adapter.JutilaGappedSelectedSystemP53Eventually)
    (hPrincipalP53 : MAPJutilaGappedCollarSelectedP53Adapter.JutilaGappedSelectedPrincipalP53Eventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap)
    (hpacket : MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint := by
  have hpowered :=
    BudgetedSelectedPoweredBlockAssembly.budgetedFixedCharacterPoweredLargeValueBridge hGM
  have hcompact :=
    PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      (MAPAPWeightedZeroMassPolylogLowStripWeld.polylogConductorDensity_of_lowStrip_and_powered
        MAPMontgomeryPolylogLowStripSource.polylogLowStripDensity_proved hpowered)
  exact MAPCertifiedHardRangeEndpoint.certifiedMAPEndpoint_of_zeroMass_and_packetBudget
    (MAPNearOneBulkBypassGappedConsumer.apWeightedZeroMassLogSaving_of_bulk_selectedP53_and_high_gap
      hcompact (MAPNearOneBulkBypassDensity.fixedPrimitiveBulkPolylogDensity_of_GM hGM)
      hP53 hPrincipalP53 hhighGap)
    hpacket

end MAPCertifiedBulkBypassEndpoint

#print axioms MAPCertifiedBulkBypassEndpoint.certifiedMAPEndpoint_of_remainingSources
