import MAPCertifiedBulkBypassEndpoint
import MAPNearOneBulkBypassGappedConsumerWeakTheta
import MAPCertifiedJutilaEndpoint
import JutilaPrincipalSelectedP53FinalWeld

/-!
# Fixed-theta three-source endpoint wrapper

This is the endpoint-level replacement boundary for the old hard-coded
`PrimitiveRegularHighGap` input.  The GM source, fixed-`theta` high saving,
and packet budget remain explicit.  Both selected P53 sources are discharged
internally, while the near-one weighted-zero source is supplied by the checked
fixed-`theta` consumer.
-/
namespace MAPCertifiedThreeSourceEndpointWeakTheta

open MAPPrimitiveRegularHighSavingFixedTheta
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPPacketIndexedFarBudgetConsumerV2
open MAPFixedScaleAPZeroRoute

theorem certifiedMAPEndpoint_of_remainingSources_fixedTheta
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hHighSaving : FixedThetaWeakHighSaving)
    (hpacket : UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint := by
  obtain ⟨theta, hThetaLow, hTheta, hHighSaving⟩ := hHighSaving
  have hP53 :=
    MAPJutilaGappedFixedModulusAggregateP53Adapter.jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
      MAPJutilaGappedAggregateP53Closed.jutilaGappedFixedModulusAggregateP53Eventually
  have hPrincipalP53 :=
    MAPJutilaPrincipalSelectedP53FinalWeld.jutilaGappedSelectedPrincipalP53Eventually
  have hpowered :=
    BudgetedSelectedPoweredBlockAssembly.budgetedFixedCharacterPoweredLargeValueBridge hGM
  have hcompact :=
    PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      (MAPAPWeightedZeroMassPolylogLowStripWeld.polylogConductorDensity_of_lowStrip_and_powered
        MAPMontgomeryPolylogLowStripSource.polylogLowStripDensity_proved hpowered)
  exact MAPCertifiedHardRangeEndpoint.certifiedMAPEndpoint_of_zeroMass_and_packetBudget
    (MAPNearOneBulkBypassGappedConsumerWeakTheta.apWeightedZeroMassLogSaving_of_bulk_selectedP53_and_high_saving
      hcompact
      (MAPNearOneBulkBypassDensity.fixedPrimitiveBulkPolylogDensity_of_GM hGM)
      hP53 hPrincipalP53 theta hThetaLow hTheta hHighSaving)
    hpacket

theorem certifiedMAPEndpoint_of_remainingSources_anyFixedTheta
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hHighSaving : FixedThetaWeakHighSavingAny)
    (hpacket : UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_remainingSources_fixedTheta hGM
    (fixedThetaWeakHighSaving_of_any hHighSaving) hpacket

end MAPCertifiedThreeSourceEndpointWeakTheta

#print axioms MAPCertifiedThreeSourceEndpointWeakTheta.certifiedMAPEndpoint_of_remainingSources_fixedTheta
#print axioms MAPCertifiedThreeSourceEndpointWeakTheta.certifiedMAPEndpoint_of_remainingSources_anyFixedTheta
