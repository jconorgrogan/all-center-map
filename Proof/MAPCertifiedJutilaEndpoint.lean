import MAPCertifiedBulkBypassEndpoint
import JutilaGappedAggregateP53Closed

/-! The nonprincipal Jutila selected-system source is now supplied internally.
The principal collar, GM source, high gap, and uniform packet budget remain
explicit analytic inputs. -/

namespace MAPCertifiedJutilaEndpoint

theorem certifiedMAPEndpoint_of_remainingSources
    (hGM : CGLProofDAG.GuthMaynardTheorem11)
    (hPrincipalP53 : MAPJutilaGappedCollarSelectedP53Adapter.JutilaGappedSelectedPrincipalP53Eventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap)
    (hpacket : MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget) :
    PrimePairEndpoints.CertifiedMAPEndpoint :=
  MAPCertifiedBulkBypassEndpoint.certifiedMAPEndpoint_of_remainingSources hGM
    (MAPJutilaGappedFixedModulusAggregateP53Adapter.jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
      MAPJutilaGappedAggregateP53Closed.jutilaGappedFixedModulusAggregateP53Eventually)
    hPrincipalP53 hhighGap hpacket

end MAPCertifiedJutilaEndpoint

#print axioms MAPCertifiedJutilaEndpoint.certifiedMAPEndpoint_of_remainingSources
