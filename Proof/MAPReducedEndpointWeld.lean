import MAPLiveEndpointPacketIndexedV3
import MAPFinalSelectableWeld
import APFullSupportCommonHeightShortIntervalConnector
import MAPPacketIndexedFarBudgetConsumerV2
import MAPSourceFacingCertifiedEndpointAlignmentWeld
import KoukTheorem113MAPRangeToCorrectedTail

/-!
# Reduced live MAP endpoint

The primitive twisted-Mangoldt theorem and the corrected full-support explicit
formula tail are premise-free.  This file therefore exposes only the three
MAP-level analytic inputs that remain on the shortest packet-indexed route.
-/

namespace MAPReducedEndpointWeld

open PrimePairEndpoints
open MAPFixedScaleAPZeroRoute
open MAPSubmissionRouteOptimizer
open MAPDynamicHBTermwiseBudgetConstructorV3

noncomputable section

/-- The three surviving MAP-level analytic obligations. -/
structure ReducedAnalyticLeavesV3 : Prop where
  weightedZeroMass : APWeightedZeroMassLogSaving
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  dynamicFarBudget : UniformDynamicV3TermwiseFarBudget

/-- The common packet endpoint accepts either dynamic decomposition once its
actual packet budget has been proved.  In particular, the refined decomposition
need not imply the stronger original termwise budget. -/
structure ReducedPacketAnalyticLeaves : Prop where
  weightedZeroMass : APWeightedZeroMassLogSaving
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  packetFarBudget :
    MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget

theorem certifiedMAPEndpoint_of_reducedPacketLeaves
    (h : ReducedPacketAnalyticLeaves) : CertifiedMAPEndpoint := by
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    _root_.MAPAPFullSupportCommonHeightShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
      h.weightedZeroMass
      _root_.KoukTheorem113MAPRangeToCorrectedTail.certifiedCorrectedAPExplicitFormulaTailFamilySquare
  have hFar : MAPMRTCorollary53Source.MAPFarSourceReduction 1 1 :=
    _root_.MAPPacketIndexedFarBudgetConsumerV2.mapFarSourceReduction_one_of_uniformPacketIndexedPaddedFarBudget
      h.packetFarBudget
  exact
    _root_.MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
      MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi
      hAP h.mapLambdaHardRange hFar

/-- All other inputs on the packet-indexed MAP route are already certified. -/
theorem certifiedMAPEndpoint_of_reducedLeavesV3
    (h : ReducedAnalyticLeavesV3) : CertifiedMAPEndpoint := by
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    _root_.MAPAPFullSupportCommonHeightShortIntervalConnector.simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
        h.weightedZeroMass
        _root_.KoukTheorem113MAPRangeToCorrectedTail.certifiedCorrectedAPExplicitFormulaTailFamilySquare
  have hPacket :
      MAPPacketIndexedFarBudgetConsumerV2.UniformPacketIndexedPaddedFarBudget :=
    uniformPacketIndexedPaddedFarBudget_of_dynamicV3Termwise h.dynamicFarBudget
  have hFar : MAPMRTCorollary53Source.MAPFarSourceReduction 1 1 :=
    _root_.MAPPacketIndexedFarBudgetConsumerV2.mapFarSourceReduction_one_of_uniformPacketIndexedPaddedFarBudget hPacket
  exact
    _root_.MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
        MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi
        hAP h.mapLambdaHardRange hFar

/-- Deterministic endpoint processing is complete: with the certified
twisted-Mangoldt theorem, the final endpoint is equivalent to local MAP. -/
theorem certifiedMAPEndpoint_iff_allCenterLocalMAP :
    CertifiedMAPEndpoint ↔ AllCenterLocalMAP :=
  _root_.MAPFinalSelectableWeld.certifiedMAPEndpoint_iff_allCenterLocalMAP_of_uniformTwistedMangoldtPsi
      MAPPrimitiveTwistedMangoldtCertified.uniformTwistedMangoldtPsi

end
end MAPReducedEndpointWeld

#print axioms MAPReducedEndpointWeld.certifiedMAPEndpoint_of_reducedLeavesV3
#print axioms MAPReducedEndpointWeld.certifiedMAPEndpoint_of_reducedPacketLeaves
#print axioms MAPReducedEndpointWeld.certifiedMAPEndpoint_iff_allCenterLocalMAP
