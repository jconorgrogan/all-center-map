import MAPLiveEndpointWeld
import MAPDynamicHBTermwiseBudgetConstructorV3

/-!
# Live endpoint on the packet-indexed dynamic HB source

This replaces the invalid shared-short far-budget field by the source-faithful
dynamic V3 termwise budget.  All other minimal analytic leaves are unchanged.
-/

namespace MAPLiveEndpointPacketIndexedV3

open MAPLiveEndpointWeld
open PrimePairEndpoints
open MAPFixedScaleAPZeroRoute MAPAPWeightedZeroMassIntegration
open MAPMRTCorollary53Source
open MAPSubmissionRouteOptimizer
open MAPPrimitiveTwistedMangoldtSourceSplit
open MAPAPRegularNearHuxleyJutilaSourceAdapter
open MAPAPRegularNearHuxleyJutilaAppendixBAdapter
open MAPAPFullSupportCommonHeightShortIntervalConnector
open MAPDynamicHBTermwiseBudgetConstructorV3
open MAPPacketIndexedFarBudgetConsumerV2
open MAPFarSourceWeldScaffold
open MAPSourceFacingCertifiedEndpointAlignmentWeld
open MAPAPAlignedShortIntervalConnector MAPAPAlignedComponentSource
open KoukTheorem113MAPRangeToCorrectedTail

noncomputable section

structure MinimalAnalyticLeavesV3 : Prop where
  primitiveTwistedMangoldt : PrimitiveTwistedMangoldtSource
  compactRange : CompactRangeLogSaving
  huxleyFixedModulus : HuxleyFixedModulusEventually
  jutilaCollar : JutilaCollarOneTenthEventually
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  dynamicV3TermwiseFarBudget : UniformDynamicV3TermwiseFarBudget

structure SplitMinimalAnalyticLeavesV3 : Prop where
  primitiveNonprincipal : PrimitiveNonprincipalTwistedMangoldtPsi
  primitivePrincipalOne : PrimitivePrincipalOneTwistedMangoldtPsi
  compactRange : CompactRangeLogSaving
  huxleyFixedModulus : HuxleyFixedModulusEventually
  jutilaCollar : JutilaCollarOneTenthEventually
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  dynamicV3TermwiseFarBudget : UniformDynamicV3TermwiseFarBudget

theorem minimalAnalyticLeavesV3_of_split
    (h : SplitMinimalAnalyticLeavesV3) : MinimalAnalyticLeavesV3 :=
  { primitiveTwistedMangoldt :=
      primitiveTwistedMangoldtPsi_of_split
        h.primitiveNonprincipal h.primitivePrincipalOne
    compactRange := h.compactRange
    huxleyFixedModulus := h.huxleyFixedModulus
    jutilaCollar := h.jutilaCollar
    weakVKResidual := h.weakVKResidual
    mapLambdaHardRange := h.mapLambdaHardRange
    dynamicV3TermwiseFarBudget := h.dynamicV3TermwiseFarBudget }

theorem apWeightedZeroMassLogSaving_of_minimalLeavesV3
    (h : MinimalAnalyticLeavesV3) : APWeightedZeroMassLogSaving := by
  exact MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    h.compactRange
    (apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
      h.huxleyFixedModulus h.jutilaCollar h.weakVKResidual)

/-- Primary endpoint constructor using the arbitrary-order, packet-indexed
Heath--Brown source. -/
theorem certifiedMAPEndpoint_of_minimalLeavesV3
    (h : MinimalAnalyticLeavesV3) : CertifiedMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      h.primitiveTwistedMangoldt
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
      (apWeightedZeroMassLogSaving_of_minimalLeavesV3 h)
      certifiedCorrectedAPExplicitFormulaTailFamilySquare
  have hPacket : UniformPacketIndexedPaddedFarBudget :=
    uniformPacketIndexedPaddedFarBudget_of_dynamicV3Termwise
      h.dynamicV3TermwiseFarBudget
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformPacketIndexedPaddedFarBudget hPacket
  exact certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
    hSW hAP h.mapLambdaHardRange hFar

theorem certifiedMAPEndpoint_of_splitMinimalLeavesV3
    (h : SplitMinimalAnalyticLeavesV3) : CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_minimalLeavesV3 (minimalAnalyticLeavesV3_of_split h)

/-- Source-facing V3 endpoint with the weak-VK field descended to the exact
four-height Khale Lemma-6.2 rows.  This changes no endpoint field; it merely
certifies the full deterministic route from those narrower source leaves. -/
theorem certifiedMAPEndpoint_of_ford_lemma62V3
    (hPrimitive : PrimitiveTwistedMangoldtSource)
    (hCompact : CompactRangeLogSaving)
    (hHuxley : HuxleyFixedModulusEventually)
    (hJutila : JutilaCollarOneTenthEventually)
    (hFord : MAPKhaleAppendixBSource.FordHurwitzEquation12 76.2 4.45)
    (h62 :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma62FourNaturalScaleBounds)
    (hZeta :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma41ZetaLogDerivativeBound)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFar : UniformDynamicV3TermwiseFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_minimalLeavesV3
    { primitiveTwistedMangoldt := hPrimitive
      compactRange := hCompact
      huxleyFixedModulus := hHuxley
      jutilaCollar := hJutila
      weakVKResidual := weakVKResidualLeaves_of_ford_lemma62 hFord h62 hZeta
      mapLambdaHardRange := hHard
      dynamicV3TermwiseFarBudget := hFar }

end
end MAPLiveEndpointPacketIndexedV3

#print axioms MAPLiveEndpointPacketIndexedV3.certifiedMAPEndpoint_of_minimalLeavesV3
#print axioms MAPLiveEndpointPacketIndexedV3.certifiedMAPEndpoint_of_splitMinimalLeavesV3
#print axioms MAPLiveEndpointPacketIndexedV3.certifiedMAPEndpoint_of_ford_lemma62V3
