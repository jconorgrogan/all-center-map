import MAPSourceFacingCertifiedEndpointAlignmentWeld
import MontgomeryLowStripBridge
import CGLDetectorStructuredLargeValue
import PostA5TypeICompactMassWeld
import APRegularNearAppendixBAdapter
import PrimitiveTwistedMangoldtSourceSplit
import CGLv2PolylogConductorDensity
import APRegularNearHuxleyJutilaAppendixBAdapter
import APRegularNearCGLJutilaAppendixBAdapter
import APRegularNearCGLGappedJutilaAppendixBAdapter
import APRegularNearCGLSelectedP53AppendixBAdapter
import JutilaGappedFixedModulusAggregateP53Adapter
import PostA5HighStripSplitReductionFromFourthMoment
import PrimitiveTwistedMangoldtCertified
import PrimitiveTwistedMangoldtCertifiedFromKhaleSources
import APFullSupportCommonHeightShortIntervalConnector
import KoukTheorem113ToCorrectedTail
import KoukTheorem113MAPRangeToCorrectedTail
import PrincipalZetaHuxley1972Theorem19Adapter
import PrincipalZetaHuxley1972TerminalProofReduction
import PrincipalZetaHuxley1972CorrectedTerminalSource
import PrincipalZetaHuxley1972ZeroFreeFromHighGap
import APPrimitiveRegularHighGapFromFordRaw

/-!
# Live zero-argument MAP endpoint weld

This module is the deterministic integration boundary for the current MAP
proof.  It records the exact analytic leaves still needed by the live
consumer and supplies two constructors:

* `certifiedMAPEndpoint_of_minimalLeaves` accepts the narrowest statements
  consumed by the endpoint;
* `certifiedMAPEndpoint_of_structuredDensityLeaves` expands the compact zero
  mass into its present Montgomery, principal-zeta, structured detector,
  Jutila, and Khale source leaves.

No analytic statement is asserted here.  Once premise-free inhabitants of
the named leaves are imported, the final zero-argument theorem is a one-line
application of either constructor.
-/

namespace MAPLiveEndpointWeld

open PrimePairEndpoints DirichletZeros
open MAPFixedScaleAPZeroRoute MAPAPWeightedZeroMassIntegration
open MAPAPRegularNearLogSaving MAPAPRegularNearAppendixBAdapter
open MAPKhaleAppendixBSource
open MAPAPDirectAlignedTailClosure
open MAPMRTCorollary53Source MAPFarSourceWeldScaffold
open MAPSubmissionRouteOptimizer
open MAPPrimitiveTwistedMangoldtSourceSplit
open MAPAPRegularNearHuxleyJutilaSourceAdapter
open MAPAPRegularNearHuxleyJutilaAppendixBAdapter
open MAPAPRegularNearCGLJutilaAppendixBAdapter
open MAPAPRegularNearCGLGappedJutilaAppendixBAdapter
open MAPJutilaGappedCollarSourceAdapter
open MAPAPRegularNearCGLSelectedP53AppendixBAdapter
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPJutilaGappedFixedModulusAggregateP53Adapter
open MAPPrimitiveTwistedMangoldtCertified
open MAPPrimitiveTwistedMangoldtCertifiedFromKhaleSources
open MAPAPFullSupportCommonHeightShortIntervalConnector
open MAPKoukTheorem113ToCorrectedTail
open KoukTheorem113MAPRangeToCorrectedTail
open MAPPrincipalZetaHuxley1972Theorem19Adapter
open MAPPrincipalZetaHuxley1972TerminalProofReduction
open MAPPrincipalZetaHuxley1972CorrectedTerminalSource
open MAPPrincipalZetaHuxley1972ZeroFreeFromHighGap
open CGLCompactStripDensityConstructor
open CGLDetectorStructuredLargeValue

noncomputable section

/-- The exact primitive-character input accepted by the deterministic
imprimitive-character adapter.  This is strictly weaker than assuming the
already packaged all-character Siegel--Walfisz conclusion. -/
abbrev PrimitiveTwistedMangoldtSource : Prop :=
  ∀ A B : ℕ, ∃ C X0 : ℝ,
    0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
      ∀ q : ℕ, 1 ≤ q →
        (q : ℝ) ≤ (Real.log X) ^ B →
      ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
      ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
        ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
            MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
          C * X / (Real.log X) ^ A

/-- The compact-strip mass estimate actually consumed by equation (2.7).
Keeping this named prevents a proof of a stronger density theorem from being
mistaken for part of the endpoint interface. -/
abbrev CompactRangeLogSaving : Prop :=
  ∀ K A epsilon : ℝ,
    0 < K → 0 < A → 0 < epsilon → epsilon ≤ 1 / 10 →
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧
      ∀ X : ℝ, X0 ≤ X →
        apCompactRangeMass ⌊Real.rpow (Real.log X) K⌋₊ epsilon X
            (apZeroHeight epsilon X) ≤
          C * Real.rpow (Real.log X) (-A)

/-- The exact residual weak-VK information used by the primary endpoint.
This is only the primitive regular high-ordinate gap.  The conductor-one
Huxley zero-free alternative is now derived from the same gap plus the
certified compact zeta gap. -/
abbrev WeakVKResidualLeaves : Prop := PrimitiveRegularHighGap

/-- Appendix B remains one way to supply the residual interface, but is no
longer exposed by the primary six-field endpoint record. -/
theorem weakVKResidualLeaves_of_appendixB104
    (hKhale104 : AppendixBCorollary104) : WeakVKResidualLeaves :=
  primitiveRegularHighGap_of_appendixB104 hKhale104

/-- Preferred source-facing constructor for the residual collar.  The
bounded-height McCurley branch, packaged Appendix-B corollary, and invalid
printed common-height collapse are absent.  The literal four natural heights
are carried with their exact weighted correction. -/
theorem weakVKResidualLeaves_of_ford_naturalScales
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hNatural :
      MAPKhaleAppendixBFirstPartScaleCorrected.AppendixBLemma41TrigNaturalScales) :
    WeakVKResidualLeaves :=
  MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_naturalScales
    hFord hNatural

/-- Lowest current source-facing constructor for the residual collar.  The
five-term trigonometric/Euler-product positivity and the exact four-height
linear combination are certified.  The remaining Khale source is four
literal Lemma-6.2 upper bounds, plus the elementary real-axis zeta estimate;
Ford's Hurwitz estimate remains separate. -/
theorem weakVKResidualLeaves_of_ford_lemma62
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (h62 :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma62FourNaturalScaleBounds)
    (hZeta :
      MAPKhaleAppendixBLemma62NaturalScaleWeld.AppendixBLemma41ZetaLogDerivativeBound) :
    WeakVKResidualLeaves :=
  MAPAPPrimitiveRegularHighGapFromFordRaw.primitiveRegularHighGap_of_ford_lemma62
    hFord h62 hZeta

/-- Montgomery's exact closed low-strip family source. -/
abbrev MontgomeryClosedLowStripSource : Prop :=
  ∃ Czero : ℝ, 0 < Czero ∧
    ∀ (r : ℕ) [NeZero r] (T sigma : ℝ),
      2 ≤ T → 1 / 2 ≤ sigma → sigma ≤ 4 / 5 →
        (MAPAPZeroDensityCert.ambientZeroCountAtLevel r sigma T : ℝ) ≤
          Czero * Real.rpow ((r : ℝ) * T)
            (MAPMontgomeryLowStrip.inghamExponent sigma) *
            (Real.log ((r : ℝ) * T)) ^ 9

/-- The conductor-one high-strip density statement used at the unique
principal branch.  It is separate from the nonprincipal detector estimate. -/
abbrev PrincipalClosedHighStripSource : Prop :=
  ∀ eta : ℝ, 0 < eta →
    ∃ C T0 : ℝ, 0 < C ∧ 2 ≤ T0 ∧
      ∀ T sigma : ℝ, T0 ≤ T →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          (dirichletZeroCount
              (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
            C * Real.rpow T
              (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta)

/-- Exact endpoint surface after removing every deterministic bridge above
equation (2.7).  Huxley is used only below `279/280`, Jutila only on the
closed collar above it, and the zero-free input is only the exact primitive
regular high-ordinate gap consumed there. -/
structure MinimalAnalyticLeaves : Prop where
  primitiveTwistedMangoldt : PrimitiveTwistedMangoldtSource
  compactRange : CompactRangeLogSaving
  huxleyFixedModulus : HuxleyFixedModulusEventually
  jutilaCollar : JutilaCollarOneTenthEventually
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  literalPaddedFarBudget : UniformLiteralPaddedFarBudget

/-- Source-faithful form of the minimal endpoint with the unique primitive
principal character exposed.  The two branches are joined only by the
compiled finite-level case split. -/
structure SplitMinimalAnalyticLeaves : Prop where
  primitiveNonprincipal : PrimitiveNonprincipalTwistedMangoldtPsi
  primitivePrincipalOne : PrimitivePrincipalOneTwistedMangoldtPsi
  compactRange : CompactRangeLogSaving
  huxleyFixedModulus : HuxleyFixedModulusEventually
  jutilaCollar : JutilaCollarOneTenthEventually
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  literalPaddedFarBudget : UniformLiteralPaddedFarBudget

/-- The principal/nonprincipal primitive split inhabits the exact primitive
binder and changes no downstream analytic premise. -/
theorem minimalAnalyticLeaves_of_split
    (h : SplitMinimalAnalyticLeaves) : MinimalAnalyticLeaves :=
  { primitiveTwistedMangoldt :=
      primitiveTwistedMangoldtPsi_of_split
        h.primitiveNonprincipal h.primitivePrincipalOne
    compactRange := h.compactRange
    huxleyFixedModulus := h.huxleyFixedModulus
    jutilaCollar := h.jutilaCollar
    weakVKResidual := h.weakVKResidual
    mapLambdaHardRange := h.mapLambdaHardRange
    literalPaddedFarBudget := h.literalPaddedFarBudget }

/-- The compact, regular-near, and exceptional-near pieces give exactly the
weighted zero-mass estimate consumed by the AP short-interval weld. -/
theorem apWeightedZeroMassLogSaving_of_minimalLeaves
    (h : MinimalAnalyticLeaves) : APWeightedZeroMassLogSaving := by
  exact MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    h.compactRange
    (apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
      h.huxleyFixedModulus h.jutilaCollar h.weakVKResidual)

/-- Deterministic endpoint constructor on the narrowest live analytic
surface. -/
theorem certifiedMAPEndpoint_of_minimalLeaves
    (h : MinimalAnalyticLeaves) : CertifiedMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      h.primitiveTwistedMangoldt
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail
      (apWeightedZeroMassLogSaving_of_minimalLeaves h)
      certifiedCorrectedAPExplicitFormulaTailFamilySquare
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget
      h.literalPaddedFarBudget
  exact
    MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
      hSW hAP h.mapLambdaHardRange hFar

/-- Minimal endpoint constructor with the conductor-one prime number theorem
branch explicit. -/
theorem certifiedMAPEndpoint_of_splitMinimalLeaves
    (h : SplitMinimalAnalyticLeaves) : CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_minimalLeaves (minimalAnalyticLeaves_of_split h)

/-- Canonical full-support endpoint constructor.  The common-height explicit
formula retains `zeroSupport primitive 0 T`, and its energy is inserted before
the MAP near/far weld.  No selected positive-`sigma` contour field occurs. -/
theorem certifiedMAPEndpoint_of_fullSupportTail
    (hPrimitive : PrimitiveTwistedMangoldtSource)
    (h27 : APWeightedZeroMassLogSaving)
    (hTail : MAPAPCorrectedPaperEdgeTail.CorrectedAPExplicitFormulaTailFamilySquare)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      hPrimitive
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_correctedTail h27 hTail
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget hFarBudget
  exact
    MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
      hSW hAP hHard hFar

/-- Source-facing full-support constructor with the primitive
Siegel--Walfisz branch opened below Appendix B.104.  Only Ford's literal
Hurwitz-zeta estimate and Khale's raw first-part estimate are used for that
branch; a separate Appendix-B input may still be required by `h27`. -/
theorem certifiedMAPEndpoint_of_ford_raw_fullSupportTail
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (h27 : APWeightedZeroMassLogSaving)
    (hTail : MAPAPCorrectedPaperEdgeTail.CorrectedAPExplicitFormulaTailFamilySquare)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_fullSupportTail
    (primitiveTwistedMangoldtPsi_of_ford_raw hFord hRaw)
      h27 hTail hHard hFarBudget

/-- Universal-height Kouk 11.3 route.  This is a viable source interface and
will be preferred once its current zero-cutoff/real-endpoint contour weld is
closed.  The selected-height route below remains available independently. -/
theorem certifiedMAPEndpoint_of_kouk113Pointwise
    (hPrimitive : PrimitiveTwistedMangoldtSource)
    (h27 : APWeightedZeroMassLogSaving)
    (h113 : KoukTheorem113FullSupportPointwise)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_fullSupportTail hPrimitive h27
    (correctedAPExplicitFormulaTailFamilySquare_of_kouk113 h113)
      hHard hFarBudget

/-- Universal-height Kouk route with the primitive branch reduced directly
to Ford's literal estimate and Khale's raw first-part estimate. -/
theorem certifiedMAPEndpoint_of_ford_raw_kouk113Pointwise
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (h27 : APWeightedZeroMassLogSaving)
    (h113 : KoukTheorem113FullSupportPointwise)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_kouk113Pointwise
    (primitiveTwistedMangoldtPsi_of_ford_raw hFord hRaw)
      h27 h113 hHard hFarBudget

/-- Canonical source-facing constructor.  The Kouk remainder estimate and
paper-edge legality are supplied at the same selected common height. -/
theorem certifiedMAPEndpoint_of_kouk113SelectedCommonHeight
    (hPrimitive : PrimitiveTwistedMangoldtSource)
    (h27 : APWeightedZeroMassLogSaving)
    (h113 : KoukTheorem113SelectedCommonHeight)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_fullSupportTail hPrimitive h27
    (correctedAPExplicitFormulaTailFamilySquare_of_selectedCommonHeight h113)
      hHard hFarBudget

/-- Selected-common-height Kouk route with the primitive branch reduced
directly to Ford's literal estimate and Khale's raw first-part estimate. -/
theorem certifiedMAPEndpoint_of_ford_raw_kouk113SelectedCommonHeight
    (hFord : FordHurwitzEquation12 76.2 4.45)
    (hRaw :
      MAPKhaleAppendixBFirstPartAnalyticReduction.AppendixBFirstPartRawEstimate)
    (h27 : APWeightedZeroMassLogSaving)
    (h113 : KoukTheorem113SelectedCommonHeight)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_kouk113SelectedCommonHeight
    (primitiveTwistedMangoldtPsi_of_ford_raw hFord hRaw)
      h27 h113 hHard hFarBudget

/-- Expanded source surface for the preferred detector-structured compact
density route.  The arbitrary-coefficient Guth--Maynard theorem is not a
premise: only the literal detector coefficient and the source-faithful split
are required. -/
structure StructuredDensityAnalyticLeaves : Prop where
  montgomeryLowStrip : MontgomeryClosedLowStripSource
  principalHighStrip : PrincipalClosedHighStripSource
  ramachandraDyadicAFE :
    BHPRamachandraMeanValueFromDyadicAFE.RamachandraLemma3To6AllCharacterDyadicAFE
  structuredLargeValue : DetectorStructuredThirtyThirteenLargeValue
  huxleyFixedModulus : HuxleyFixedModulusEventually
  jutilaCollar : JutilaCollarOneTenthEventually
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  literalPaddedFarBudget : UniformLiteralPaddedFarBudget

/-- The structured detector leaves imply the exact compact-range logarithmic
saving without passing through an arbitrary-coefficient large-value theorem. -/
theorem compactRangeLogSaving_of_structuredDensityLeaves
    (h : StructuredDensityAnalyticLeaves) : CompactRangeLogSaving := by
  have hLow : FixedPrimitiveLowStripOrPrincipalDensity :=
    MAPMontgomeryLowStrip.fixedPrimitiveLowStripOrPrincipalDensity_of_montgomery_and_zeta
        h.montgomeryLowStrip h.principalHighStrip
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    CGLCompactStripDensityConstructor.fixedPrimitivePolylogDensity_of_components hLow
      (fixedPrimitiveHighStripDensity_of_structuredSplitReduction
        (PostA5HighStripSplitReductionFromFourthMoment.postA5HighStripStructuredSplitReduction_of_ramachandraDyadicAFE
          h.ramachandraDyadicAFE)
        h.structuredLargeValue)
  have hDensity : MAPAPZeroDensityCert.PolylogConductorDensity :=
    CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed
  exact
    PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      hDensity

/-- Fastest wall-clock source surface.  The exact CGL v2 all-cases theorem
already includes the low strip and compact strip.  The terminal collar asks
for Jutila's fixed-modulus aggregate nonprincipal row-system estimate and
restricts it deterministically to each character needed downstream.  The
conductor-one branch descends below Huxley's displayed equation (1.9) to the
corrected terminal classification/class-I/class-II leaves.  The Kouk source
is certified premise-free in the exact MAP height range. -/
structure CGLv2AnalyticLeaves : Prop where
  cglV2AllCases : CGLMeshFormalization.CGLv2Theorem12AllCases
  jutilaGappedFixedModulusAggregateP53 :
    JutilaGappedFixedModulusAggregateP53Eventually
  huxley1972CorrectedTerminalAnalyticLeaves :
    Huxley1972CorrectedTerminalAnalyticLeaves
  weakVKResidual : WeakVKResidualLeaves
  mapLambdaHardRange : MAPLambdaCorollary53HardRange
  literalPaddedFarBudget : UniformLiteralPaddedFarBudget

/-- Direct compact logarithmic saving from the exact CGL v2 theorem. -/
theorem compactRangeLogSaving_of_cglV2Leaves
    (h : CGLv2AnalyticLeaves) : CompactRangeLogSaving := by
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    CGLMeshFormalization.fixedPrimitivePolylogDensity_of_cgl_v2
      h.cglV2AllCases
  have hDensity : MAPAPZeroDensityCert.PolylogConductorDensity :=
    CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed
  exact
    PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      hDensity

/-- Primary submission constructor when CGL v2 itself is certified. -/
theorem certifiedMAPEndpoint_of_cglV2Leaves
    (h : CGLv2AnalyticLeaves) : CertifiedMAPEndpoint := by
  exact certifiedMAPEndpoint_of_fullSupportTail
      MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi
      (apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_and_high_gap
        (compactRangeLogSaving_of_cglV2Leaves h)
        h.cglV2AllCases
          (jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
            h.jutilaGappedFixedModulusAggregateP53)
          (principalSelectedP53_of_correctedAnalyticLeaves_of_zeroFree
            (correctedEquation610ZeroFree_of_primitiveRegularHighGap
              h.weakVKResidual)
            h.huxley1972CorrectedTerminalAnalyticLeaves)
          h.weakVKResidual)
      certifiedCorrectedAPExplicitFormulaTailFamilySquare
      h.mapLambdaHardRange h.literalPaddedFarBudget

/-- Deterministic endpoint constructor from the preferred expanded source
surface. -/
theorem certifiedMAPEndpoint_of_structuredDensityLeaves
    (h : StructuredDensityAnalyticLeaves) : CertifiedMAPEndpoint := by
  exact certifiedMAPEndpoint_of_fullSupportTail
      MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi
      (MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
        (compactRangeLogSaving_of_structuredDensityLeaves h)
        (apRegularNearOneRangeMass_logSaving_of_huxley_collar_and_high_gap
          h.huxleyFixedModulus h.jutilaCollar h.weakVKResidual))
      certifiedCorrectedAPExplicitFormulaTailFamilySquare
      h.mapLambdaHardRange h.literalPaddedFarBudget

end
end MAPLiveEndpointWeld

#print axioms MAPLiveEndpointWeld.apWeightedZeroMassLogSaving_of_minimalLeaves
#print axioms MAPLiveEndpointWeld.weakVKResidualLeaves_of_appendixB104
#print axioms MAPLiveEndpointWeld.weakVKResidualLeaves_of_ford_naturalScales
#print axioms MAPLiveEndpointWeld.weakVKResidualLeaves_of_ford_lemma62
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_minimalLeaves
#print axioms MAPLiveEndpointWeld.minimalAnalyticLeaves_of_split
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_splitMinimalLeaves
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_fullSupportTail
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_ford_raw_fullSupportTail
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_kouk113Pointwise
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_ford_raw_kouk113Pointwise
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_kouk113SelectedCommonHeight
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_ford_raw_kouk113SelectedCommonHeight
#print axioms MAPLiveEndpointWeld.compactRangeLogSaving_of_structuredDensityLeaves
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_structuredDensityLeaves
#print axioms MAPLiveEndpointWeld.compactRangeLogSaving_of_cglV2Leaves
#print axioms MAPLiveEndpointWeld.certifiedMAPEndpoint_of_cglV2Leaves
