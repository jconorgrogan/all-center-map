import APRegularNearAppendixBAdapter
import JutilaEquation17RangeSplit
import JutilaTheoremOneFiniteClosure
import PostA5HighStripSplitReductionFromFourthMoment
import APRegularNearCGLSelectedP53AppendixBAdapter
import JutilaGappedFixedModulusAggregateP53Adapter
import PrincipalZetaHuxley1972CorrectedTerminalSource
import PrincipalZetaHuxley1972ZeroFreeFromHighGap
import MontgomeryNeededLowStripBridge
import APPrimitiveRegularHighGapSourceLeaves
import DetectorStructuredFromBudgetedDirect
import PrincipalZetaStructuredDensity
import PrincipalZetaStructuredSplitFromFourthMoment
import PrincipalZetaFourthMomentFromDyadicAFE
import PrincipalHighOrdinateDetectorBudgetProof

/-!
# Exact source weld for the weighted AP zero mass

This file records two honest stopping points for equation (2.7).

The first theorem is the shortest live interface: compact density, Jutila's
eventual `eta = 1/10` estimate, and the primitive regular high-ordinate gap.
The second theorem opens the compact input through Montgomery, the principal
zeta branch, and Appendix A.4.  The Type-I coefficient is still required to
satisfy `IsNormalizedDetectorCoefficient`; no arbitrary-coefficient
Guth--Maynard statement is introduced.

`JutilaTheoremOneFiniteClosure` is used only for what it proves: deterministic
loss allocation and terminal quadratic absorption.  It does not currently
produce a live Jutila density proposition.  The earliest live unproved Jutila
declaration below is therefore kept visible rather than hidden behind a false
zero-argument wrapper.
-/

namespace MAPAPWeightedZeroMassSourceWeld

open MAPFixedScaleAPZeroRoute MAPAPWeightedZeroMassIntegration
open MAPAPRegularNearLogSaving MAPAPRegularNearAppendixBAdapter
open MAPKhaleAppendixBSource MAPJutilaEquation17RangeSplit
open CGLCompactStripDensityConstructor CGLDetectorStructuredLargeValue
open MAPJutilaGappedFixedModulusAggregateP53Adapter
open MAPJutilaGappedCollarSelectedP53Adapter
open MAPAPRegularNearCGLSelectedP53AppendixBAdapter
open MAPPrincipalZetaHuxley1972CorrectedTerminalSource
open MAPPrincipalZetaHuxley1972ZeroFreeFromHighGap
open MAPMontgomeryNeededLowStrip
open MAPAPPrimitiveRegularHighGapSourceLeaves
open CGLProofDAG
open MAPDetectorStructuredFromBudgetedDirect
open MAPPrincipalZetaStructuredDensity

noncomputable section

/-- The shortest exact analytic surface feeding the final weighted mass. -/
structure NearestAnalyticLeaves : Prop where
  compactDensity : MAPAPZeroDensityCert.PolylogConductorDensity
  jutilaOneTenth : JutilaEquation17OneTenthEventually
  primitiveRegularHighGap : PrimitiveRegularHighGap

/-- Earliest connected nonprincipal Jutila declaration on the live p.53
route.  The still deeper pointwise declaration
`JutilaP53IntegratedCorrelationEstimateAt` has no adapter to this eventual
fixed-modulus aggregate yet. -/
abbrev EarliestConnectedJutilaSource : Prop :=
  JutilaGappedFixedModulusAggregateP53Eventually

/-- All range partitions, exceptional-zero handling, and logarithmic
absorption after these three leaves are deterministic. -/
theorem apWeightedZeroMassLogSaving_of_nearestLeaves
    (h : NearestAnalyticLeaves) : APWeightedZeroMassLogSaving :=
  MAPAPExceptionalUnconditional.apWeightedZeroMassLogSaving_of_compact_regular
    (PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      h.compactDensity)
    (apRegularNearOneRangeMass_logSaving_of_oneTenth_eventual_and_high_gap
      h.jutilaOneTenth h.primitiveRegularHighGap)

/-- Conditional direct-CGL-v2 comparison surface.  The reduced structured
surface below is preferred because it does not assume the stronger all-modulus
CGL theorem. -/
structure DirectCGLv2Leaves : Prop where
  cglV2 : CGLMeshFormalization.CGLv2Theorem12AllCases
  jutilaAggregateP53 : JutilaGappedFixedModulusAggregateP53Eventually
  principalHuxleyTerminal : Huxley1972CorrectedTerminalAnalyticLeaves
  primitiveRegularHighGap : PrimitiveRegularHighGap

/-- The direct CGL-v2 route to equation (2.7).  The Jutila aggregate is only
restricted to the selected fixed-character rows, and the principal Huxley
leaf is converted using the already supplied high gap. -/
theorem apWeightedZeroMassLogSaving_of_directCGLv2Leaves
    (h : DirectCGLv2Leaves) : APWeightedZeroMassLogSaving := by
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    CGLMeshFormalization.fixedPrimitivePolylogDensity_of_cgl_v2 h.cglV2
  have hDensity : MAPAPZeroDensityCert.PolylogConductorDensity :=
    CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed
  have hCompact :=
    PostA5TypeICompactMassWeld.apCompactRangeMass_logSaving_of_polylogConductorDensity
      hDensity
  exact apWeightedZeroMassLogSaving_of_compact_cglv2_selectedP53_and_high_gap
    hCompact h.cglV2
    (jutilaGappedSelectedSystemP53_of_fixedModulusAggregate
      h.jutilaAggregateP53)
    (principalSelectedP53_of_correctedAnalyticLeaves_of_zeroFree
      (correctedEquation610ZeroFree_of_primitiveRegularHighGap
        h.primitiveRegularHighGap)
      h.principalHuxleyTerminal)
    h.primitiveRegularHighGap

/-- Preferred reduced source surface.  It stops before the all-modulus CGL
theorem, preserves the normalized detector coefficient in the recentered
Appendix-A.4 split, and opens the high-gap input to Ford plus the weakest
current Khale pointwise and zeta leaves. -/
structure ReducedStructuredLeaves : Prop where
  compactBase : FixedPrimitiveLowStripOrPrincipalDensity
  recenteredStructuredSplit : PostA5HighStripStructuredSplitReduction
  detectorStructuredLargeValue : DetectorStructuredThirtyThirteenLargeValue
  jutilaOneTenth : JutilaEquation17OneTenthEventually
  fordHurwitz : FordHurwitzEquation12 76.2 4.45
  khalePointwise : MAPKhaleLemma41PointwiseSource.KhaleLemma41FiniteSelectedEstimate
  zetaLogDerivative :
    MAPKhaleAppendixBLemma41NaturalScales.FordLemma31ZetaLogDerivativeBound

/-- Deterministic reduced-density weld.  No `CGLv2Theorem12AllCases` and no
arbitrary-coefficient Guth--Maynard premise occurs in this theorem. -/
theorem apWeightedZeroMassLogSaving_of_reducedStructuredLeaves
    (h : ReducedStructuredLeaves) : APWeightedZeroMassLogSaving := by
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    fixedPrimitivePolylogDensity_of_components h.compactBase
      (fixedPrimitiveHighStripDensity_of_structuredSplitReduction
        h.recenteredStructuredSplit h.detectorStructuredLargeValue)
  have hDensity : MAPAPZeroDensityCert.PolylogConductorDensity :=
    CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed
  exact apWeightedZeroMassLogSaving_of_nearestLeaves
    { compactDensity := hDensity
      jutilaOneTenth := h.jutilaOneTenth
      primitiveRegularHighGap :=
        primitiveRegularHighGap_of_pointwise_khale
          h.fordHurwitz h.khalePointwise h.zetaLogDerivative }

/-! ## Premise-minimized budgeted powered route

The following surface records the exact extra data needed after replacing the
shared `DetectorStructuredThirtyThirteenLargeValue` premise by the weaker
budgeted fixed-character powered bridge.  The nonprincipal and principal
post-A.5 splits remain separate: both consume the same large-value bridge, but
their Type-II ledgers are different.  Montgomery is needed only below the
`7/10` junction; the principal split supplies conductor one above it. -/

/-- Exact compact-density source bundle after opening the low/principal splice.

None of the four fields is inhabited here.  This structure is a source
boundary, not an unconditional density theorem. -/
structure BudgetedPostA5DensityLeaves : Prop where
  montgomeryLowStrip : MontgomeryNeededLowStripSource
  principalStructuredSplit : PrincipalPostA5StructuredSplitReduction
  nonprincipalStructuredSplit : PostA5HighStripStructuredSplitReduction
  budgetedPoweredLargeValue : BudgetedFixedCharacterPoweredLargeValueBridge

/-- All deterministic density welds after the budgeted powered estimate.

The single powered bridge is specialized once to the normalized detector
coefficient theorem and then reused in the principal and nonprincipal
post-A.5 branches. -/
theorem polylogConductorDensity_of_budgetedPostA5Leaves
    (h : BudgetedPostA5DensityLeaves) :
    MAPAPZeroDensityCert.PolylogConductorDensity := by
  have hStructured : DetectorStructuredThirtyThirteenLargeValue :=
    detectorStructuredThirtyThirteen_of_budgetedBridge
      h.budgetedPoweredLargeValue
  have hPrincipal :=
    principal_zeta_high_strip_density_of_structured_split
      h.principalStructuredSplit hStructured
  have hBase : FixedPrimitiveLowStripOrPrincipalDensity :=
    fixedPrimitiveLowStripOrPrincipalDensity_of_needed_montgomery_and_zeta
      h.montgomeryLowStrip hPrincipal
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    fixedPrimitivePolylogDensity_of_components hBase
      (fixedPrimitiveHighStripDensity_of_structuredSplitReduction
        h.nonprincipalStructuredSplit hStructured)
  exact CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed

/-- Optional finite-rank convenience bundle for the compact branch.

This surface is stronger than the source-faithful Ramachandra contour theorem:
it postulates a finite pointwise dyadic AFE with coefficients fixed before the
character and height.  When available, one such AFE supplies both post-A.5
Type-II inputs.  Its
principal specialization uses the already proved high-ordinate detector
budget; its nonprincipal specialization uses the recentered Appendix-A.4
split.  The budgeted powered bridge supplies the common Type-I large-value
input.  The preferred direct surface is the pair of discrete full-`L` fourth
moments in `APWeightedZeroMassDirectFourthMomentAdapter`. -/
structure BudgetedSharedAFEDensityLeaves : Prop where
  montgomeryLowStrip : MontgomeryNeededLowStripSource
  ramachandraDyadicAFE :
    BHPRamachandraMeanValueFromDyadicAFE.RamachandraLemma3To6AllCharacterDyadicAFE
  budgetedPoweredLargeValue : BudgetedFixedCharacterPoweredLargeValueBridge

/-- The shared AFE really does inhabit both distinct post-A.5 split fields.
This is the exact bridge from the compressed three-leaf source surface to the
four-field structural density surface above. -/
theorem budgetedPostA5DensityLeaves_of_sharedAFE
    (h : BudgetedSharedAFEDensityLeaves) : BudgetedPostA5DensityLeaves :=
  { montgomeryLowStrip := h.montgomeryLowStrip
    principalStructuredSplit :=
      MAPPrincipalZetaStructuredSplitFromFourthMoment.principalPostA5StructuredSplitReduction_of_principalFourthMoment
        MAPPrincipalHighOrdinateDetectorBudgetProof.principalHighOrdinateDetectorBudget_unconditional
        (MAPPrincipalZetaFourthMomentFromDyadicAFE.principalZetaDiscreteFourthMoment_of_dyadicAFE_raw
          h.ramachandraDyadicAFE)
    nonprincipalStructuredSplit :=
      PostA5HighStripSplitReductionFromFourthMoment.postA5HighStripStructuredSplitReduction_of_ramachandraDyadicAFE
        h.ramachandraDyadicAFE
    budgetedPoweredLargeValue := h.budgetedPoweredLargeValue }

/-- Compress the two exact post-A.5 split premises to their common dyadic AFE
source, then run the premise-minimized budgeted density weld. -/
theorem polylogConductorDensity_of_budgetedSharedAFELeaves
    (h : BudgetedSharedAFEDensityLeaves) :
    MAPAPZeroDensityCert.PolylogConductorDensity :=
  polylogConductorDensity_of_budgetedPostA5Leaves
    (budgetedPostA5DensityLeaves_of_sharedAFE h)

/-- Optional AFE-based source bundle for equation (2.7) through the budgeted
powered route.  These fields remain useful when an independent finite-rank
AFE is available, but they are not the minimal Ramachandra source surface. -/
structure BudgetedSharedAFEAnalyticLeaves : Prop where
  density : BudgetedSharedAFEDensityLeaves
  jutilaBulk : BulkEquation17OneTenthEventually
  jutilaCollar : CollarEquation17OneTenthEventually
  khaleAppendixB104 : AppendixBCorollary104

/-- Complete deterministic equation-(2.7) weld from the premise-minimized
budgeted source bundle.  This theorem is conditional because the fields of
`BudgetedSharedAFEAnalyticLeaves` are not inhabited in this module. -/
theorem apWeightedZeroMassLogSaving_of_budgetedSharedAFELeaves
    (h : BudgetedSharedAFEAnalyticLeaves) : APWeightedZeroMassLogSaving := by
  apply apWeightedZeroMassLogSaving_of_nearestLeaves
  exact
    { compactDensity := polylogConductorDensity_of_budgetedSharedAFELeaves h.density
      jutilaOneTenth := oneTenthEventually_of_bulk_and_collar
        h.jutilaBulk h.jutilaCollar
      primitiveRegularHighGap := primitiveRegularHighGap_of_appendixB104
        h.khaleAppendixB104 }

/-- The literal collar split agrees with the loss allocated by the certified
finite closure.  This is the exact point at which the finite Jutila algebra
meets the live range decomposition. -/
theorem splitDelta_eq_internalDelta_oneTenth :
    splitDelta = MAPJutilaTheoremOneFiniteClosure.internalDelta (1 / 10) := by
  norm_num [splitDelta, MAPJutilaTheoremOneFiniteClosure.internalDelta]

/-- Ranked expanded leaves for the requested source route.

The order is dependency order inside the compact branch, followed by the two
Jutila ranges and Khale's literal `q >= 3` corollary.  The first four fields
feed the Montgomery/zeta base and Appendix-A.4 high strip; the structured
large-value field applies only to coefficients carrying the certified
`IsNormalizedDetectorCoefficient` provenance. -/
structure ExpandedAnalyticLeaves : Prop where
  montgomeryLowStrip : MontgomeryNeededLowStripSource
  principalZetaHighStrip : ∀ eta : ℝ, 0 < eta →
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T sigma : ℝ), T₀ ≤ T →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
          (DirichletZeros.dirichletZeroCount
              (1 : DirichletCharacter ℂ 1) sigma T : ℝ) ≤
            C * Real.rpow T
              (MAPGuthMaynard.densityCoeff * (1 - sigma) + eta)
  ramachandraDyadicAFE :
    BHPRamachandraMeanValueFromDyadicAFE.RamachandraLemma3To6AllCharacterDyadicAFE
  detectorStructuredLargeValue : DetectorStructuredThirtyThirteenLargeValue
  jutilaBulk : BulkEquation17OneTenthEventually
  jutilaCollar : CollarEquation17OneTenthEventually
  khaleAppendixB104 : AppendixBCorollary104

/-- Deterministically reduce the expanded source surface to the nearest three
live obligations. -/
theorem nearestAnalyticLeaves_of_expanded
    (h : ExpandedAnalyticLeaves) : NearestAnalyticLeaves := by
  have hLow : FixedPrimitiveLowStripOrPrincipalDensity :=
    fixedPrimitiveLowStripOrPrincipalDensity_of_needed_montgomery_and_zeta
      h.montgomeryLowStrip h.principalZetaHighStrip
  have hSplit : PostA5HighStripStructuredSplitReduction :=
    PostA5HighStripSplitReductionFromFourthMoment.postA5HighStripStructuredSplitReduction_of_ramachandraDyadicAFE
      h.ramachandraDyadicAFE
  have hFixed : CGLPolylogBypass.FixedPrimitivePolylogDensity :=
    fixedPrimitivePolylogDensity_of_components hLow
      (fixedPrimitiveHighStripDensity_of_structuredSplitReduction
        hSplit h.detectorStructuredLargeValue)
  have hDensity : MAPAPZeroDensityCert.PolylogConductorDensity :=
    CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target hFixed
  exact
    { compactDensity := hDensity
      jutilaOneTenth := oneTenthEventually_of_bulk_and_collar
        h.jutilaBulk h.jutilaCollar
      primitiveRegularHighGap := primitiveRegularHighGap_of_appendixB104
        h.khaleAppendixB104 }

/-- Complete source-facing equation-(2.7) weld.  Every implication after the
seven displayed published-source leaves is compiled deterministic Lean. -/
theorem apWeightedZeroMassLogSaving_of_expandedLeaves
    (h : ExpandedAnalyticLeaves) : APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_nearestLeaves
    (nearestAnalyticLeaves_of_expanded h)

end
end MAPAPWeightedZeroMassSourceWeld

#check MAPJutilaP53AggregateCorrelationLeaf.JutilaP53IntegratedCorrelationEstimateAt
#check MAPJutilaGappedFixedModulusAggregateP53Adapter.JutilaGappedFixedModulusAggregateP53Eventually

#print axioms MAPAPWeightedZeroMassSourceWeld.splitDelta_eq_internalDelta_oneTenth
#print axioms MAPAPWeightedZeroMassSourceWeld.apWeightedZeroMassLogSaving_of_nearestLeaves
#print axioms MAPAPWeightedZeroMassSourceWeld.apWeightedZeroMassLogSaving_of_directCGLv2Leaves
#print axioms MAPAPWeightedZeroMassSourceWeld.apWeightedZeroMassLogSaving_of_reducedStructuredLeaves
#print axioms MAPAPWeightedZeroMassSourceWeld.polylogConductorDensity_of_budgetedPostA5Leaves
#print axioms MAPAPWeightedZeroMassSourceWeld.budgetedPostA5DensityLeaves_of_sharedAFE
#print axioms MAPAPWeightedZeroMassSourceWeld.polylogConductorDensity_of_budgetedSharedAFELeaves
#print axioms MAPAPWeightedZeroMassSourceWeld.apWeightedZeroMassLogSaving_of_budgetedSharedAFELeaves
#print axioms MAPAPWeightedZeroMassSourceWeld.nearestAnalyticLeaves_of_expanded
#print axioms MAPAPWeightedZeroMassSourceWeld.apWeightedZeroMassLogSaving_of_expandedLeaves
