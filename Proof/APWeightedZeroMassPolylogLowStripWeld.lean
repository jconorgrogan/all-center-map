import APWeightedZeroMassCertifiedFourthMomentWeld
import MontgomeryPolylogLowStripConsumer

/-! The weighted-zero consumer accepts the polylogarithmic-conductor low strip
directly. Fixed logarithmic losses in a proved low-strip estimate can therefore
be absorbed before this interface; the classical log^9 theorem is unnecessary.
All still-open analytic inputs remain explicit. -/

namespace MAPAPWeightedZeroMassPolylogLowStripWeld

open MAPMontgomeryPolylogLowStripConsumer
open MAPAPWeightedZeroMassSourceWeld
open MAPDetectorStructuredFromBudgetedDirect
open MAPPrincipalZetaStructuredDensity
open MAPPrincipalZetaStructuredSplitFromFourthMoment
open MAPPrincipalHighOrdinateDetectorBudgetProof
open PostA5HighStripSplitReductionFromFourthMoment
open CGLCompactStripDensityConstructor
open CGLDetectorStructuredLargeValue
open CGLProofDAG

noncomputable section

theorem polylogConductorDensity_of_lowStrip_and_powered
    (hlow : PolylogLowStripDensity)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge) :
    MAPAPZeroDensityCert.PolylogConductorDensity := by
  have hfourth := PrincipalDiscreteFourthFromContinuous.directDiscreteFourthMomentPair_proved
  have hstructured := detectorStructuredThirtyThirteen_of_budgetedBridge hpowered
  have hprincipalSplit :=
    principalPostA5StructuredSplitReduction_of_principalFourthMoment
      principalHighOrdinateDetectorBudget_unconditional hfourth.principal
  have hnonprincipalSplit :=
    postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment hfourth.nonprincipal
  have hprincipal :=
    principal_zeta_high_strip_density_of_structured_split hprincipalSplit hstructured
  have hbase := fixedPrimitiveLowStripOrPrincipalDensity_of_polylog_and_zeta hlow hprincipal
  exact CGLPolylogBypass.fixedPrimitivePolylogDensity_to_project_target
    (fixedPrimitivePolylogDensity_of_components hbase
      (fixedPrimitiveHighStripDensity_of_structuredSplitReduction hnonprincipalSplit hstructured))

theorem apWeightedZeroMassLogSaving_of_lowStrip_and_remainingSources
    (hlow : PolylogLowStripDensity)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge)
    (hjutila : MAPAPRegularNearLogSaving.JutilaEquation17OneTenthEventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap) :
    MAPFixedScaleAPZeroRoute.APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_nearestLeaves
    { compactDensity := polylogConductorDensity_of_lowStrip_and_powered hlow hpowered
      jutilaOneTenth := hjutila
      primitiveRegularHighGap := hhighGap }

end
end MAPAPWeightedZeroMassPolylogLowStripWeld

#print axioms MAPAPWeightedZeroMassPolylogLowStripWeld.polylogConductorDensity_of_lowStrip_and_powered
#print axioms MAPAPWeightedZeroMassPolylogLowStripWeld.apWeightedZeroMassLogSaving_of_lowStrip_and_remainingSources
