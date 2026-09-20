import PrincipalDiscreteFourthFromContinuous

/-!
# Weighted-zero density weld with certified fourth moments

This module discharges the principal and nonprincipal discrete fourth-moment
fields internally from the premise-free continuous Ramachandra theorem.  It
keeps the genuinely open Montgomery low-strip, powered `30/13`, Jutila, and
primitive high-gap inputs visible.
-/
namespace MAPAPWeightedZeroMassCertifiedFourthMomentWeld

open MAPAPWeightedZeroMassSourceWeld
open MAPAPWeightedZeroMassDirectFourthMomentAdapter
open MAPMontgomeryNeededLowStrip
open CGLProofDAG
open MAPAPRegularNearLogSaving
open MAPFixedScaleAPZeroRoute

noncomputable section

/-- The post-A.5 density bundle with both discrete full-`L` fourth moments
certified internally.  Exactly the low-strip Montgomery source and powered
large-value bridge remain as inputs. -/
theorem budgetedPostA5DensityLeaves_of_remainingSources
    (hmontgomery : MontgomeryNeededLowStripSource)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge) :
    BudgetedPostA5DensityLeaves :=
  budgetedPostA5DensityLeaves_of_directFourthMoments
    hmontgomery
    PrincipalDiscreteFourthFromContinuous.directDiscreteFourthMomentPair_proved
    hpowered

/-- The nearest exact compact-density object after installing the certified
principal and nonprincipal fourth moments. -/
theorem polylogConductorDensity_of_remainingSources
    (hmontgomery : MontgomeryNeededLowStripSource)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge) :
    MAPAPZeroDensityCert.PolylogConductorDensity :=
  polylogConductorDensity_of_budgetedPostA5Leaves
    (budgetedPostA5DensityLeaves_of_remainingSources hmontgomery hpowered)

/-- Source-facing bundle consumed by the terminal weighted-zero constructor.
The Jutila and primitive regular high-gap fields remain explicit because the
certified fourth moments do not discharge them. -/
theorem nearestAnalyticLeaves_of_remainingSources
    (hmontgomery : MontgomeryNeededLowStripSource)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge)
    (hjutila : JutilaEquation17OneTenthEventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap) :
    NearestAnalyticLeaves :=
  { compactDensity :=
      polylogConductorDensity_of_remainingSources hmontgomery hpowered
    jutilaOneTenth := hjutila
    primitiveRegularHighGap := hhighGap }

/-- Exact conditional weighted-zero endpoint after the certified fourth-moment
weld.  This does not assert weighted zero mass unconditionally: all four
remaining analytic sources occur in the theorem signature. -/
theorem apWeightedZeroMassLogSaving_of_remainingSources
    (hmontgomery : MontgomeryNeededLowStripSource)
    (hpowered : BudgetedFixedCharacterPoweredLargeValueBridge)
    (hjutila : JutilaEquation17OneTenthEventually)
    (hhighGap : MAPAPRegularNearAppendixBAdapter.PrimitiveRegularHighGap) :
    APWeightedZeroMassLogSaving :=
  apWeightedZeroMassLogSaving_of_nearestLeaves
    (nearestAnalyticLeaves_of_remainingSources
      hmontgomery hpowered hjutila hhighGap)

end
end MAPAPWeightedZeroMassCertifiedFourthMomentWeld

#print axioms MAPAPWeightedZeroMassCertifiedFourthMomentWeld.budgetedPostA5DensityLeaves_of_remainingSources
#print axioms MAPAPWeightedZeroMassCertifiedFourthMomentWeld.polylogConductorDensity_of_remainingSources
#print axioms MAPAPWeightedZeroMassCertifiedFourthMomentWeld.nearestAnalyticLeaves_of_remainingSources
#print axioms MAPAPWeightedZeroMassCertifiedFourthMomentWeld.apWeightedZeroMassLogSaving_of_remainingSources
