import APWeightedZeroMassSourceWeld
import PrincipalHighOrdinateDetectorBudgetProof

/-!
# Direct fourth-moment adapter for the post-A.5 density split

This is the source-faithful replacement for the optional finite dyadic AFE
surface.  The two split consumers only require the principal and primitive
nonprincipal discrete fourth-moment consequences.  A holomorphic sampling
theorem may construct these directly from the continuous Ramachandra source
without first producing a pointwise finite-rank AFE.
-/

namespace MAPAPWeightedZeroMassDirectFourthMomentAdapter

open MAPAPWeightedZeroMassSourceWeld
open MAPPrincipalZetaStructuredSplitFromFourthMoment
open MAPPrincipalHighOrdinateDetectorBudgetProof
open PostA5HighStripSplitReductionFromFourthMoment
open FixedCharacterFourthMomentFromAFE

noncomputable section

/-- The exact two full-`L` discrete moments needed by the principal and
nonprincipal post-A.5 consumers. -/
structure DirectDiscreteFourthMomentPair : Prop where
  principal : PrincipalZetaDiscreteFourthMoment
  nonprincipal : NonprincipalFixedCharacterDiscreteFourthMoment

/-- Build the four-field post-A.5 density surface directly from its actual
discrete fourth-moment inputs, avoiding the stronger finite-rank AFE object. -/
theorem budgetedPostA5DensityLeaves_of_directFourthMoments
    (hmontgomery : MAPMontgomeryNeededLowStrip.MontgomeryNeededLowStripSource)
    (hfourth : DirectDiscreteFourthMomentPair)
    (hpowered : CGLProofDAG.BudgetedFixedCharacterPoweredLargeValueBridge) :
    BudgetedPostA5DensityLeaves :=
  { montgomeryLowStrip := hmontgomery
    principalStructuredSplit :=
      principalPostA5StructuredSplitReduction_of_principalFourthMoment
        principalHighOrdinateDetectorBudget_unconditional hfourth.principal
    nonprincipalStructuredSplit :=
      postA5HighStripStructuredSplitReduction_of_nonprincipalFourthMoment
        hfourth.nonprincipal
    budgetedPoweredLargeValue := hpowered }

/-- Direct compact-density consequence of the two sampled full-`L` moments. -/
theorem polylogConductorDensity_of_directFourthMoments
    (hmontgomery : MAPMontgomeryNeededLowStrip.MontgomeryNeededLowStripSource)
    (hfourth : DirectDiscreteFourthMomentPair)
    (hpowered : CGLProofDAG.BudgetedFixedCharacterPoweredLargeValueBridge) :
    MAPAPZeroDensityCert.PolylogConductorDensity :=
  polylogConductorDensity_of_budgetedPostA5Leaves
    (budgetedPostA5DensityLeaves_of_directFourthMoments
      hmontgomery hfourth hpowered)

end
end MAPAPWeightedZeroMassDirectFourthMomentAdapter

#print axioms MAPAPWeightedZeroMassDirectFourthMomentAdapter.budgetedPostA5DensityLeaves_of_directFourthMoments
#print axioms MAPAPWeightedZeroMassDirectFourthMomentAdapter.polylogConductorDensity_of_directFourthMoments
