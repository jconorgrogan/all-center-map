import MAPEndpointSourceWeld
import MAPLambdaHardRangeConnector
import APDirectAlignedShortInterval

/-!
# Source-facing MAP endpoint with the MAP-specific MRT hard range

This is the narrowest current release constructor.  It exposes the joint
signed left/horizontal aligned contour family and the literal far-source
budget, while replacing generic MRT Proposition 5.1 by the hard-range estimate
for the one Mangoldt input actually used by MAP.
-/

namespace MAPLambdaEndpointSourceWeld

open PrimePairEndpoints
open MAPFixedScaleAPZeroRoute MAPAPAlignedShortIntervalConnector
open MAPAPAlignedTailToRemainderTransfer MAPMRTCorollary53Source
open MAPFarSourceWeldScaffold MAPSubmissionRouteOptimizer
open MAPAPDirectAlignedTailClosure MAPAPDirectAlignedShortInterval

noncomputable section

/-- The AP contour input is the literal joint signed left/horizontal family
square.  Alignment, the character projector, exact floor support, maximal
square summation, and every deterministic remainder term are supplied by the
compiled direct AP route. -/
theorem fullUnconditionalMAPEndpoint_of_mapLambda_primitive_sourceLeaves
    (hPrimitive :
      ∀ A B : ℕ, ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
          ∀ X : ℝ, X0 ≤ X →
          ∀ q : ℕ, 1 ≤ q →
            (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
          ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
            ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
                MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
              C * X / (Real.log X) ^ A)
    (h27 : APWeightedZeroMassLogSaving)
    (hAPContour : AlignedLeftHorizontalFamilySquare)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    FullUnconditionalMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      hPrimitive
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_leftHorizontal
      h27 hAPContour
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget hFarBudget
  exact fullUnconditionalMAPEndpoint_of_mapLambdaHard_activeLeaves
    hSW hAP hHard hFar

end
end MAPLambdaEndpointSourceWeld

#print axioms MAPLambdaEndpointSourceWeld.fullUnconditionalMAPEndpoint_of_mapLambda_primitive_sourceLeaves
