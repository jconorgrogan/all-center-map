import APDirectAlignedTailClosure
import APAlignedShortIntervalConnector

/-! # Exact direct AP endpoint from the one signed contour family -/

namespace MAPAPDirectAlignedShortInterval

open APFoundation MAPFixedScaleAPZeroRoute
open MAPAPDirectAlignedTailClosure MAPAPAlignedShortIntervalConnector

/-- Equation (2.7) and the joint signed left/horizontal contour estimate are
now the only AP analytic sources. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_leftHorizontal
    (h27 : APWeightedZeroMassLogSaving)
    (hLH : AlignedLeftHorizontalFamilySquare) :
    SimultaneousShortIntervalAP :=
  simultaneousShortIntervalAP_of_weightedZeroMass_of_alignedTail
    h27 (alignedTailFamilySquare_of_leftHorizontalFamilySquare hLH)

end MAPAPDirectAlignedShortInterval

#print axioms MAPAPDirectAlignedShortInterval.simultaneousShortIntervalAP_of_weightedZeroMass_of_leftHorizontal
