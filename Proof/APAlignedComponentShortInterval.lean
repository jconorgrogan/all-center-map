import APAlignedShortIntervalConnector
import APAlignedComponentSource

/-! # Exact AP endpoint from the six aligned contour components -/

namespace MAPAPAlignedComponentShortInterval

open APFoundation MAPFixedScaleAPZeroRoute
open MAPAPAlignedShortIntervalConnector MAPAPAlignedComponentSource

/-- Literal equation (2.7) and the six aligned window-component estimate are
the exact remaining sources for the simultaneous AP theorem. -/
theorem simultaneousShortIntervalAP_of_weightedZeroMass_of_components
    (h27 : APWeightedZeroMassLogSaving)
    (hcomponents : AlignedComponentFamilySquare) :
    SimultaneousShortIntervalAP :=
  simultaneousShortIntervalAP_of_weightedZeroMass_of_alignedTail
    h27 (alignedTailFamilySquare_of_componentFamilySquare hcomponents)

end MAPAPAlignedComponentShortInterval

#print axioms MAPAPAlignedComponentShortInterval.simultaneousShortIntervalAP_of_weightedZeroMass_of_components
