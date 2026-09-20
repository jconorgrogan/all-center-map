import GuthMaynardLemma295ExactMAFE
import GuthMaynardHeathBrownCoreFromPowerSeparatedJutila

/-! The literal coefficient-one Heath--Brown estimate from the proved
source-scale approximate functional equation and its deterministic bootstrap. -/

namespace GuthMaynardHeathBrownCertified

theorem heathBrownOneCoefficientCore :
    GuthMaynardHeathBrownMajorant.HeathBrownOneCoefficientCore :=
  GuthMaynardHeathBrownCoreFromPowerSeparatedJutila.heathBrownOneCoefficientCore_of_exactAFE
    GuthMaynardLemma295ExactMAFE.lemma295ApproximateFunctionalEquationExactM

end GuthMaynardHeathBrownCertified

#print axioms GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore
