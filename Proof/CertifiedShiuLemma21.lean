import ShiuEndToEndAssembly
import ShiuClassIVFinal
import PaperLemma21ShiuWeld

/-!
# No-premise specialized Shiu and manuscript Lemma 2.1

This is the final public assembly module. The class-specific files prove
source-faithful sufficient Section-5 consequences; `ShiuEndToEndAssembly` joins them through the
exact four-class partition; `PaperLemma21ShiuWeld` transports the resulting
specialized Shiu theorem into the manuscript's mixed-mean Lemma 2.1.
-/

namespace ShiuFinalCertification

/-- The literal three-branch Section-5 package, with Classes I--IV all
discharged and no theorem-valued premise.  This exposes the completed
class-by-class argument before the final Shiu summation. -/
theorem certifiedSectionFiveClassEstimates :
    ShiuEndToEnd.SectionFiveClassEstimates :=
  ShiuEndToEndAssembly.sectionFiveClassEstimates_of_certifiedI_II_III
    ShiuClassIVBound.certifiedClassIV58Estimate

/-- The specialized dyadic Shiu theorem, with no theorem-valued premise. -/
theorem certifiedDyadicTauSquareShiuTarget :
    ShiuFoundation.DyadicTauSquareShiuTarget :=
  ShiuEndToEnd.dyadicTauSquareShiuTarget_of_sectionFiveClassEstimates
    certifiedSectionFiveClassEstimates

/-- The literal manuscript Lemma 2.1, now inhabited from the certified Shiu
chain and with no theorem-valued premise. -/
theorem certifiedPaperMixedMeanLemma21 (c : ℝ) (a k : ℕ) :
    MixedMeanMajorantWeld.PaperMixedMeanLemma21 c a k :=
  MAPMixedMeanCompletion.paperMixedMeanLemma21_of_dyadicTauSquareShiuTarget
    certifiedDyadicTauSquareShiuTarget c a k

end ShiuFinalCertification

#print axioms ShiuFinalCertification.certifiedSectionFiveClassEstimates
#print axioms ShiuFinalCertification.certifiedDyadicTauSquareShiuTarget
#print axioms ShiuFinalCertification.certifiedPaperMixedMeanLemma21
