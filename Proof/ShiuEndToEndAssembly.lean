import ShiuClassIFinal
import ShiuClassIIIII

/-!
# Specialized Shiu end-to-end assembly

This module is deliberately downstream of `ShiuEndToEndScaffold` and the
class-specific files.  Keeping it separate avoids an import cycle: the
class-I final absorption uses the exact modulus/totient cancellation proved
in the scaffold, while this file inserts the resulting class-I theorem back
into the final four-class weld.
-/

namespace ShiuEndToEndAssembly

open ShiuEndToEnd

/-- Classes I, II, and III are now unconditional. The sufficient class-IV
Section-5 consequence is the only input left in the exact four-class weld. -/
theorem sectionFiveClassEstimates_of_certifiedI_II_III
    (hIV : ClassIV58Estimate) :
    SectionFiveClassEstimates :=
  sectionFiveClassEstimates_of_literalClasses
    ShiuClassIBound.certifiedClassI53Estimate
    ShiuClassIIIII.certifiedClassIIIII56Estimate hIV

/-- The natural specialized Shiu target with the already-certified class-I
branch inserted. Its premise is the explicit class-IV consequence, not a
renamed copy of the total progression conclusion. -/
theorem dyadicTauSquareShiuTarget_of_classIV
    (hIV : ClassIV58Estimate) :
    ShiuFoundation.DyadicTauSquareShiuTarget :=
  dyadicTauSquareShiuTarget_of_sectionFiveClassEstimates
    (sectionFiveClassEstimates_of_certifiedI_II_III hIV)

end ShiuEndToEndAssembly

#print axioms ShiuEndToEndAssembly.sectionFiveClassEstimates_of_certifiedI_II_III
#print axioms ShiuEndToEndAssembly.dyadicTauSquareShiuTarget_of_classIV
