import BHPCanonicalPrincipalSourceClosed
import MAPPolylogCor212SplitSelected

/-! # Direct Ramachandra-to-MAP selected-prefix constructor -/

namespace MAPPolylogCor212SplitRamachandra

open RamachandraTheorem6ShiftedStripSource
open MAPBHPCanonicalPrincipalSourceClosed
open MAPPolylogCor212SplitDefinitions
open MAPPolylogCor212SplitSelected

noncomputable section

/-- With the principal BHP contour now premise-free, Ramachandra Theorem 6 is
the sole analytic source parameter of the global MAP selected-prefix budget. -/
theorem selectedPrefixFourthMoment_of_ramachandra
    (hRamachandra : RamachandraTheorem6K2Source) :
    MAPPolylogSelectedPrefixFourthMomentLiteral :=
  selectedPrefixFourthMoment_of_canonical
    (canonicalAllCharacterSelectedFourthMomentLiteral_of_ramachandra
      hRamachandra)

end
end MAPPolylogCor212SplitRamachandra

#print axioms MAPPolylogCor212SplitRamachandra.selectedPrefixFourthMoment_of_ramachandra
