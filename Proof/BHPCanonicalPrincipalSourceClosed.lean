import BHPCanonicalPrincipalHorizontalClosed
import BHPCanonicalAllCharacterLiteral

/-!
# Premise-free principal BHP source and literal all-character weld

The principal contour source is now completely discharged.  The only analytic
source premise remaining in the selected all-character fourth moment is the
separately isolated Ramachandra Theorem 6 package.
-/

namespace MAPBHPCanonicalPrincipalSourceClosed

open MAPBHPCanonicalPrincipalHorizontalClosed
open MAPBHPCanonicalPrincipalPointwise
open MAPBHPCanonicalAllCharacterFromPrincipal
open MAPBHPCanonicalAllCharacterLiteral
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- No-`T ≤ X` principal pointwise source, now premise-free. -/
theorem canonicalPrincipalPointwiseSourceLiteral_proved :
    CanonicalPrincipalPointwiseSourceLiteral :=
  canonicalPrincipalPointwiseSourceLiteral_of_horizontal
    canonicalPrincipalHorizontalSource_proved

/-- Exact final weld: after the independently isolated Ramachandra Theorem 6
source is supplied, the all-character selected-prefix fourth moment follows
with global constants and the literal `card / X^2` Perron error. -/
theorem canonicalAllCharacterSelectedFourthMomentLiteral_of_ramachandra
    (hRamachandra : RamachandraTheorem6K2Source) :
    CanonicalAllCharacterSelectedFourthMomentLiteral :=
  canonicalAllCharacterSelectedFourthMomentLiteral_of_sources
    canonicalPrincipalPointwiseSourceLiteral_proved hRamachandra

end
end MAPBHPCanonicalPrincipalSourceClosed

#print axioms MAPBHPCanonicalPrincipalSourceClosed.canonicalPrincipalPointwiseSourceLiteral_proved
#print axioms MAPBHPCanonicalPrincipalSourceClosed.canonicalAllCharacterSelectedFourthMomentLiteral_of_ramachandra
