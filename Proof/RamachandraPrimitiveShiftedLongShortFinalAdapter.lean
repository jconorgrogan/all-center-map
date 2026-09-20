import RamachandraPrimitiveShiftedPackageAdapter

/-!
# Final deterministic weld from the literal long/short source packages

This module makes the last deterministic dependency explicit: once the two
literal contour moment packages and their continuity are constructed, the
primitive fourth moment and Ramachandra's all-character Theorem 6 source
statement follow through the certified principal split, conductor partition,
Euler factors, and logarithmic absorption.
-/

namespace RamachandraPrimitiveShiftedLongShortFinalAdapter

open Complex
open RamachandraPrimitiveShiftedContourReduction
open RamachandraPrimitiveShiftedHighLowWeld
open RamachandraPrimitiveShiftedPackageAdapter
open RamachandraTheorem6ShiftedStripSource

noncomputable section

/-- The complete deterministic weld.  Its hypotheses are lower, literal
long/short contour data; no fourth-moment conclusion appears among them. -/
theorem ramachandraTheorem6K2Source_of_longShortPackages
    (hlongCont : PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedLongContour psi T sigma t))
    (hshortCont : PrimitiveShiftedSourcePieceContinuity
      (fun psi T sigma t => primitiveShiftedShortContour psi T sigma t))
    (hlongBound : PrimitiveShiftedSourceMomentPackage
      primitiveFamilyLongContourSecondMoment)
    (hshortBound : PrimitiveShiftedSourceMomentPackage
      primitiveFamilyShortContourSecondMoment) :
    RamachandraTheorem6K2Source :=
  ramachandraTheorem6K2Source_of_exists_highNonprincipalConstruction
    (highNonprincipalConstructionPackage_of_longShort
      hlongCont hshortCont hlongBound hshortBound)

end
end RamachandraPrimitiveShiftedLongShortFinalAdapter

#print axioms RamachandraPrimitiveShiftedLongShortFinalAdapter.ramachandraTheorem6K2Source_of_longShortPackages
