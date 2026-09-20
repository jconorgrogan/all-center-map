import RamachandraLongContourSourcePackage
import RamachandraShortContourSourcePackage
import RamachandraPrimitiveShiftedLongShortFinalAdapter
import MAPPolylogCor212SplitRamachandra
import MAPPolylogCor212SplitSampled

/-!
# Premise-free Ramachandra Theorem 6 source

This is the terminal weld of the independently certified long- and
short-contour packages.  The exported theorem has no analytic hypotheses.
-/

namespace RamachandraTheorem6Unconditional

open RamachandraLongContourSourcePackage
open RamachandraShortContourSourcePackage
open RamachandraPrimitiveShiftedLongShortFinalAdapter
open RamachandraTheorem6ShiftedStripSource
open MAPPolylogCor212SplitDefinitions
open MAPPolylogCor212SplitSampled

noncomputable section

/-- Ramachandra's all-character shifted fourth-moment theorem at `k = 2`,
assembled from the literal contour identity and the proved long/short source
moment packages. -/
theorem ramachandraTheorem6K2Source_proved :
    RamachandraTheorem6K2Source :=
  ramachandraTheorem6K2Source_of_longShortPackages
    primitiveShiftedLongSourcePieceContinuity
    primitiveShiftedShortSourcePieceContinuity
    primitiveShiftedLongSourceMomentPackage
    primitiveShiftedShortSourceMomentPackage

/-- Premise-free global selected-prefix fourth-moment source obtained from
the certified Ramachandra theorem and the already closed principal contour. -/
theorem mapPolylogSelectedPrefixFourthMomentLiteral_proved :
    MAPPolylogSelectedPrefixFourthMomentLiteral :=
  MAPPolylogCor212SplitRamachandra.selectedPrefixFourthMoment_of_ramachandra
    ramachandraTheorem6K2Source_proved

/-- Premise-free sampled Type-d1/d2 budget.  This is the source-faithful
finite consequence of Ramachandra currently available without postulating a
finite-rank approximation of the Mellin integrals. -/
theorem mapLowTypeD12SampledBudget_proved :
    MAPLowTypeD12SampledBudget :=
  sampledBudget_of_ramachandra ramachandraTheorem6K2Source_proved

end
end RamachandraTheorem6Unconditional

#print axioms RamachandraTheorem6Unconditional.ramachandraTheorem6K2Source_proved
#print axioms RamachandraTheorem6Unconditional.mapPolylogSelectedPrefixFourthMomentLiteral_proved
#print axioms RamachandraTheorem6Unconditional.mapLowTypeD12SampledBudget_proved
