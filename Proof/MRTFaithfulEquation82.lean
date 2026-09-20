import MRTFaithfulSmoothCutoffBudgets
import MRTWholeLineEq83ParallelEquation82

/-!
# Equation (82) for the single faithful Proposition-5.1 cutoff

This specializes the already-certified whole-line packet-correlation estimate
to the narrow cutoff used in equations (72), (74), (76), and (79).  The same
cutoff is used as the harmless compact outer cutoff.
-/

namespace MAPMRTFaithfulEquation82

open MeasureTheory
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
open MAPMRTProposition51HardBranch MAPMRTWholeLineEq83ParallelEquation82
open MAPMRTWholeLineEq83Parallel MAPMRTWholeLineOffDiagonalAmplitude

noncomputable section

/-- Fully concrete equation-(82) packet correlation bound for the faithful
cutoff.  All differentiability, support, supremum, and `L¹` budgets have been
discharged. -/
theorem faithful_source_packet_correlation_equation82
    {X H beta t t' : ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) :
    let D0 := ∫ y : ℝ, |faithfulCutoff y|
    let D1 := ∫ y : ℝ, |faithfulCutoffDeriv y|
    let D2 := ∫ y : ℝ, |faithfulCutoffSecond y|
    let B1 := faithfulCutoffDerivBudget
    let B2 := faithfulCutoffSecondBudget
    let C83 := wholeLineEquation83Constant D0 D1 D2 B1 B2 D1
    let Coff := wholeLineOffDiagonalCoefficient B1 B2 B1 B2
    ‖MAPMRTPacketEquation82.packetCorrelation
        (fun r x ↦ sourceStationaryPacket X H x beta r
          faithfulCutoff faithfulCutoff) t t'‖ ≤
      ((1 + wholeLineEquation82Threshold) ^ 2 * C83 + 4 * Coff) *
        H / (|beta| * X) /
          (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  dsimp only
  apply MAPMRTWholeLineEq83ParallelEquation82.source_packet_correlation_equation82_wholeLine
    (cutoff := faithfulCutoff)
    (cutoff' := faithfulCutoffDeriv)
    (cutoff'' := faithfulCutoffSecond)
    (outer := faithfulCutoff)
    (outer' := faithfulCutoffDeriv)
    (outer'' := faithfulCutoffSecond)
    hH hHalf hhard
  · intro y hy
    exact faithfulCutoff_zero_of_one_le hy
  · intro y hy
    exact faithfulCutoffDeriv_zero_of_one_le hy
  · intro y hy
    exact faithfulCutoffSecond_zero_of_one_le hy
  · intro y hy
    exact faithfulCutoff_zero_of_one_le hy
  · intro y hy
    exact faithfulCutoffDeriv_zero_of_one_le hy
  · intro y hy
    exact faithfulCutoffSecond_zero_of_one_le hy
  · exact abs_faithfulCutoff_le_one
  · exact abs_faithfulCutoffDeriv_le
  · exact abs_faithfulCutoffSecond_le
  · exact abs_faithfulCutoff_le_one
  · exact abs_faithfulCutoffDeriv_le
  · exact abs_faithfulCutoffSecond_le
  · exact faithfulCutoff_hasDerivAt
  · exact faithfulCutoffSecond_hasDerivAt
  · exact faithfulCutoff_hasDerivAt
  · exact faithfulCutoffSecond_hasDerivAt
  · exact faithfulCutoffSecond_continuous
  · exact faithfulCutoffSecond_continuous
  · simpa [Real.norm_eq_abs] using faithfulCutoff_integrable.norm
  · exact faithfulCutoffDeriv_abs_integrable
  · exact faithfulCutoffSecond_abs_integrable
  · exact faithfulCutoffDeriv_abs_integrable
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl
  · exact le_rfl

#print axioms faithful_source_packet_correlation_equation82

end
end MAPMRTFaithfulEquation82
