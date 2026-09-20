import MRTFaithfulEquation82
import MRTWholeLineEquation81FromEquation82
import MRTMediumEq79ParallelMovingWindow

/-!
# Faithful equation (82) into the equation (81) Schur consumer

This packages the concrete equation-(82) constant and feeds it into the
first-principles equation-(81) source-scale theorem.  No cutoff parameter or
regularity premise remains.
-/

namespace MAPMRTFaithfulEquation81Weld

open MeasureTheory
open MAPMRTFaithfulSmoothCutoff MAPMRTFaithfulSmoothCutoffBudgets
open MAPMRTProposition51HardBranch MAPMRTMediumEq79Parallel
open MAPMRTEquation81Kernel MAPMRTEquation81AveragingBilinear
open MAPMRTWholeLineEquation81FromEquation82
open MAPMRTWholeLineEq83ParallelEquation82
open MAPMRTWholeLineEq83Parallel MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTWholeLineOffDiagonalTwoIBP
open MAPMRTWholeLineHighCellEquation84

noncomputable section

def faithfulEquation82D0 : ℝ := ∫ y : ℝ, |faithfulCutoff y|
def faithfulEquation82D1 : ℝ := ∫ y : ℝ, |faithfulCutoffDeriv y|
def faithfulEquation82D2 : ℝ := ∫ y : ℝ, |faithfulCutoffSecond y|

def faithfulEquation82Constant : ℝ :=
  let C83 := wholeLineEquation83Constant faithfulEquation82D0
    faithfulEquation82D1 faithfulEquation82D2 faithfulCutoffDerivBudget
    faithfulCutoffSecondBudget faithfulEquation82D1
  let Coff := wholeLineOffDiagonalCoefficient faithfulCutoffDerivBudget
    faithfulCutoffSecondBudget faithfulCutoffDerivBudget
    faithfulCutoffSecondBudget
  (1 + wholeLineEquation82Threshold) ^ 2 * C83 + 4 * Coff

def faithfulEquation82Scale (X H beta : ℝ) : ℝ :=
  faithfulEquation82Constant * H / (|beta| * X)

theorem faithfulEquation82Constant_nonneg : 0 ≤ faithfulEquation82Constant := by
  have hD0 : 0 ≤ faithfulEquation82D0 := by
    unfold faithfulEquation82D0
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hD1 : 0 ≤ faithfulEquation82D1 := by
    unfold faithfulEquation82D1
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hD2 : 0 ≤ faithfulEquation82D2 := by
    unfold faithfulEquation82D2
    exact integral_nonneg fun _ ↦ abs_nonneg _
  have hB1 : 0 ≤ faithfulCutoffDerivBudget :=
    faithfulCutoffDerivBudget_nonneg
  have hB2 : 0 ≤ faithfulCutoffSecondBudget :=
    faithfulCutoffSecondBudget_nonneg
  have hA1 : 0 ≤ wholeLineAmplitudeFirstConstant
      faithfulCutoffDerivBudget faithfulCutoffDerivBudget := by
    unfold wholeLineAmplitudeFirstConstant
    positivity
  have hA2 : 0 ≤ wholeLineAmplitudeSecondConstant
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget := by
    unfold wholeLineAmplitudeSecondConstant
    positivity
  have htwo : 0 ≤ wholeLineTwoIBPConstant
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget := by
    unfold wholeLineTwoIBPConstant
    positivity
  have hCoff : 0 ≤ wholeLineOffDiagonalCoefficient
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget
      faithfulCutoffDerivBudget faithfulCutoffSecondBudget := by
    unfold wholeLineOffDiagonalCoefficient
    positivity
  have hC83 : 0 ≤ wholeLineEquation83Constant faithfulEquation82D0
      faithfulEquation82D1 faithfulEquation82D2 faithfulCutoffDerivBudget
      faithfulCutoffSecondBudget faithfulEquation82D1 := by
    unfold wholeLineEquation83Constant outerScaleInflation curvatureFloor
    positivity
  unfold faithfulEquation82Constant
  dsimp only
  positivity

theorem faithfulEquation82Scale_nonneg
    {X H beta : ℝ} (hX : 0 < X) (hH : 0 ≤ H) :
    0 ≤ faithfulEquation82Scale X H beta := by
  unfold faithfulEquation82Scale
  exact div_nonneg
    (mul_nonneg faithfulEquation82Constant_nonneg hH)
    (mul_nonneg (abs_nonneg beta) hX.le)

/-- The concrete faithful equation-(82) estimate in the literal kernel form
consumed by Schur. -/
theorem faithful_packetCorrelation_le_equation81Kernel
    {X H beta t t' : ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H) :
    ‖MAPMRTPacketEquation82.packetCorrelation
      (fun r x ↦ sourceStationaryPacket X H x beta r
        faithfulCutoff faithfulCutoff) t t'‖ ≤
      faithfulEquation82Scale X H beta *
        equation81Kernel (|beta| * H) t t' := by
  have h := MAPMRTFaithfulEquation82.faithful_source_packet_correlation_equation82
    (X := X) (H := H) (beta := beta) (t := t) (t' := t') hH hHalf hhard
  dsimp only at h
  simpa [faithfulEquation82D0, faithfulEquation82D1,
    faithfulEquation82D2, faithfulEquation82Constant,
    faithfulEquation82Scale, equation81Kernel] using h

/-- Equation (81) for the faithful packet and an arbitrary measurable finite
weight.  The only remaining data are the weight's elementary measurability and
pointwise finiteness of its moving average. -/
theorem faithful_packetCorrelationBilinear_source_scale
    {X H beta : ℝ} {F : ℝ → ENNReal}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hF : Measurable F)
    (hAfin : ∀ x, equation81Average (|beta| * H) F x ≠ ⊤) :
    ENNReal.ofReal (|beta| * H) *
        packetCorrelationBilinear
          (fun r x ↦ sourceStationaryPacket X H x beta r
            faithfulCutoff faithfulCutoff) F ≤
      18 * ENNReal.ofReal (faithfulEquation82Scale X H beta) *
        (∫⁻ x : ℝ, (equation81Average (|beta| * H) F x) ^ 2) := by
  have hX : 0 < X := by linarith
  have hR : 0 < |beta| * H := by
    have : 0 < |beta| := by
      by_contra hb
      have : beta = 0 := abs_eq_zero.mp (le_antisymm (le_of_not_gt hb) (abs_nonneg _))
      subst beta
      norm_num at hhard
    positivity
  exact packetCorrelationBilinear_source_scale hR
    (faithfulEquation82Scale_nonneg hX (le_trans zero_le_one hH)) hF hAfin
    (fun t t' ↦ faithful_packetCorrelation_le_equation81Kernel
      hH hHalf hhard)

#print axioms faithful_packetCorrelation_le_equation81Kernel
#print axioms faithful_packetCorrelationBilinear_source_scale

end
end MAPMRTFaithfulEquation81Weld
