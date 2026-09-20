import MRTWholeLineEq83Parallel
import MRTWholeLinePacketHardCorrelation
import MRTPacketEquation82LargeThreshold

/-!
# Whole-line MRT equation (82) from equations (83) and (84)

The near band is controlled by the unrestricted equation-(83) energy theorem;
the far band is the already-certified whole-line two-IBP correlation estimate.
The intermediate band is absorbed by the large-threshold Cauchy envelope.
-/

namespace MAPMRTWholeLineEq83ParallelEquation82

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTPacketEquation82
open MAPMRTPacketEquation82LargeThreshold
open MAPMRTWholeLinePacketMemLp
open MAPMRTWholeLineEq83Parallel
open MAPMRTWholeLineHighCellEquation84
open MAPMRTWholeLinePacketHardCorrelation
open MAPMRTWholeLineOffDiagonalTwoIBP
open MAPMRTWholeLineOffDiagonalAmplitude

noncomputable section

def wholeLineEquation82Threshold : ℝ := 8 * Real.pi

def wholeLineOffDiagonalCoefficient
    (Bcut1 Bcut2 Bouter1 Bouter2 : ℝ) : ℝ :=
  4 * Real.exp 100 *
    wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2

set_option maxHeartbeats 800000 in
theorem source_packet_correlation_equation82_wholeLine
    {X H beta t t' D0 D1 D2 Bcut1 Bcut2 Bouter1 Bouter2 Dout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bcut1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ Bcut2)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bouter1)
    (houter''Bound : ∀ y, |outer'' y| ≤ Bouter2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'')
    (hcutoffInt : Integrable (fun y ↦ |cutoff y|))
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (houter'Int : Integrable (fun y ↦ |outer' y|))
    (hD0 : (∫ y : ℝ, |cutoff y|) ≤ D0)
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2)
    (hDout : (∫ y : ℝ, |outer' y|) ≤ Dout) :
    let C83 := wholeLineEquation83Constant
      D0 D1 D2 Bouter1 Bouter2 Dout
    let Coff := wholeLineOffDiagonalCoefficient
      Bcut1 Bcut2 Bouter1 Bouter2
    ‖packetCorrelation
        (fun r x ↦ sourceStationaryPacket X H x beta r cutoff outer)
        t t'‖ ≤
      ((1 + wholeLineEquation82Threshold) ^ 2 * C83 + 4 * Coff) *
        H / (|beta| * X) /
          (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  dsimp only
  let L : ℝ := wholeLineEquation82Threshold
  let C83 : ℝ := wholeLineEquation83Constant
    D0 D1 D2 Bouter1 Bouter2 Dout
  let Coff : ℝ := wholeLineOffDiagonalCoefficient
    Bcut1 Bcut2 Bouter1 Bouter2
  let J : ℝ → ℝ → ℂ := fun r x ↦
    sourceStationaryPacket X H x beta r cutoff outer
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hX : 0 < X := by linarith
  have hBcut1 : 0 ≤ Bcut1 :=
    (abs_nonneg (cutoff' 0)).trans (hcutoff'Bound 0)
  have hBcut2 : 0 ≤ Bcut2 :=
    (abs_nonneg (cutoff'' 0)).trans (hcutoff''Bound 0)
  have hBouter1 : 0 ≤ Bouter1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBouter2 : 0 ≤ Bouter2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hD0n : 0 ≤ D0 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff y))).trans hD0
  have hD1n : 0 ≤ D1 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hD1
  have hD2n : 0 ≤ D2 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff'' y))).trans hD2
  have hDoutn : 0 ≤ Dout :=
    (integral_nonneg (fun y ↦ abs_nonneg (outer' y))).trans hDout
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (hcutoffDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (hcutoffSecond y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (houterDeriv y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr
      (fun y ↦ (houterSecond y).continuousAt)
  have hL : 1 ≤ L := by
    unfold L wholeLineEquation82Threshold
    nlinarith [Real.pi_gt_three]
  have hC83 : 0 ≤ C83 := by
    unfold C83 wholeLineEquation83Constant
    dsimp only
    unfold wholeLineTrivialCoefficient wholeLineVdCCoefficient
      wholeLineFarCoefficient highCellEquation84BaseConstant
      outerScaleInflation curvatureFloor
    positivity
  have hCoff : 0 ≤ Coff := by
    unfold Coff wholeLineOffDiagonalCoefficient wholeLineTwoIBPConstant
      wholeLineAmplitudeFirstConstant wholeLineAmplitudeSecondConstant
    positivity
  have hJ : ∀ s, MemLp (J s) 2 := by
    intro s
    exact memLp_sourceStationaryPacket hX hHpos hcutoffCont houterCont
      hcutoffSupport houterSupport
  have h83 : ∀ s, (∫ x : ℝ, ‖J s x‖ ^ 2) ≤
      C83 * H / (|beta| * X) := by
    intro s
    exact source_packet_energy_equation83_wholeLine
      (X := X) (H := H) (beta := beta) (t := s)
      (D0 := D0) (D1 := D1) (D2 := D2)
      (B1 := Bouter1) (B2 := Bouter2) (Dout := Dout)
      hH hHalf hhard hcutoffSupport hcutoff'Support houterSupport
      hcutoffBound houterBound houter'Bound houter''Bound hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoff''Cont houter''Cont
      hcutoffInt hcutoff'Int hcutoff''Int houter'Int hD0 hD1 hD2 hDout
  have hoff : ∀ s s', L * (|beta| * H) ≤ |s - s'| →
      ‖packetCorrelation J s s'‖ ≤
        Coff * H ^ 2 / (X * |s - s'| ^ 2) := by
    intro s s' hsep
    have hf := norm_unrestrictedPacketCorrelation_le_hard
      (X := X) (H := H) (beta := beta) (s := s) (s' := s')
      (Bcut1 := Bcut1) (Bcut2 := Bcut2)
      (Bouter1 := Bouter1) (Bouter2 := Bouter2)
      (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
      (outer := outer) (outer' := outer') (outer'' := outer'')
      hX hHpos hhard (by
        simpa only [L, wholeLineEquation82Threshold, mul_assoc] using hsep)
      hBcut1 hBcut2 hBouter1 hBouter2 hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoffSupport hcutoff'Support
      hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
      houterSupport houter'Support houter''Support houterBound
      houter'Bound houter''Bound
    simpa [J, Coff, wholeLineOffDiagonalCoefficient] using hf
  simpa [J, L, C83, Coff] using
    (packet_correlation_equation82_large_threshold
      (X := X) (H := H) (beta := beta) (L := L)
      (C83 := C83) (Coff := Coff) (t := t) (t' := t')
      (J := J) hX hHpos hhard hL hC83 hCoff hJ h83 hoff)

#print axioms source_packet_correlation_equation82_wholeLine

end
end MAPMRTWholeLineEq83ParallelEquation82
