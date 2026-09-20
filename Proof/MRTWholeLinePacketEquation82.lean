import MRTWholeLinePacketEquation83
import MRTWholeLinePacketHardCorrelation
import MRTPacketEquation82LargeThreshold

/-!
# Source-faithful whole-line MRT equation (82)

This composes the unrestricted equation-(83) energy with the exact hard
correlation bound at separation `8π|β|H`.  The intermediate band is absorbed
by the large-threshold Cauchy envelope.
-/

namespace MAPMRTWholeLinePacketEquation82

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTWholeLinePacketMemLp MAPMRTWholeLinePacketEquation83
open MAPMRTWholeLinePacketHardCorrelation MAPMRTPacketEquation82
open MAPMRTPacketEquation82LargeThreshold
open MAPMRTWholeLineOffDiagonalTwoIBP
open MAPMRTWholeLineOffDiagonalAmplitude

noncomputable section

/-- Explicit coefficient in the whole-line equation-(82) bound. -/
def wholeLineEquation82Constant
    (D0 D1 D2 Dout Bcut1 Bcut2 Bouter1 Bouter2 : ℝ) : ℝ :=
  let C83 := wholeLineEquation83Constant
    D0 D1 D2 Dout Bouter1 Bouter2
  let Coff := 4 * Real.exp 100 *
    wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2
  (1 + 8 * Real.pi) ^ 2 * C83 + 4 * Coff

/-- MRT equation (82) for the literal unrestricted packet. -/
theorem source_packet_correlation_equation82_wholeLine
    {X H beta eta t t' D0 D1 D2 Dout Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
    (hBcut1 : 0 ≤ Bcut1) (hBcut2 : 0 ≤ Bcut2)
    (hBouter1 : 0 ≤ Bouter1) (hBouter2 : 0 ≤ Bouter2)
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
    ‖packetCorrelation
        (fun r x ↦ sourceStationaryPacket X H x beta r cutoff outer)
        t t'‖ ≤
      wholeLineEquation82Constant D0 D1 D2 Dout
          Bcut1 Bcut2 Bouter1 Bouter2 * H / (|beta| * X) /
        (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  let J : ℝ → ℝ → ℂ := fun r x ↦
    sourceStationaryPacket X H x beta r cutoff outer
  let C83 : ℝ := wholeLineEquation83Constant
    D0 D1 D2 Dout Bouter1 Bouter2
  let Coff : ℝ := 4 * Real.exp 100 *
    wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hX : 0 < X := by linarith
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have hJ : ∀ s, MemLp (J s) 2 := by
    intro s
    exact memLp_sourceStationaryPacket hX hHpos hcutoffCont houterCont
      hcutoffSupport houterSupport
  have h83 : ∀ s, (∫ x : ℝ, ‖J s x‖ ^ 2) ≤
      C83 * H / (|beta| * X) := by
    intro s
    exact source_packet_energy_equation83_wholeLine
      (X := X) (H := H) (beta := beta) (eta := eta) (t := s)
      (D0 := D0) (D1 := D1) (D2 := D2) (Dout := Dout)
      (B1 := Bouter1) (B2 := Bouter2)
      hH hHalf hhard hetaPos hetaHard hcutoffSupport hcutoff'Support
      houterSupport hcutoffBound houterBound houter'Bound houter''Bound
      hcutoffDeriv hcutoffSecond houterDeriv houterSecond
      hcutoff''Cont houter''Cont hcutoffInt hcutoff'Int hcutoff''Int
      houter'Int hD0 hD1 hD2 hDout
  have hC83 : 0 ≤ C83 := by
    unfold C83 wholeLineEquation83Constant
    positivity
  have hCoff : 0 ≤ Coff := by
    have htwo : 0 ≤
        wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
      unfold wholeLineTwoIBPConstant wholeLineAmplitudeFirstConstant
        wholeLineAmplitudeSecondConstant
      positivity
    unfold Coff
    positivity
  have hL : (1 : ℝ) ≤ 8 * Real.pi := by
    have hp : 3 < Real.pi := Real.pi_gt_three
    nlinarith
  have hoff : ∀ s s', (8 * Real.pi) * (|beta| * H) ≤ |s - s'| →
      ‖packetCorrelation J s s'‖ ≤ Coff * H ^ 2 / (X * |s - s'| ^ 2) := by
    intro s s' hsep
    have hh := norm_unrestrictedPacketCorrelation_le_hard
      (X := X) (H := H) (beta := beta) (s := s) (s' := s')
      (Bcut1 := Bcut1) (Bcut2 := Bcut2)
      (Bouter1 := Bouter1) (Bouter2 := Bouter2)
      (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
      (outer := outer) (outer' := outer') (outer'' := outer'')
      hX hHpos hhard (by simpa [mul_assoc] using hsep)
      hBcut1 hBcut2 hBouter1 hBouter2
      hcutoffCont hcutoff'Cont hcutoff''Cont houterCont houter'Cont
      houter''Cont hcutoffDeriv hcutoffSecond houterDeriv houterSecond
      hcutoffSupport hcutoff'Support hcutoff''Support hcutoffBound
      hcutoff'Bound hcutoff''Bound houterSupport houter'Support
      houter''Support houterBound houter'Bound houter''Bound
    simpa [J, Coff] using hh
  exact packet_correlation_equation82_large_threshold
    hX hHpos hhard hL hC83 hCoff hJ h83 hoff

#print axioms source_packet_correlation_equation82_wholeLine

end
end MAPMRTWholeLinePacketEquation82
