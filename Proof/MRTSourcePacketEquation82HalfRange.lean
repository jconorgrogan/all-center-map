import MRTSourcePacketEquation83HalfRange
import MRTPacketEquation82LargeThreshold

/-!
# MRT equation (82) after the proved half-range equations (84) and (83)

Only the distinct-frequency two-integration-by-parts estimate remains as an
input.  Its large threshold is retained literally, and the intermediate band
is absorbed by `packet_correlation_equation82_large_threshold`.
-/

namespace MAPMRTSourcePacketEquation82HalfRange

open MeasureTheory Set
open MAPMRTSourcePacketSupport
open MAPMRTPacketEquation83
open MAPMRTPacketEquation82
open MAPMRTPacketEquation82LargeThreshold
open MAPMRTSourcePacketEquation83HalfRange

noncomputable section

theorem source_packet_correlation_equation82_halfRange
    {X H beta eta t t' D1 D2 B1 B2 L Coff : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
    (hL : 1 ≤ L) (hCoff : 0 ≤ Coff)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'') (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2)
    (hoff : ∀ s s', L * (|beta| * H) ≤ |s - s'| →
      ‖packetCorrelation
          (fun r x ↦ sourceRestrictedPacket X H beta r cutoff outer x)
          s s'‖ ≤ Coff * H ^ 2 / (X * |s - s'| ^ 2)) :
    let C84 := equation84HalfRangeConstant D1 D2 B1 B2
    let Dout := ∫ y : ℝ, |outer' y|
    let Dinflated := D1 + C84 / (10 * Real.exp 50)
    let C83 := 16 * Real.pi * packetPointwiseConstant Dinflated Dout ^ 2 /
      Real.exp (-100)
    ‖packetCorrelation
        (fun r x ↦ sourceRestrictedPacket X H beta r cutoff outer x)
        t t'‖ ≤
      ((1 + L) ^ 2 * C83 + 4 * Coff) * H / (|beta| * X) /
        (1 + |t - t'| / (|beta| * H)) ^ 2 := by
  dsimp
  let C84 : ℝ := equation84HalfRangeConstant D1 D2 B1 B2
  let Dout : ℝ := ∫ y : ℝ, |outer' y|
  let Dinflated : ℝ := D1 + C84 / (10 * Real.exp 50)
  let C83 : ℝ := 16 * Real.pi * packetPointwiseConstant Dinflated Dout ^ 2 /
    Real.exp (-100)
  let J : ℝ → ℝ → ℂ := fun r x ↦
    sourceRestrictedPacket X H beta r cutoff outer x
  have hX : 0 < X := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have hJ : ∀ s, MemLp (J s) 2 := by
    intro s
    exact memLp_sourceRestrictedPacket hcutoffCont houterCont houterSupport
  have h83 : ∀ s, (∫ x : ℝ, ‖J s x‖ ^ 2) ≤
      C83 * H / (|beta| * X) := by
    intro s
    exact source_packet_energy_equation83_halfRange
      (X := X) (H := H) (beta := beta) (eta := eta) (t := s)
      (D1 := D1) (D2 := D2) (B1 := B1) (B2 := B2)
      hH hHalf hhard hetaPos hetaHard hcutoffSupport hcutoff'Support
      houterSupport houter'Support hcutoffBound houterBound houter'Bound
      houter''Bound hcutoffDeriv hcutoffSecond houterDeriv houterSecond
      hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
  have hC83 : 0 ≤ C83 := by unfold C83; positivity
  exact packet_correlation_equation82_large_threshold
    hX hHpos hhard hL hC83 hCoff hJ h83 hoff

#print axioms source_packet_correlation_equation82_halfRange

end
end MAPMRTSourcePacketEquation82HalfRange
