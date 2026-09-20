import MRTSourcePacketEquation84HalfRange
import MRTPacketEquation83

/-!
# MRT equation (83) from the proved half-range equation (84)

This module closes the constant mismatch between the literal half-range
equation-(84) theorem and the equation-(83) energy argument.  The combined
pointwise constant is passed explicitly; no comparison with the earlier
first-derivative-only constant is assumed.
-/

namespace MAPMRTSourcePacketEquation83HalfRange

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTSourcePacketSupport
open MAPMRTPacketEquation83
open MAPMRTSourcePacketEquation84HalfRange

noncomputable section

/-- The explicit constant proved by the sharp-window/collar split in (84). -/
def equation84HalfRangeConstant (D1 D2 B1 B2 : ℝ) : ℝ :=
  (1500 + 24 * (10 * (1 + B1) * (1 + D1)) +
      4 * (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)) +
    (150000 + 24 * (300 + 6 * B1 + 3 * D1) +
      4 * (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2))

/-- Equation (83) with equation (84) discharged throughout the literal source
range `H ≤ X/2`.  Inflating the first-derivative budget is only an algebraic
way of feeding the already proved general equation-(83) theorem its actual
pointwise constant; it does not change any cutoff hypothesis. -/
theorem source_packet_energy_equation83_halfRange
    {X H beta eta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hhard : 1 < |beta| * H)
    (hetaPos : 0 < eta) (hetaHard : eta < 1 / 100)
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
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let C84 := equation84HalfRangeConstant D1 D2 B1 B2
    let Dout := ∫ y : ℝ, |outer' y|
    let Dinflated := D1 + C84 / (10 * Real.exp 50)
    (∫ x : ℝ,
      ‖sourceRestrictedPacket X H beta t cutoff outer x‖ ^ 2) ≤
      (16 * Real.pi * packetPointwiseConstant Dinflated Dout ^ 2 /
          Real.exp (-100)) * H / (|beta| * X) := by
  dsimp
  let C84 : ℝ := equation84HalfRangeConstant D1 D2 B1 B2
  let Dout : ℝ := ∫ y : ℝ, |outer' y|
  let Dinflated : ℝ := D1 + C84 / (10 * Real.exp 50)
  have hX : 0 < X := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have houter'Compact : HasCompactSupport outer' := by
    apply HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-1 : ℝ) 1) isCompact_Icc
    intro y hy
    by_contra hmem
    have habs : 1 ≤ |y| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hmem
      rcases hmem with hylt | hygt
      · rw [abs_of_nonpos (by linarith : y ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ y)]
        linarith
    exact hy (houter'Support y habs)
  have houter'Int : Integrable (fun y ↦ |outer' y|) :=
    houter'Cont.abs.integrable_of_hasCompactSupport houter'Compact.abs
  have hD1n : 0 ≤ D1 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff' y))).trans hD1
  have hD2n : 0 ≤ D2 :=
    (integral_nonneg (fun y ↦ abs_nonneg (cutoff'' y))).trans hD2
  have hB1 : 0 ≤ B1 := (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hB2 : 0 ≤ B2 := (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hC84 : 0 ≤ C84 := by
    unfold C84 equation84HalfRangeConstant
    positivity
  have hDout : 0 ≤ Dout := by
    unfold Dout
    exact integral_nonneg (fun y ↦ abs_nonneg (outer' y))
  have hDinflated : D1 ≤ Dinflated := by
    unfold Dinflated
    have : 0 ≤ C84 / (10 * Real.exp 50) := by positivity
    linarith
  have hC84le : C84 ≤ packetPointwiseConstant Dinflated Dout := by
    unfold Dinflated packetPointwiseConstant
    have he : 0 < Real.exp 50 := Real.exp_pos 50
    have hbase : 0 ≤ 800 * Real.exp 50 +
        10 * Real.exp 50 * (101 + D1 + Dout) := by positivity
    field_simp [ne_of_gt he]
    nlinarith
  have hLnonneg : 0 ≤ packetPointwiseConstant Dinflated Dout :=
    hC84.trans hC84le
  have h84 : ∀ x,
      4 * max (|beta| * H) (X / H) ≤ |t / (2 * Real.pi) + beta * x| →
      ‖sourceRestrictedPacket X H beta t cutoff outer x‖ ≤
        packetPointwiseConstant Dinflated Dout * (X / H) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by
    intro x hxcenter
    by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
    · simp only [sourceRestrictedPacket, Set.indicator_of_mem hx]
      have hhalf := norm_sourceStationaryPacket_equation84_halfRange
        hX hHpos hHalf hx.1 hx.2 hxcenter hcutoffSupport hcutoff'Support
        houterSupport houter'Support hcutoffBound houterBound houter'Bound
        houter''Bound hcutoffDeriv hcutoffSecond houterDeriv houterSecond
        hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
      have hscale : 0 ≤ (X / H) /
          |t / (2 * Real.pi) + beta * x| ^ 2 := by positivity
      have hhalf' :
          ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
            C84 * (X / H) /
              |t / (2 * Real.pi) + beta * x| ^ 2 := by
        simpa [C84, equation84HalfRangeConstant] using hhalf
      calc
        ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
            C84 * ((X / H) /
              |t / (2 * Real.pi) + beta * x| ^ 2) := by
          calc
            _ ≤ C84 * (X / H) /
                |t / (2 * Real.pi) + beta * x| ^ 2 := hhalf'
            _ = _ := by ring
        _ ≤ packetPointwiseConstant Dinflated Dout * ((X / H) /
              |t / (2 * Real.pi) + beta * x| ^ 2) :=
          mul_le_mul_of_nonneg_right hC84le hscale
        _ = _ := by ring
    · have hz : sourceRestrictedPacket X H beta t cutoff outer x = 0 := by
        simp [sourceRestrictedPacket, hx]
      rw [hz, norm_zero]
      exact div_nonneg
        (mul_nonneg hLnonneg (div_nonneg hX.le hHpos.le)) (sq_nonneg _)
  exact source_packet_energy_equation83_of_equation84
    (X := X) (H := H) (beta := beta) (eta := eta) (t := t)
    (Dcut := Dinflated) (Dout := Dout)
    hH hHalf hhard hetaPos hetaHard hcutoffSupport houterSupport
    hcutoffBound houterBound hcutoffDeriv houterDeriv hcutoff'Cont
    houter'Cont hcutoff'Int houter'Int (hD1.trans hDinflated) le_rfl h84

#print axioms source_packet_energy_equation83_halfRange

end
end MAPMRTSourcePacketEquation83HalfRange
