import MRTWholeLinePacketFubini

/-!
# Square integrability of the unrestricted MRT source packet

The source removes the sharp `x` cutoff before Cauchy--Schwarz.  This module
records that the resulting whole-line packet is still in `L²`: the outer
`w` cutoff and the translated arithmetic cutoff force a fixed compact
`x` support.  This is the source-correct `MemLp` interface for equation (82).
-/

namespace MAPMRTWholeLinePacketMemLp

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch MAPMRTVanDerCorput
open MAPMRTSourcePacketSupport
open MAPMRTWholeLinePacketFubini

noncomputable section

private theorem cutoff_center_eq_zero_of_x_outside_compact
    {X H x w : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : |w| ≤ 100)
    (hx : x ∉ Set.Icc (-(X * Real.exp 100 + H))
      (X * Real.exp 100 + H)) :
    cutoff ((X * Real.exp w - x) / H) = 0 := by
  apply hcutoffSupport
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · have hnum : H ≤ X * Real.exp w - x := by
      have hcenter : 0 ≤ X * Real.exp w := by positivity
      have hM : 0 ≤ X * Real.exp 100 := by positivity
      linarith
    have hq : 1 ≤ (X * Real.exp w - x) / H := by
      rw [le_div_iff₀ hH]
      simpa only [one_mul] using hnum
    rw [abs_of_nonneg (by linarith)]
    exact hq
  · have hew : Real.exp w ≤ Real.exp 100 :=
      Real.exp_le_exp.mpr ((abs_le.mp hw).2)
    have hcenter : X * Real.exp w ≤ X * Real.exp 100 := by gcongr
    have hnum : X * Real.exp w - x ≤ -H := by linarith
    have hq : (X * Real.exp w - x) / H ≤ -1 := by
      rw [div_le_iff₀ hH]
      linarith
    rw [abs_of_nonpos (hq.trans (by norm_num))]
    linarith

/-- The unrestricted packet vanishes outside a compact interval depending
only on the two literal cutoff supports. -/
theorem sourceStationaryPacket_eq_zero_outside_compact
    {X H beta t x : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (hx : x ∉ Set.Icc (-(X * Real.exp 100 + H))
      (X * Real.exp 100 + H)) :
    sourceStationaryPacket X H x beta t cutoff outer = 0 := by
  unfold sourceStationaryPacket
  rw [show (∫ w : ℝ,
      additivePhase (stationaryPacketPhase X beta t w) *
        sourcePacketAmplitude X H x cutoff outer w) =
      ∫ _w : ℝ, (0 : ℂ) by
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : |w| ≤ 100
    · have hcut := cutoff_center_eq_zero_of_x_outside_compact hX hH
        hcutoffSupport hw hx
      simp [sourcePacketAmplitude, hcut]
    · have habs : 100 ≤ |w| := le_of_not_ge hw
      have hout : outer (w / 100) = 0 := by
        apply houterSupport
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
        exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 100)).2 (by
          simpa using habs)
      simp [sourcePacketAmplitude, hout]]
  simp

/-- The square norm of the source-correct whole-line packet is integrable. -/
theorem integrable_norm_sourceStationaryPacket_sq
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    Integrable (fun x : ℝ ↦
      ‖sourceStationaryPacket X H x beta t cutoff outer‖ ^ 2) := by
  let S : Set ℝ := Set.Icc (-(X * Real.exp 100 + H))
    (X * Real.exp 100 + H)
  let f : ℝ → ℝ := fun x ↦
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ^ 2
  have hfCont : Continuous f := by
    unfold f
    exact (continuous_sourceStationaryPacket_in_x hcutoffCont houterCont
      houterSupport).norm.pow 2
  have hOn : IntegrableOn f S :=
    hfCont.continuousOn.integrableOn_compact isCompact_Icc
  have hInd : Integrable (S.indicator f) :=
    hOn.integrable_indicator measurableSet_Icc
  apply hInd.congr
  filter_upwards with x
  by_cases hx : x ∈ S
  · simp only [Set.indicator_of_mem hx]
    rfl
  · have hz := sourceStationaryPacket_eq_zero_outside_compact
      (beta := beta) (t := t) hX hH hcutoffSupport houterSupport hx
    simp [S, f, hz]

/-- The unrestricted packet is an `L²` function of the whole `x` line. -/
theorem memLp_sourceStationaryPacket
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    MemLp (fun x : ℝ ↦
      sourceStationaryPacket X H x beta t cutoff outer) 2 := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      sourceStationaryPacket X H x beta t cutoff outer) :=
    (continuous_sourceStationaryPacket_in_x hcutoffCont houterCont
      houterSupport).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hmeas).2
    (integrable_norm_sourceStationaryPacket_sq hX hH hcutoffCont houterCont
      hcutoffSupport houterSupport)

#print axioms sourceStationaryPacket_eq_zero_outside_compact
#print axioms integrable_norm_sourceStationaryPacket_sq
#print axioms memLp_sourceStationaryPacket

end
end MAPMRTWholeLinePacketMemLp
