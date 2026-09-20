import MRTWholeLinePacketTrivialBound

/-!
# The lower cell for the unrestricted MRT packet

The arithmetic cutoff forces the packet to vanish for `x ≤ -H`.  Hence the
part of the whole line below the high cell `x ≥ 4H` has effective length at
most `5H`.  This is the exact replacement for silently restoring a sharp
`[X/2,4X]` restriction after Cauchy--Schwarz.
-/

namespace MAPMRTWholeLineEq83ParallelLowCell

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTCorollary53Source

noncomputable section

theorem sourceStationaryPacket_eq_zero_of_le_neg_H
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hx : x ≤ -H) :
    sourceStationaryPacket X H x beta t cutoff outer = 0 := by
  unfold sourceStationaryPacket
  rw [show (∫ w : ℝ,
      additivePhase (stationaryPacketPhase X beta t w) *
        sourcePacketAmplitude X H x cutoff outer w) =
      ∫ _w : ℝ, (0 : ℂ) by
    apply integral_congr_ae
    filter_upwards with w
    have hnum : H ≤ X * Real.exp w - x := by
      have hcenter : 0 < X * Real.exp w := mul_pos hX (Real.exp_pos w)
      linarith
    have hquot : 1 ≤ (X * Real.exp w - x) / H := by
      rw [le_div_iff₀ hH]
      simpa only [one_mul] using hnum
    have hzero : cutoff ((X * Real.exp w - x) / H) = 0 := by
      apply hcutoffSupport
      rw [abs_of_nonneg (by linarith)]
      exact hquot
    simp [sourcePacketAmplitude, hzero]]
  simp

/-- A general lower-cell integration lemma. -/
theorem integral_Iio_four_mul_le_five_mul
    {H A : ℝ} {J : ℝ → ℂ}
    (hH : 0 < H) (hA : 0 ≤ A)
    (hzero : ∀ x, x ≤ -H → J x = 0)
    (hbound : ∀ x, ‖J x‖ ≤ A)
    (hInt : Integrable (fun x ↦ ‖J x‖ ^ 2)) :
    (∫ x in Set.Iio (4 * H), ‖J x‖ ^ 2) ≤ 5 * H * A ^ 2 := by
  let f : ℝ → ℝ := fun x ↦ ‖J x‖ ^ 2
  let g : ℝ → ℝ := fun _x ↦ A ^ 2
  have hleftInt : Integrable ((Set.Iio (4 * H)).indicator f) :=
    hInt.indicator measurableSet_Iio
  have hrightInt : Integrable ((Set.Ioc (-H) (4 * H)).indicator g) :=
    continuous_const.integrableOn_Ioc.integrable_indicator measurableSet_Ioc
  have hpoint : ∀ x,
      (Set.Iio (4 * H)).indicator f x ≤
        (Set.Ioc (-H) (4 * H)).indicator g x := by
    intro x
    by_cases hxHigh : x < 4 * H
    · by_cases hxLow : x ≤ -H
      · have hz := hzero x hxLow
        rw [Set.indicator_of_mem (show x ∈ Set.Iio (4 * H) by exact hxHigh)]
        simp only [f, hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow]
        exact Set.indicator_nonneg (fun _x _hx ↦ sq_nonneg A) x
      · have hxMid : -H < x := lt_of_not_ge hxLow
        simp only [Set.indicator_of_mem (show x ∈ Set.Iio (4 * H) by exact hxHigh),
          Set.indicator_of_mem (show x ∈ Set.Ioc (-H) (4 * H) by exact ⟨hxMid, hxHigh.le⟩)]
        unfold f g
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound x) 2
    · have hxNot : x ∉ Set.Iio (4 * H) := by simpa [Set.mem_Iio] using hxHigh
      rw [Set.indicator_of_notMem hxNot]
      exact Set.indicator_nonneg (fun _x _hx ↦ sq_nonneg A) x
  have hmono := integral_mono hleftInt hrightInt hpoint
  rw [MeasureTheory.integral_indicator measurableSet_Iio,
    MeasureTheory.integral_indicator measurableSet_Ioc] at hmono
  calc
    (∫ x in Set.Iio (4 * H), ‖J x‖ ^ 2) ≤
        ∫ x in Set.Ioc (-H) (4 * H), A ^ 2 := by simpa [f, g] using hmono
    _ = 5 * H * A ^ 2 := by
      rw [MeasureTheory.setIntegral_const, measureReal_def, Real.volume_Ioc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ 4 * H - -H)]
      simp only [smul_eq_mul]
      ring

#print axioms sourceStationaryPacket_eq_zero_of_le_neg_H
#print axioms integral_Iio_four_mul_le_five_mul

end
end MAPMRTWholeLineEq83ParallelLowCell
