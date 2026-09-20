import MRTWholeLinePacketMemLp

/-!
# A uniform whole-line trivial bound for the MRT source packet

Although the arithmetic center `x` is unrestricted after the legal
pre-Cauchy extension, the fixed outer window gives a uniform lower bound for
the derivative of `z(w)=(X exp w-x)/H`.  Changing variables in the cutoff
therefore recovers the source scale `H/X`, with a fixed `exp(50)` loss.
-/

namespace MAPMRTWholeLinePacketTrivialBound

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorput MAPMRTVanDerCorputProof

noncomputable section

/-- The exact outer-window `L¹` majorant.  `D0` is the fixed cutoff's
ordinary `L¹` budget. -/
theorem interval_norm_sourcePacketAmplitude_le
    {X H x D0 : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff)
    (houterCont : Continuous outer)
    (hcutoffInt : Integrable (fun y : ℝ ↦ |cutoff y|))
    (hD0 : (∫ y : ℝ, |cutoff y|) ≤ D0)
    (houterBound : ∀ y, |outer y| ≤ 1) :
    (∫ w : ℝ in (-100)..100,
        ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤
      Real.exp 50 * (H / X) * D0 := by
  let z : ℝ → ℝ := fun w ↦ (X * Real.exp w - x) / H
  let r : ℝ → ℝ := fun w ↦ X * Real.exp w / H
  have hzDeriv : ∀ w, HasDerivAt z (r w) w := by
    intro w
    unfold z r
    exact ((Real.hasDerivAt_exp w).const_mul X).sub_const x |>.div_const H
  have hrNonneg : ∀ w, 0 ≤ r w := by intro w; unfold r; positivity
  have hzCont : Continuous z := by unfold z; fun_prop
  have hchange :
      (∫ w : ℝ in (-100)..100, |cutoff (z w)| * r w) =
        ∫ y : ℝ in z (-100)..z 100, |cutoff y| := by
    simpa [Function.comp_def] using
      (intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
        (a := (-100 : ℝ)) (b := 100) (f := z) (f' := r)
        (g := fun y ↦ |cutoff y|) hzCont.continuousOn
        (fun w _ ↦ hzDeriv w) (fun w _ ↦ hrNonneg w))
  have hzOrder : z (-100) ≤ z 100 := by
    unfold z
    apply div_le_div_of_nonneg_right _ hH.le
    have he := Real.exp_le_exp.mpr (by norm_num : (-100 : ℝ) ≤ 100)
    nlinarith [mul_le_mul_of_nonneg_left he hX.le]
  have hcutInterval :
      (∫ y : ℝ in z (-100)..z 100, |cutoff y|) ≤ D0 :=
    (intervalIntegral_le_integral_of_nonneg hzOrder hcutoffInt
      (fun y ↦ abs_nonneg _)).trans hD0
  have hcutComp : Continuous fun w : ℝ ↦ |cutoff (z w)| :=
    hcutoffCont.abs.comp hzCont
  have hiLeft : IntervalIntegrable
      (fun w : ℝ ↦ ‖sourcePacketAmplitude X H x cutoff outer w‖)
      volume (-100) 100 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    unfold sourcePacketAmplitude
    fun_prop
  have hiRight : IntervalIntegrable
      (fun w : ℝ ↦ Real.exp 50 * (H / X) * (|cutoff (z w)| * r w))
      volume (-100) 100 := by
    apply ContinuousOn.intervalIntegrable
    apply Continuous.continuousOn
    exact continuous_const.mul (hcutComp.mul (by unfold r; fun_prop))
  have hpoint : ∀ w ∈ Set.Icc (-100 : ℝ) 100,
      ‖sourcePacketAmplitude X H x cutoff outer w‖ ≤
        Real.exp 50 * (H / X) * (|cutoff (z w)| * r w) := by
    intro w hw
    have he : Real.exp (w / 2) ≤ Real.exp 50 * Real.exp w := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hw.1]
    have hout := houterBound (w / 100)
    have hr : r w = X * Real.exp w / H := rfl
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    rw [show (X * Real.exp w - x) / H = z w by rfl]
    calc
      Real.exp (w / 2) * |cutoff (z w)| * |outer (w / 100)| ≤
          (Real.exp 50 * Real.exp w) * |cutoff (z w)| * 1 := by gcongr
      _ = Real.exp 50 * (H / X) * (|cutoff (z w)| * r w) := by
        rw [hr]
        field_simp [hX.ne', hH.ne']
  calc
    (∫ w : ℝ in (-100)..100,
        ‖sourcePacketAmplitude X H x cutoff outer w‖) ≤
        ∫ w : ℝ in (-100)..100,
          Real.exp 50 * (H / X) * (|cutoff (z w)| * r w) :=
      intervalIntegral.integral_mono_on (by norm_num) hiLeft hiRight hpoint
    _ = Real.exp 50 * (H / X) *
        (∫ w : ℝ in (-100)..100, |cutoff (z w)| * r w) := by
      rw [intervalIntegral.integral_const_mul]
    _ = Real.exp 50 * (H / X) *
        (∫ y : ℝ in z (-100)..z 100, |cutoff y|) := by rw [hchange]
    _ ≤ Real.exp 50 * (H / X) * D0 := by
      gcongr

/-- Uniform pointwise bound for the legally extended packet. -/
theorem norm_sourceStationaryPacket_le_trivial_wholeLine
    {X H x beta t D0 : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffCont : Continuous cutoff)
    (houterCont : Continuous outer)
    (hcutoffInt : Integrable (fun y : ℝ ↦ |cutoff y|))
    (hD0 : (∫ y : ℝ, |cutoff y|) ≤ D0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1) :
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      Real.exp 50 * D0 * H / X := by
  rw [sourceStationaryPacket_eq_onOuterWindow houterSupport]
  unfold stationaryPacketOn
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (by norm_num : (-100 : ℝ) ≤ 100) (f := fun w : ℝ ↦
      additivePhase (stationaryPacketPhase X beta t w) *
        sourcePacketAmplitude X H x cutoff outer w)
  refine hnorm.trans ?_
  have hamp := interval_norm_sourcePacketAmplitude_le (x := x) hX hH hcutoffCont
    houterCont hcutoffInt hD0 houterBound
  have heq : (∫ w : ℝ in (-100)..100,
      ‖additivePhase (stationaryPacketPhase X beta t w) *
        sourcePacketAmplitude X H x cutoff outer w‖) =
      ∫ w : ℝ in (-100)..100,
        ‖sourcePacketAmplitude X H x cutoff outer w‖ := by
    apply intervalIntegral.integral_congr
    intro w hw
    change ‖additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outer w‖ =
        ‖sourcePacketAmplitude X H x cutoff outer w‖
    rw [norm_mul, norm_additivePhase, one_mul]
  rw [heq]
  exact hamp.trans_eq (by ring)

#print axioms interval_norm_sourcePacketAmplitude_le
#print axioms norm_sourceStationaryPacket_le_trivial_wholeLine

end
end MAPMRTWholeLinePacketTrivialBound
