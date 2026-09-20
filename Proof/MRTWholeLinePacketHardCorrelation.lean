import MRTWholeLinePacketFubini
import MRTWholeLineOffDiagonalEq82Bound
import MRTWholeLineOffDiagonalAmplitudeL1

/-!
# Source-facing hard off-diagonal packet correlation

This module connects the exact unrestricted Fubini identity to the
support-aware two-integration-by-parts estimate.  The only adapter is the
literal outer-cutoff restriction from the whole `w` line to `[-100,100]`.
No sharp `x` cutoff and no extension-error term are introduced.
-/

namespace MAPMRTWholeLinePacketHardCorrelation

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTCorollary53Source
open MAPMRTOffDiagonalPhase
open MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTWholeLineOffDiagonalAmplitudeL1

noncomputable section

private theorem hundred_le_abs_of_not_mem_Ioc
    {w : ℝ} (hw : w ∉ Set.Ioc (-100 : ℝ) 100) :
    100 ≤ |w| := by
  simp only [Set.mem_Ioc, not_and_or, not_lt] at hw
  rcases hw with hw | hw
  · rw [abs_of_nonpos (by linarith)]
    linarith
  · rw [abs_of_nonneg (by linarith)]
    exact (not_le.mp hw).le

/-- The full-line `w` integral obtained by Fubini equals the fixed source
interval integral because the left outer factor vanishes at and beyond the
two endpoints. -/
theorem integral_wholeLineEvaluatedKernel_eq_innerIntegral
    {X H beta s s' h : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    (∫ w : ℝ,
        MAPMRTWholeLinePacketFubini.wholeLineEvaluatedKernel
          X H beta s s' cutoff outer (w, h)) =
      MAPMRTWholeLineOffDiagonalEq82Bound.wholeLineOffDiagonalInnerIntegral
        X H beta s s' cutoff outer h := by
  let f : ℝ → ℂ := fun w ↦
    additivePhase (offDiagonalPhase X beta s s' h w) *
      (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)
  have hpoint : ∀ w : ℝ,
      w ∉ Set.Ioc (-100 : ℝ) 100 → f w = 0 := by
    intro w hw
    have hzero := wholeLineOffDiagonalAmplitude_eq_zero_of_left_outer_support
      (X := X) (H := H) (h := h) (w := w) (cutoff := cutoff)
      houterSupport (hundred_le_abs_of_not_mem_Ioc hw)
    simp [f, hzero]
  unfold MAPMRTWholeLinePacketFubini.wholeLineEvaluatedKernel
    MAPMRTWholeLineOffDiagonalEq82Bound.wholeLineOffDiagonalInnerIntegral
  change (∫ w : ℝ, f w) = ∫ w : ℝ in (-100)..100, f w
  rw [intervalIntegral.integral_of_le (by norm_num : (-100 : ℝ) ≤ 100)]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ Set.Ioc (-100 : ℝ) 100
  · simp [hw]
  · simp [hw, hpoint w hw]

/-- The full-line double integral in the exact Fubini theorem is the same
object as the support-aware hard-bound double integral. -/
theorem wholeLineDoubleIntegral_eq_boundedDoubleIntegral
    {X H beta s s' : ℝ} {cutoff outer : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0) :
    MAPMRTWholeLinePacketFubini.wholeLineOffDiagonalDoubleIntegral
        X H beta s s' cutoff outer =
      MAPMRTWholeLineOffDiagonalEq82Bound.wholeLineOffDiagonalDoubleIntegral
        X H beta s s' cutoff outer := by
  unfold MAPMRTWholeLinePacketFubini.wholeLineOffDiagonalDoubleIntegral
    MAPMRTWholeLineOffDiagonalEq82Bound.wholeLineOffDiagonalDoubleIntegral
  apply integral_congr_ae
  filter_upwards with h
  exact integral_wholeLineEvaluatedKernel_eq_innerIntegral houterSupport

/-- The literal hard-frequency estimate in MRT equation (82), for the
unrestricted packet produced by the legal pre-Cauchy whole-line extension. -/
theorem norm_unrestrictedPacketCorrelation_le_hard
    {X H beta s s' Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hhard : 1 < |beta| * H)
    (hsep : 8 * Real.pi * |beta| * H ≤ |s - s'|)
    (hBcut1 : 0 ≤ Bcut1) (hBcut2 : 0 ≤ Bcut2)
    (hBouter1 : 0 ≤ Bouter1) (hBouter2 : 0 ≤ Bouter2)
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoff''Cont : Continuous cutoff'')
    (houterCont : Continuous outer)
    (houter'Cont : Continuous outer')
    (houter''Cont : Continuous outer'')
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ Bcut1)
    (hcutoff''Bound : ∀ y, |cutoff'' y| ≤ Bcut2)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ Bouter1)
    (houter''Bound : ∀ y, |outer'' y| ≤ Bouter2) :
    ‖MAPMRTPacketEquation82.packetCorrelation
        (fun r x ↦ sourceStationaryPacket X H x beta r cutoff outer)
        s s'‖ ≤
      4 * Real.exp 100 *
        MAPMRTWholeLineOffDiagonalTwoIBP.wholeLineTwoIBPConstant
          Bcut1 Bcut2 Bouter1 Bouter2 * H ^ 2 /
          (X * |s - s'| ^ 2) := by
  rw [MAPMRTWholeLinePacketFubini.packetCorrelation_unrestricted_eq_wholeLineOffDiagonalDoubleIntegral
      hX hH hcutoffCont houterCont hcutoffSupport houterSupport]
  rw [wholeLineDoubleIntegral_eq_boundedDoubleIntegral houterSupport]
  exact MAPMRTWholeLineOffDiagonalEq82Bound.norm_wholeLineOffDiagonalDoubleIntegral_le
      hX hH hhard hsep
      hBcut1 hBcut2 hBouter1 hBouter2 hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoffSupport hcutoff'Support
      hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
      houterSupport houter'Support houter''Support houterBound
      houter'Bound houter''Bound

#print axioms integral_wholeLineEvaluatedKernel_eq_innerIntegral
#print axioms wholeLineDoubleIntegral_eq_boundedDoubleIntegral
#print axioms norm_unrestrictedPacketCorrelation_le_hard

end
end MAPMRTWholeLinePacketHardCorrelation
