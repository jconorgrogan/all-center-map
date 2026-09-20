import MRTWholeLineOffDiagonalTwoIBP
import MRTWholeLineShiftSupport

/-!
# The whole-line hard off-diagonal bound after the `h` integration

This is the analytic side of MRT (8.2)--(8.4) after the exact whole-line
Fubini/change-of-variables identity.  The companion Fubini module identifies
the original packet correlation with this double integral.
-/

namespace MAPMRTWholeLineOffDiagonalEq82Bound

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTWholeLineOffDiagonalTwoIBP
open MAPMRTWholeLineShiftSupport

noncomputable section

def wholeLineOffDiagonalInnerIntegral
    (X H beta s s' : ℝ) (cutoff outer : ℝ → ℝ) (h : ℝ) : ℂ :=
  ∫ w : ℝ in (-100)..100,
    additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
      X beta s s' h w) *
      (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)

def wholeLineOffDiagonalDoubleIntegral
    (X H beta s s' : ℝ) (cutoff outer : ℝ → ℝ) : ℂ :=
  ∫ h : ℝ, wholeLineOffDiagonalInnerIntegral
    X H beta s s' cutoff outer h

/-- The final hard-frequency source bound.  The constant is explicit and the
right side has the required `H²/(X|s-s'|²)` scale. -/
theorem norm_wholeLineOffDiagonalDoubleIntegral_le
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
    ‖wholeLineOffDiagonalDoubleIntegral X H beta s s' cutoff outer‖ ≤
      4 * Real.exp 100 *
        wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 * H ^ 2 /
          (X * |s - s'| ^ 2) := by
  let f : ℝ → ℂ := fun h ↦ wholeLineOffDiagonalInnerIntegral
    X H beta s s' cutoff outer h
  have hbetaH : 0 < |beta| * H := lt_trans zero_lt_one hhard
  have hsepPos : 0 < 8 * Real.pi * |beta| * H := by
    rw [show 8 * Real.pi * |beta| * H = 8 * Real.pi * (|beta| * H) by ring]
    positivity
  have hP : 0 < |s - s'| := hsepPos.trans_le hsep
  have hC : 0 ≤ wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
    unfold wholeLineTwoIBPConstant wholeLineAmplitudeFirstConstant
      wholeLineAmplitudeSecondConstant
    positivity
  have hzero : ∀ h, 2 * Real.exp 100 * H / X < |h| → f h = 0 := by
    intro h hh
    have hz (w : ℝ) := wholeLineAmplitudes_all_zero_of_h_outside
      (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
      (cutoff'' := cutoff'') (outer := outer) (outer' := outer')
      (outer'' := outer'') (w := w) hX hH hcutoffSupport hcutoff'Support
      hcutoff''Support houterSupport houter'Support houter''Support hh
    unfold f wholeLineOffDiagonalInnerIntegral
    rw [show (∫ w : ℝ in (-100)..100,
        additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
          X beta s s' h w) *
          (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)) =
        ∫ _w : ℝ in (-100)..100, (0 : ℂ) by
      apply intervalIntegral.integral_congr
      intro w hw
      simp [hz w |>.1]]
    simp
  have hbound : ∀ h, ‖f h‖ ≤
      wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 * H /
        |s - s'| ^ 2 := by
    intro h
    exact norm_wholeLineOffDiagonalIntegral_le hX hH hhard hsep
      hBcut1 hBcut2 hBouter1 hBouter2 hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoffSupport hcutoff'Support
      hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
      houterSupport houter'Support houter''Support houterBound
      houter'Bound houter''Bound
  have hfinal := norm_h_integral_le_eq82_scale
    (f := f) (X := X) (H := H) (d := |s - s'|)
    (C := wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2)
    hX hH hP hC hzero hbound
  simpa [wholeLineOffDiagonalDoubleIntegral, f] using hfinal

#print axioms norm_wholeLineOffDiagonalDoubleIntegral_le

end
end MAPMRTWholeLineOffDiagonalEq82Bound
