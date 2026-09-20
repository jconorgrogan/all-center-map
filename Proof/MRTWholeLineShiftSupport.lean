import MRTWholeLineOffDiagonalAmplitudeL1

/-!
# The literal `h = O(H/X)` support in MRT p.50

After the whole-line `x` extension and the substitution `w' = w+h`, the
cutoff autocorrelation is supported where

`|(X exp w - X exp (w+h))/H| ≤ 2`.

Together with the two outer cutoffs (`|w|, |w+h| < 100`) this forces the
explicit window

`|h| ≤ 2 exp(100) H / X`.

This file also records the abstract final `h`-integration: a pointwise
`C H / d²` bound on that window integrates to the literal source scale
`4 exp(100) C H² / (X d²)`.
-/

namespace MAPMRTWholeLineShiftSupport

open MeasureTheory Set
open MAPMRTWholeLineCutoffAutocorrelation
open MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTWholeLineOffDiagonalAmplitudeL1

noncomputable section

private theorem nonnegative_shift_le_expWindow
    {X H h w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hh : 0 ≤ h)
    (hwLower : -100 < w)
    (hshift : |wholeLinePacketShift X H h w| ≤ 2) :
    h ≤ 2 * Real.exp 100 * H / X := by
  have hew : Real.exp (-100) ≤ Real.exp w :=
    Real.exp_le_exp.mpr hwLower.le
  have heh : h ≤ Real.exp h - 1 := by
    linarith [Real.add_one_le_exp h]
  have heh0 : 0 ≤ Real.exp h - 1 := by linarith
  have hprod : X * Real.exp (-100) * h ≤
      X * Real.exp w * (Real.exp h - 1) := by
    gcongr
  have hshift_formula :
      |wholeLinePacketShift X H h w| =
        X * Real.exp w * (Real.exp h - 1) / H := by
    unfold wholeLinePacketShift
    rw [Real.exp_add]
    rw [show X * Real.exp w - X * (Real.exp w * Real.exp h) =
        X * Real.exp w * (1 - Real.exp h) by ring]
    rw [abs_div, abs_mul, abs_mul, abs_of_pos hX,
      abs_of_pos (Real.exp_pos w), abs_of_nonpos (by linarith : 1 - Real.exp h ≤ 0),
      abs_of_pos hH]
    ring
  have hscaled : X * Real.exp (-100) * h ≤ 2 * H := by
    have hupper : X * Real.exp w * (Real.exp h - 1) ≤ 2 * H := by
      have := mul_le_mul_of_nonneg_right hshift hH.le
      rw [hshift_formula] at this
      field_simp [ne_of_gt hH] at this
      simpa [mul_comm] using this
    exact hprod.trans hupper
  have hexp_inv : Real.exp (-100) * Real.exp 100 = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [le_div_iff₀ hX]
  have hm := mul_le_mul_of_nonneg_right hscaled (Real.exp_pos 100).le
  have hm' : X * h ≤ 2 * Real.exp 100 * H := by
    calc
      X * h = X * Real.exp (-100) * h * Real.exp 100 := by
        rw [show X * Real.exp (-100) * h * Real.exp 100 =
          X * h * (Real.exp (-100) * Real.exp 100) by ring, hexp_inv]
        ring
      _ ≤ 2 * H * Real.exp 100 := hm
      _ = 2 * Real.exp 100 * H := by ring
  simpa [mul_comm] using hm'

theorem abs_shift_parameter_le_expWindow
    {X H h w : ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hw : |w| < 100) (hwh : |w + h| < 100)
    (hshift : |wholeLinePacketShift X H h w| ≤ 2) :
    |h| ≤ 2 * Real.exp 100 * H / X := by
  by_cases hh : 0 ≤ h
  · rw [abs_of_nonneg hh]
    exact nonnegative_shift_le_expWindow hX hH hh (abs_lt.mp hw).1 hshift
  · have hneg : h < 0 := lt_of_not_ge hh
    have hsymm :
        wholeLinePacketShift X H (-h) (w + h) =
          -wholeLinePacketShift X H h w := by
      unfold wholeLinePacketShift
      congr 1
      ring_nf
    have hshift' : |wholeLinePacketShift X H (-h) (w + h)| ≤ 2 := by
      rw [hsymm, abs_neg]
      exact hshift
    have hle := nonnegative_shift_le_expWindow hX hH (by linarith : 0 ≤ -h)
      (abs_lt.mp hwh).1 hshift'
    rw [abs_of_nonpos hneg.le]
    exact hle

private theorem all_zero_of_left_outer
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hw : 100 ≤ |w|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0 := by
  exact ⟨
    wholeLineOffDiagonalAmplitude_eq_zero_of_left_outer_support houterSupport hw,
    wholeLineOffDiagonalAmplitudeDeriv_eq_zero_of_left_outer_support
      houterSupport houter'Support hw,
    wholeLineOffDiagonalAmplitudeSecond_eq_zero_of_left_outer_support
      houterSupport houter'Support houter''Support hw⟩

private theorem all_zero_of_right_outer
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hwh : 100 ≤ |w + h|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0 := by
  exact ⟨
    wholeLineOffDiagonalAmplitude_eq_zero_of_right_outer_support houterSupport hwh,
    wholeLineOffDiagonalAmplitudeDeriv_eq_zero_of_right_outer_support
      houterSupport houter'Support hwh,
    wholeLineOffDiagonalAmplitudeSecond_eq_zero_of_right_outer_support
      houterSupport houter'Support houter''Support hwh⟩

/-- All three source amplitudes vanish pointwise when `h` lies outside the
explicit `2 exp(100) H/X` window. -/
theorem wholeLineAmplitudes_all_zero_of_h_outside
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (houter''Support : ∀ y, 1 ≤ |y| → outer'' y = 0)
    (hh : 2 * Real.exp 100 * H / X < |h|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0 := by
  by_cases hw : 100 ≤ |w|
  · exact all_zero_of_left_outer houterSupport houter'Support houter''Support hw
  · have hw' : |w| < 100 := lt_of_not_ge hw
    by_cases hwh : 100 ≤ |w + h|
    · exact all_zero_of_right_outer houterSupport houter'Support houter''Support hwh
    · have hwh' : |w + h| < 100 := lt_of_not_ge hwh
      apply wholeLineOffDiagonalAmplitude_all_zero_of_shift
        hcutoffSupport hcutoff'Support hcutoff''Support
      by_contra hn
      have hshift : |wholeLinePacketShift X H h w| ≤ 2 := le_of_not_gt hn
      exact (not_le_of_gt hh)
        (abs_shift_parameter_le_expWindow hX hH hw' hwh' hshift)

/-- Abstract scalar integration over an absolute-value support window. -/
theorem norm_integral_le_two_mul_window
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {R B : ℝ}
    (hR : 0 ≤ R)
    (hzero : ∀ h, R < |h| → f h = 0)
    (hbound : ∀ h, ‖f h‖ ≤ B) :
    ‖∫ h : ℝ, f h‖ ≤ 2 * R * B := by
  let I : Set ℝ := Set.Icc (-R) R
  have hEq : f =ᵐ[volume] I.indicator f := by
    filter_upwards [] with h
    by_cases hi : h ∈ I
    · simp [I, hi]
    · have hout : R < |h| := by
        simp only [I, Set.mem_Icc, not_and_or, not_le] at hi
        rcases hi with hi | hi
        · rw [abs_of_nonpos (by linarith)]
          linarith
        · rw [abs_of_nonneg (by linarith)]
          exact hi
      simp [I, hi, hzero h hout]
  rw [integral_congr_ae hEq, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := -R) (b := R) (C := B)
    (fun h _hh ↦ hbound h)
  calc
    ‖∫ h : ℝ in -R..R, f h‖ ≤ B * |R - -R| := h
    _ = 2 * R * B := by rw [abs_of_nonneg (by linarith : 0 ≤ R - -R)]; ring

/-- The final scalar `h` integration at the exact source scale.  This theorem
is deliberately abstract in the inner oscillatory integral: the companion
two-IBP module supplies its pointwise `C H/d²` estimate. -/
theorem norm_h_integral_le_eq82_scale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {X H d C : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hd : 0 < d) (hC : 0 ≤ C)
    (hzero : ∀ h, 2 * Real.exp 100 * H / X < |h| → f h = 0)
    (hbound : ∀ h, ‖f h‖ ≤ C * H / d ^ 2) :
    ‖∫ h : ℝ, f h‖ ≤
      4 * Real.exp 100 * C * H ^ 2 / (X * d ^ 2) := by
  have hR : 0 ≤ 2 * Real.exp 100 * H / X := by positivity
  have hB : 0 ≤ C * H / d ^ 2 := by positivity
  have h := norm_integral_le_two_mul_window hR hzero hbound
  calc
    ‖∫ h : ℝ, f h‖ ≤
        2 * (2 * Real.exp 100 * H / X) * (C * H / d ^ 2) := h
    _ = 4 * Real.exp 100 * C * H ^ 2 / (X * d ^ 2) := by
      field_simp [ne_of_gt hX, ne_of_gt hd]
      ring

#print axioms abs_shift_parameter_le_expWindow
#print axioms wholeLineAmplitudes_all_zero_of_h_outside
#print axioms norm_integral_le_two_mul_window
#print axioms norm_h_integral_le_eq82_scale

end
end MAPMRTWholeLineShiftSupport
