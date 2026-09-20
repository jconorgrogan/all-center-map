import MRTWholeLineOffDiagonalAmplitude
import MRTOffDiagonalTwoIBP

/-!
# Support-aware two-IBP for the whole-line MRT amplitude

For fixed `h`, the cutoff-overlap condition is a connected left interval in
`w`, because

`|X exp w - X exp (w+h)| = X |1-exp h| exp w`.

We therefore integrate only over that active interval.  At its moving right
endpoint the cutoff autocorrelation and its first derivative vanish exactly.
This avoids imposing the phase-separation hypothesis on regions where the
amplitude is already zero, and it introduces no truncated-`x` boundary term.
-/

namespace MAPMRTWholeLineOffDiagonalTwoIBP

open MeasureTheory Set
open MAPMRTWholeLineCutoffAutocorrelation
open MAPMRTWholeLineOffDiagonalAmplitude
open MAPMRTOffDiagonalTwoIBP
open MAPMRTCorollary53Source

noncomputable section

private theorem one_le_abs_or_one_le_abs_add_of_two_le_abs
    {y delta : ℝ} (hdelta : 2 ≤ |delta|) :
    1 ≤ |y| ∨ 1 ≤ |y + delta| := by
  by_contra h
  push_neg at h
  have htri : |delta| ≤ |y + delta| + |y| := by
    calc
      |delta| = |(y + delta) - y| := by congr 1 <;> ring
      _ ≤ |y + delta| + |y| := abs_sub _ _
  linarith

theorem wholeLineCutoffAutocorrelation_eq_zero_of_two_le_abs
    {cutoff : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hdelta : 2 ≤ |delta|) :
    wholeLineCutoffAutocorrelation cutoff delta = 0 := by
  unfold wholeLineCutoffAutocorrelation
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_le_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoffSupport (y + delta) hyd, mul_zero]]
  simp

theorem wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_le_abs
    {cutoff cutoff' : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hdelta : 2 ≤ |delta|) :
    wholeLineCutoffAutocorrelationDeriv cutoff cutoff' delta = 0 := by
  unfold wholeLineCutoffAutocorrelationDeriv
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff' (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff' (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_le_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoff'Support (y + delta) hyd, mul_zero]]
  simp

theorem wholeLineCutoffAutocorrelationSecond_eq_zero_of_two_le_abs
    {cutoff cutoff'' : ℝ → ℝ} {delta : ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hdelta : 2 ≤ |delta|) :
    wholeLineCutoffAutocorrelationSecond cutoff cutoff'' delta = 0 := by
  unfold wholeLineCutoffAutocorrelationSecond
  rw [show (∫ y : ℝ in (-1)..1, cutoff y * cutoff'' (y + delta)) =
      ∫ _y : ℝ in (-1)..1, (0 : ℝ) by
    apply intervalIntegral.integral_congr
    intro y _hy
    change cutoff y * cutoff'' (y + delta) = 0
    rcases one_le_abs_or_one_le_abs_add_of_two_le_abs hdelta with hy | hyd
    · rw [hcutoffSupport y hy, zero_mul]
    · rw [hcutoff''Support (y + delta) hyd, mul_zero]]
  simp

theorem wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
    {X H h w : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (hshift : 2 ≤ |wholeLinePacketShift X H h w|) :
    wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0 := by
  have h0 := wholeLineCutoffAutocorrelation_eq_zero_of_two_le_abs
    hcutoffSupport hshift
  have h1 := wholeLineCutoffAutocorrelationDeriv_eq_zero_of_two_le_abs
    hcutoffSupport hcutoff'Support hshift
  have h2 := wholeLineCutoffAutocorrelationSecond_eq_zero_of_two_le_abs
    hcutoffSupport hcutoff''Support hshift
  simp [wholeLineOffDiagonalAmplitude, wholeLineOffDiagonalAmplitudeDeriv,
    wholeLineOffDiagonalAmplitudeSecond, wholeLineCorrelationAlong,
    wholeLineCorrelationAlongDeriv, wholeLineCorrelationAlongSecond,
    h0, h1, h2]

theorem abs_exp_center_difference
    {X h w : ℝ} (hX : 0 ≤ X) :
    |X * Real.exp w - X * Real.exp (w + h)| =
      X * |1 - Real.exp h| * Real.exp w := by
  rw [Real.exp_add]
  have he : 0 ≤ Real.exp w := (Real.exp_pos w).le
  calc
    |X * Real.exp w - X * (Real.exp w * Real.exp h)| =
        |X * Real.exp w * (1 - Real.exp h)| := by congr 1 <;> ring
    _ = |X| * |Real.exp w| * |1 - Real.exp h| := by rw [abs_mul, abs_mul]
    _ = X * Real.exp w * |1 - Real.exp h| := by
      rw [abs_of_nonneg hX, abs_of_nonneg he]
    _ = X * |1 - Real.exp h| * Real.exp w := by ring

private theorem center_distance_le_of_le_log_ratio
    {X H h w : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hc : 0 < X * |1 - Real.exp h|)
    (hw : w ≤ Real.log (2 * H / (X * |1 - Real.exp h|))) :
    |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H := by
  let c := X * |1 - Real.exp h|
  have hratio : 0 < 2 * H / c := div_pos (by positivity) hc
  have hew : Real.exp w ≤ 2 * H / c := by
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hw
  rw [abs_exp_center_difference hX.le]
  change c * Real.exp w ≤ _
  have hc0 : c ≠ 0 := ne_of_gt hc
  calc
    c * Real.exp w ≤ c * (2 * H / c) := by gcongr
    _ = 2 * H := by field_simp [hc0]

private theorem center_distance_ge_of_log_ratio_le
    {X H h w : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hc : 0 < X * |1 - Real.exp h|)
    (hw : Real.log (2 * H / (X * |1 - Real.exp h|)) ≤ w) :
    2 * H ≤ |X * Real.exp w - X * Real.exp (w + h)| := by
  let c := X * |1 - Real.exp h|
  have hratio : 0 < 2 * H / c := div_pos (by positivity) hc
  have hew : 2 * H / c ≤ Real.exp w := by
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hw
  rw [abs_exp_center_difference hX.le]
  change _ ≤ c * Real.exp w
  have hc0 : c ≠ 0 := ne_of_gt hc
  calc
    2 * H = c * (2 * H / c) := by field_simp [hc0]
    _ ≤ c * Real.exp w := by gcongr

private theorem two_le_abs_packetShift_of_center_ge
    {X H h w : ℝ} (hH : 0 < H)
    (hcenter : 2 * H ≤ |X * Real.exp w - X * Real.exp (w + h)|) :
    2 ≤ |wholeLinePacketShift X H h w| := by
  unfold wholeLinePacketShift
  rw [abs_div, abs_of_pos hH]
  exact (le_div_iff₀ hH).2 (by simpa using hcenter)

def wholeLineTwoIBPConstant
    (Bcut1 Bcut2 Bouter1 Bouter2 : ℝ) : ℝ :=
  200 * Real.exp 100 *
    ((4 * Real.pi) ^ 2 *
        wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2 +
      3 * (4 * Real.pi) ^ 3 *
        wholeLineAmplitudeFirstConstant Bcut1 Bouter1 +
      ((4 * Real.pi) * ((4 * Real.pi) ^ 2 + 2 * (4 * Real.pi) ^ 3) +
        (4 * Real.pi) ^ 4) * 2)

theorem raw_twoIBP_budget_eq_constant
    {H P Bcut1 Bcut2 Bouter1 Bouter2 : ℝ} (hP : 0 < P) :
    let d := P / (4 * Real.pi)
    (1 / d) ^ 2 *
          (200 * (H * Real.exp 100 *
            wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2)) +
        3 * (1 / d) * (P / d ^ 2) *
          (200 * (H * Real.exp 100 *
            wholeLineAmplitudeFirstConstant Bcut1 Bouter1)) +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) *
          (200 * (H * Real.exp 100 * 2)) =
      wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 * H / P ^ 2 := by
  dsimp
  unfold wholeLineTwoIBPConstant
  field_simp [ne_of_gt hP, Real.pi_ne_zero]

/-- Two integrations by parts on the connected active part of the whole-line
amplitude.  The hypotheses at `b` and on `[b,100]` are geometric support
facts, rather than an artificial truncation of the original `x` integral. -/
theorem norm_wholeLineOffDiagonalIntegral_le_of_activeRightEndpoint
    {X H beta s s' h b Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hH : 0 < H) (hhard : 1 < |beta| * H)
    (hsep : 8 * Real.pi * |beta| * H ≤ |s - s'|)
    (hbLeft : -100 ≤ b) (hbRight : b ≤ 100)
    (hclose : ∀ w ∈ Set.Icc (-100 : ℝ) b,
      |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H)
    (hAb : wholeLineOffDiagonalAmplitude X H cutoff outer h b = 0)
    (hA1b : wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff'
      outer outer' h b = 0)
    (hTail : ∀ w ∈ Set.Icc b 100,
      wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0)
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
    let d := |s - s'| / (4 * Real.pi)
    let P := |s - s'|
    ‖∫ w : ℝ in (-100)..100,
        additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
          X beta s s' h w) *
          (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)‖ ≤
      (1 / d) ^ 2 *
          (200 * (H * Real.exp 100 *
            wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2)) +
        3 * (1 / d) * (P / d ^ 2) *
          (200 * (H * Real.exp 100 *
            wholeLineAmplitudeFirstConstant Bcut1 Bouter1)) +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) *
          (200 * (H * Real.exp 100 * 2)) := by
  dsimp
  let Ar : ℝ → ℝ := wholeLineOffDiagonalAmplitude X H cutoff outer h
  let A1r : ℝ → ℝ :=
    wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h
  let A2r : ℝ → ℝ :=
    wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
      outer outer' outer'' h
  let A : ℝ → ℂ := fun w ↦ (Ar w : ℂ)
  let A1 : ℝ → ℂ := fun w ↦ (A1r w : ℂ)
  let A2 : ℝ → ℂ := fun w ↦ (A2r w : ℂ)
  have hArCont : Continuous Ar := continuous_iff_continuousAt.mpr fun w ↦
    (hasDerivAt_wholeLineOffDiagonalAmplitude hcutoffCont hcutoff'Cont
      hcutoffBound hcutoff'Bound hcutoffDeriv houterDeriv).continuousAt
  have hA1rCont : Continuous A1r := continuous_iff_continuousAt.mpr fun w ↦
    (hasDerivAt_wholeLineOffDiagonalAmplitudeDeriv hcutoffCont hcutoff'Cont
      hcutoff''Cont hcutoffBound hcutoff'Bound hcutoff''Bound
      hcutoffDeriv hcutoffSecond houterDeriv houterSecond).continuousAt
  have hA2rCont : Continuous A2r :=
    continuous_wholeLineOffDiagonalAmplitudeSecond hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont
  have hACont : Continuous A := Complex.continuous_ofReal.comp hArCont
  have hA1Cont : Continuous A1 := Complex.continuous_ofReal.comp hA1rCont
  have hA2Cont : Continuous A2 := Complex.continuous_ofReal.comp hA2rCont
  have hbudgets := wholeLineOffDiagonalAmplitude_L1_budgets
    (X := X) (H := H) (h := h) (Bcut1 := Bcut1) (Bcut2 := Bcut2)
    (Bouter1 := Bouter1) (Bouter2 := Bouter2)
    (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
    (outer := outer) (outer' := outer') (outer'' := outer'')
    hH.le hBcut1 hBcut2 hBouter1 hBouter2 hcutoffCont hcutoff'Cont
    hcutoff''Cont houterCont houter'Cont houter''Cont hcutoffDeriv
    hcutoffSecond houterDeriv houterSecond hcutoffSupport hcutoff'Support
    hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
    houterSupport houter'Support houter''Support houterBound
    houter'Bound houter''Bound
  have hA0sub : (∫ w : ℝ in (-100)..b, ‖A w‖) ≤
      200 * (H * Real.exp 100 * 2) := by
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (f := fun w ↦ ‖A w‖) (a := (-100 : ℝ)) (b := b)
      (c := (-100 : ℝ)) (d := 100)
      (by rfl) hbLeft hbRight
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hACont.norm.intervalIntegrable (-100) 100)
    exact hm.trans (by simpa [A, Ar, Complex.norm_real, Real.norm_eq_abs] using hbudgets.1)
  have hA1sub : (∫ w : ℝ in (-100)..b, ‖A1 w‖) ≤
      200 * (H * Real.exp 100 *
        wholeLineAmplitudeFirstConstant Bcut1 Bouter1) := by
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (f := fun w ↦ ‖A1 w‖) (a := (-100 : ℝ)) (b := b)
      (c := (-100 : ℝ)) (d := 100)
      (by rfl) hbLeft hbRight
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hA1Cont.norm.intervalIntegrable (-100) 100)
    exact hm.trans (by simpa [A1, A1r, Complex.norm_real, Real.norm_eq_abs] using hbudgets.2.1)
  have hA2sub : (∫ w : ℝ in (-100)..b, ‖A2 w‖) ≤
      200 * (H * Real.exp 100 *
        wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2) := by
    have hm := intervalIntegral.integral_mono_interval (μ := volume)
      (f := fun w ↦ ‖A2 w‖) (a := (-100 : ℝ)) (b := b)
      (c := (-100 : ℝ)) (d := 100)
      (by rfl) hbLeft hbRight
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
      (hA2Cont.norm.intervalIntegrable (-100) 100)
    exact hm.trans (by simpa [A2, A2r, Complex.norm_real, Real.norm_eq_abs] using hbudgets.2.2)
  have hleftEndpoints := wholeLineOffDiagonalAmplitude_endpoints
    (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
    houterSupport houter'Support
  have hcore := norm_offDiagonalIntegral_le_two_ibp_budgets
    (X := X) (H := H) (beta := beta) (s := s) (s' := s') (h := h)
    (a := (-100 : ℝ)) (b := b)
    (amplitude := A) (amplitude' := A1) (amplitude'' := A2)
    (A0 := 200 * (H * Real.exp 100 * 2))
    (A1 := 200 * (H * Real.exp 100 *
      wholeLineAmplitudeFirstConstant Bcut1 Bouter1))
    (A2 := 200 * (H * Real.exp 100 *
      wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2))
    hbLeft hH hhard hsep hclose
    (fun w hw ↦ (hasDerivAt_wholeLineOffDiagonalAmplitude hcutoffCont
      hcutoff'Cont hcutoffBound hcutoff'Bound hcutoffDeriv houterDeriv
        (w := w)).ofReal_comp)
    (fun w hw ↦ (hasDerivAt_wholeLineOffDiagonalAmplitudeDeriv hcutoffCont
      hcutoff'Cont hcutoff''Cont hcutoffBound hcutoff'Bound
      hcutoff''Bound hcutoffDeriv hcutoffSecond houterDeriv houterSecond
        (w := w)).ofReal_comp)
    hA2Cont.continuousOn
    (by simpa [A, Ar] using hleftEndpoints.1)
    (by simpa [A, Ar] using hAb)
    (by simpa [A1, A1r] using hleftEndpoints.2.2.1)
    (by simpa [A1, A1r] using hA1b)
    hA0sub hA1sub hA2sub
  let integrand : ℝ → ℂ := fun w ↦
    additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
      X beta s s' h w) * A w
  have hphaseCont : Continuous fun w ↦
      additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
        X beta s s' h w) := by
    have hadd : Continuous additivePhase := continuous_iff_continuousAt.mpr fun z ↦
      (MAPMRTVanDerCorputProof.hasDerivAt_additivePhase z).continuousAt
    exact hadd.comp (continuous_iff_continuousAt.mpr fun w ↦
      (MAPMRTOffDiagonalPhase.hasDerivAt_offDiagonalPhase X beta s s' h w).continuousAt)
  have hintCont : Continuous integrand := hphaseCont.mul hACont
  have htailZero : (∫ w : ℝ in b..100, integrand w) = 0 := by
    rw [show (∫ w : ℝ in b..100, integrand w) =
        ∫ _w : ℝ in b..100, (0 : ℂ) by
      apply intervalIntegral.integral_congr
      intro w hw
      have hwIcc : w ∈ Set.Icc b 100 := by
        simpa [Set.uIcc_of_le hbRight] using hw
      simp [integrand, A, Ar, hTail w hwIcc]]
    simp
  have hleftInt : IntervalIntegrable integrand volume (-100) b :=
    hintCont.intervalIntegrable (-100) b
  have hrightInt : IntervalIntegrable integrand volume b 100 :=
    hintCont.intervalIntegrable b 100
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    hleftInt hrightInt
  have hfull : (∫ w : ℝ in (-100)..100, integrand w) =
      ∫ w : ℝ in (-100)..b, integrand w := by
    rw [htailZero, add_zero] at hadd
    exact hadd.symm
  calc
    ‖∫ w : ℝ in (-100)..100,
        additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
          X beta s s' h w) *
          (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)‖ =
        ‖∫ w : ℝ in (-100)..100, integrand w‖ := by rfl
    _ = ‖∫ w : ℝ in (-100)..b, integrand w‖ := congrArg norm hfull
    _ ≤ _ := by simpa [integrand] using hcore

/-- For each fixed shift, either the whole amplitude vanishes on the outer
window or its active support has one right endpoint on which both boundary
terms vanish. -/
theorem exists_activeRightEndpoint_or_all_zero
    {X H h : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (hcutoff''Support : ∀ y, 1 ≤ |y| → cutoff'' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0) :
    (∀ w ∈ Set.Icc (-100 : ℝ) 100,
      wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h w = 0 ∧
      wholeLineOffDiagonalAmplitudeSecond X H cutoff cutoff' cutoff''
        outer outer' outer'' h w = 0) ∨
    ∃ b : ℝ, -100 ≤ b ∧ b ≤ 100 ∧
      (∀ w ∈ Set.Icc (-100 : ℝ) b,
        |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H) ∧
      wholeLineOffDiagonalAmplitude X H cutoff outer h b = 0 ∧
      wholeLineOffDiagonalAmplitudeDeriv X H cutoff cutoff' outer outer' h b = 0 ∧
      (∀ w ∈ Set.Icc b 100,
        wholeLineOffDiagonalAmplitude X H cutoff outer h w = 0) := by
  let c : ℝ := X * |1 - Real.exp h|
  by_cases hc0 : c = 0
  · right
    refine ⟨100, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
    · intro w hw
      rw [abs_exp_center_difference hX.le]
      change c * Real.exp w ≤ 2 * H
      rw [hc0, zero_mul]
      positivity
    · exact (wholeLineOffDiagonalAmplitude_endpoints
        (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
        houterSupport houter'Support).2.1
    · exact (wholeLineOffDiagonalAmplitude_endpoints
        (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
        houterSupport houter'Support).2.2.2
    · intro w hw
      have : w = 100 := by linarith [hw.1, hw.2]
      subst w
      exact (wholeLineOffDiagonalAmplitude_endpoints
        (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
        houterSupport houter'Support).2.1
  · have hc : 0 < c := lt_of_le_of_ne (by positivity) (Ne.symm hc0)
    let r : ℝ := Real.log (2 * H / c)
    by_cases hr : r ≤ -100
    · left
      intro w hw
      have hcenter : 2 * H ≤ |X * Real.exp w - X * Real.exp (w + h)| := by
        apply center_distance_ge_of_log_ratio_le hX hH
          (by simpa [c] using hc)
        simpa [r, c] using hr.trans hw.1
      exact wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
        hcutoffSupport hcutoff'Support hcutoff''Support
        (two_le_abs_packetShift_of_center_ge hH hcenter)
    · have hrLeft : -100 ≤ r := le_of_not_ge hr
      let b : ℝ := min 100 r
      have hbLeft : -100 ≤ b := by
        unfold b
        exact le_min (by norm_num) hrLeft
      have hbRight : b ≤ 100 := min_le_left _ _
      right
      refine ⟨b, hbLeft, hbRight, ?_, ?_, ?_, ?_⟩
      · intro w hw
        apply center_distance_le_of_le_log_ratio hX hH
          (by simpa [c] using hc)
        have hbr : b ≤ r := min_le_right _ _
        simpa [r, c] using hw.2.trans hbr
      · by_cases hr100 : 100 ≤ r
        · have hb100 : b = 100 := by simp [b, min_eq_left hr100]
          rw [hb100]
          exact (wholeLineOffDiagonalAmplitude_endpoints
            (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
            houterSupport houter'Support).2.1
        · have hbr : b = r := by simp [b, min_eq_right (le_of_not_ge hr100)]
          have hcenter : 2 * H ≤ |X * Real.exp b - X * Real.exp (b + h)| := by
            apply center_distance_ge_of_log_ratio_le hX hH
              (by simpa [c] using hc)
            simp [hbr, r, c]
          exact (wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
            (outer' := outer') (outer'' := outer'')
            hcutoffSupport hcutoff'Support hcutoff''Support
            (two_le_abs_packetShift_of_center_ge hH hcenter)).1
      · by_cases hr100 : 100 ≤ r
        · have hb100 : b = 100 := by simp [b, min_eq_left hr100]
          rw [hb100]
          exact (wholeLineOffDiagonalAmplitude_endpoints
            (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
            houterSupport houter'Support).2.2.2
        · have hbr : b = r := by simp [b, min_eq_right (le_of_not_ge hr100)]
          have hcenter : 2 * H ≤ |X * Real.exp b - X * Real.exp (b + h)| := by
            apply center_distance_ge_of_log_ratio_le hX hH
              (by simpa [c] using hc)
            simp [hbr, r, c]
          exact (wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
            (outer' := outer') (outer'' := outer'')
            hcutoffSupport hcutoff'Support hcutoff''Support
            (two_le_abs_packetShift_of_center_ge hH hcenter)).2.1
      · intro w hw
        by_cases hr100 : 100 ≤ r
        · have hb100 : b = 100 := by simp [b, min_eq_left hr100]
          have hw100 : w = 100 := by rw [hb100] at hw; linarith [hw.1, hw.2]
          subst w
          exact (wholeLineOffDiagonalAmplitude_endpoints
            (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
            houterSupport houter'Support).2.1
        · have hbr : b = r := by simp [b, min_eq_right (le_of_not_ge hr100)]
          have hcenter : 2 * H ≤ |X * Real.exp w - X * Real.exp (w + h)| := by
            apply center_distance_ge_of_log_ratio_le hX hH
              (by simpa [c] using hc)
            simpa [hbr, r, c] using hw.1
          exact (wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
            (outer' := outer') (outer'' := outer'')
            hcutoffSupport hcutoff'Support hcutoff''Support
            (two_le_abs_packetShift_of_center_ge hH hcenter)).1

/-- The fixed-shift whole-line oscillatory integral has the exact source size
`O(H/|s-s'|^2)`.  The displayed constant depends only on the six cutoff
budgets and contains no `X/H`. -/
theorem norm_wholeLineOffDiagonalIntegral_le
    {X H beta s s' h Bcut1 Bcut2 Bouter1 Bouter2 : ℝ}
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
    ‖∫ w : ℝ in (-100)..100,
        additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
          X beta s s' h w) *
          (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)‖ ≤
      wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 * H /
        |s - s'| ^ 2 := by
  have hbetaH : 0 < |beta| * H := lt_trans zero_lt_one hhard
  have hsepPos : 0 < 8 * Real.pi * |beta| * H := by
    rw [show 8 * Real.pi * |beta| * H = 8 * Real.pi * (|beta| * H) by ring]
    positivity
  have hP : 0 < |s - s'| := hsepPos.trans_le hsep
  have hC : 0 ≤ wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 := by
    unfold wholeLineTwoIBPConstant wholeLineAmplitudeFirstConstant
      wholeLineAmplitudeSecondConstant
    positivity
  rcases exists_activeRightEndpoint_or_all_zero
    (X := X) (H := H) (h := h) (cutoff := cutoff) (cutoff' := cutoff')
    (cutoff'' := cutoff'') (outer := outer) (outer' := outer')
    (outer'' := outer'') hX hH hcutoffSupport hcutoff'Support
    hcutoff''Support houterSupport houter'Support with hzero | hactive
  · have hInt : (∫ w : ℝ in (-100)..100,
        additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
          X beta s s' h w) *
          (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)) = 0 := by
      rw [show (∫ w : ℝ in (-100)..100,
          additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
            X beta s s' h w) *
            (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)) =
          ∫ _w : ℝ in (-100)..100, (0 : ℂ) by
        apply intervalIntegral.integral_congr
        intro w hw
        have hwIcc : w ∈ Set.Icc (-100 : ℝ) 100 := by
          simpa [Set.uIcc_of_le (by norm_num : (-100 : ℝ) ≤ 100)] using hw
        simp [hzero w hwIcc |>.1]]
      simp
    rw [hInt, norm_zero]
    positivity
  · obtain ⟨b, hbLeft, hbRight, hclose, hAb, hA1b, hTail⟩ := hactive
    have hraw := norm_wholeLineOffDiagonalIntegral_le_of_activeRightEndpoint
      (X := X) (H := H) (beta := beta) (s := s) (s' := s') (h := h)
      (b := b) (Bcut1 := Bcut1) (Bcut2 := Bcut2)
      (Bouter1 := Bouter1) (Bouter2 := Bouter2)
      (cutoff := cutoff) (cutoff' := cutoff') (cutoff'' := cutoff'')
      (outer := outer) (outer' := outer') (outer'' := outer'')
      hH hhard hsep hbLeft hbRight hclose hAb hA1b hTail
      hBcut1 hBcut2 hBouter1 hBouter2 hcutoffCont hcutoff'Cont
      hcutoff''Cont houterCont houter'Cont houter''Cont hcutoffDeriv
      hcutoffSecond houterDeriv houterSecond hcutoffSupport hcutoff'Support
      hcutoff''Support hcutoffBound hcutoff'Bound hcutoff''Bound
      houterSupport houter'Support houter''Support houterBound
      houter'Bound houter''Bound
    calc
      ‖∫ w : ℝ in (-100)..100,
          additivePhase (MAPMRTOffDiagonalPhase.offDiagonalPhase
            X beta s s' h w) *
            (wholeLineOffDiagonalAmplitude X H cutoff outer h w : ℂ)‖ ≤
          (1 / (|s - s'| / (4 * Real.pi))) ^ 2 *
              (200 * (H * Real.exp 100 *
                wholeLineAmplitudeSecondConstant Bcut1 Bcut2 Bouter1 Bouter2)) +
            3 * (1 / (|s - s'| / (4 * Real.pi))) *
              (|s - s'| / (|s - s'| / (4 * Real.pi)) ^ 2) *
              (200 * (H * Real.exp 100 *
                wholeLineAmplitudeFirstConstant Bcut1 Bouter1)) +
            ((1 / (|s - s'| / (4 * Real.pi))) *
                (|s - s'| / (|s - s'| / (4 * Real.pi)) ^ 2 +
                  2 * |s - s'| ^ 2 / (|s - s'| / (4 * Real.pi)) ^ 3) +
              (|s - s'| / (|s - s'| / (4 * Real.pi)) ^ 2) ^ 2) *
              (200 * (H * Real.exp 100 * 2)) := by simpa using hraw
      _ = wholeLineTwoIBPConstant Bcut1 Bcut2 Bouter1 Bouter2 * H /
          |s - s'| ^ 2 := raw_twoIBP_budget_eq_constant hP

#print axioms wholeLineOffDiagonalAmplitude_all_zero_of_two_le_shift
#print axioms abs_exp_center_difference
#print axioms norm_wholeLineOffDiagonalIntegral_le_of_activeRightEndpoint
#print axioms exists_activeRightEndpoint_or_all_zero
#print axioms norm_wholeLineOffDiagonalIntegral_le

end
end MAPMRTWholeLineOffDiagonalTwoIBP
