import MRTSourceOuterCutoffEndpoint
import MRTSourceLowerCollarVdC

/-!
# Exact finite-interval identity for the MRT lower-collar packet

At the endpoint `H = X / 2`, the source packet has an unbounded logarithmic
window only at the single spatial endpoint `x = X / 2`.  At every strict
collar point its cutoff window is compact.  This module identifies the exact
part on which inserting the outer cutoff changes the packet:

`[log ((x-X/2)/X), -10]`.

This is a deterministic identity.  It keeps the literal lower collar, the
stationary phase, the source normalization, and the two cutoff functions
visible; it asserts no estimate for the resulting integral.
-/

namespace MAPMRTSourceLowerCollarPacketIdentity

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof
open MAPMRTSourceOuterCutoffEndpoint
open MAPMRTSourceLowerCollarVdC

noncomputable section

/-- The cutoff-window identity only needs positivity of `x-H`; the earlier
`H <= X/4` hypothesis was a convenient uniform way to obtain this positivity.
This strict version is the one needed inside the endpoint collar. -/
theorem sourcePacketAmplitude_eq_zero_of_not_mem_Ioc_strict
    {X H x w : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hxMinus : 0 < x - H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : w ∉ Set.Ioc (Real.log ((x - H) / X))
      (Real.log ((x + H) / X))) :
    sourcePacketAmplitude X H x cutoff outer w = 0 := by
  have hxPlus : 0 < x + H := by linarith
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hb : 0 < (x + H) / X := div_pos hxPlus hX
  simp only [Set.mem_Ioc, not_and_or, not_le] at hw
  have hzero : cutoff ((X * Real.exp w - x) / H) = 0 := by
    apply hcutoffSupport
    rcases hw with hwLeft | hwRight
    · have hexp : Real.exp w ≤ (x - H) / X := by
        rw [← Real.exp_log ha]
        exact Real.exp_le_exp.mpr (le_of_not_gt hwLeft)
      have hnum : X * Real.exp w - x ≤ -H := by
        have := (le_div_iff₀ hX).mp hexp
        linarith
      have hquot : (X * Real.exp w - x) / H ≤ -1 := by
        rw [div_le_iff₀ hH]
        linarith
      rw [abs_of_nonpos (hquot.trans (by norm_num))]
      linarith
    · have hexp : (x + H) / X < Real.exp w := by
        rw [← Real.exp_log hb]
        exact Real.exp_lt_exp.mpr hwRight
      have hnum : H < X * Real.exp w - x := by
        have := (div_lt_iff₀ hX).mp hexp
        linarith
      have hquot : 1 < (X * Real.exp w - x) / H := by
        rw [lt_div_iff₀ hH]
        linarith
      rw [abs_of_pos (lt_trans zero_lt_one hquot)]
      exact hquot.le
  simp [sourcePacketAmplitude, hzero]

/-- Whole-line equation (80) equals its literal compact cutoff window whenever
the lower spatial endpoint is strict. -/
theorem sourceStationaryPacket_eq_onCutoffWindow_strict
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hxMinus : 0 < x - H)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    sourceStationaryPacket X H x beta t cutoff outer =
      stationaryPacketOn X beta t
        (sourcePacketAmplitude X H x cutoff outer)
        (Real.log ((x - H) / X)) (Real.log ((x + H) / X)) := by
  have hxPlus : 0 < x + H := by linarith
  have hwindowOrder :
      Real.log ((x - H) / X) ≤ Real.log ((x + H) / X) := by
    apply Real.log_le_log (div_pos hxMinus hX)
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  let integrand : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w) *
      sourcePacketAmplitude X H x cutoff outer w
  have hindicator : integrand = Set.indicator
      (Set.Ioc (Real.log ((x - H) / X)) (Real.log ((x + H) / X)))
        integrand := by
    funext w
    by_cases hw : w ∈ Set.Ioc (Real.log ((x - H) / X))
        (Real.log ((x + H) / X))
    · simp [hw]
    · have hz := sourcePacketAmplitude_eq_zero_of_not_mem_Ioc_strict
        (outer := outer) hX hH hxMinus hcutoffSupport hw
      simp [integrand, hw, hz]
  unfold sourceStationaryPacket stationaryPacketOn
  change (∫ w : ℝ, integrand w) = _
  rw [hindicator, MeasureTheory.integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le hwindowOrder]

/-- At a strict point of the exact lower outer collar, the packet error is
precisely the interval from the cutoff's lower logarithmic endpoint to `-10`.
No collar mass, endpoint, or outer-cutoff normalization is discarded. -/
theorem sourceStationaryPacket_withoutOuter_sub_outer_eq_lowerCollarIntegral
    {X x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hx : x ∈ lowerOuterCollar X)
    (hxStrict : X / 2 < x)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    sourceStationaryPacket X (X / 2) x beta t cutoff (fun _ ↦ 1) -
        sourceStationaryPacket X (X / 2) x beta t cutoff outer =
      ∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w := by
  have hH : 0 < X / 2 := by positivity
  have hxMinus : 0 < x - X / 2 := sub_pos.mpr hxStrict
  have hxPlus : 0 < x + X / 2 := by linarith
  let a : ℝ := Real.log ((x - X / 2) / X)
  let b : ℝ := Real.log ((x + X / 2) / X)
  let phase : ℝ → ℂ := fun w ↦
    additivePhase (stationaryPacketPhase X beta t w)
  let amp0 : ℝ → ℂ := sourcePacketAmplitude X (X / 2) x cutoff (fun _ ↦ 1)
  let amp1 : ℝ → ℂ := sourcePacketAmplitude X (X / 2) x cutoff outer
  have hab : a ≤ b := by
    unfold a b
    apply Real.log_le_log (div_pos hxMinus hX)
    apply div_le_div_of_nonneg_right _ hX.le
    linarith
  have haNegTen : a < -10 := by
    have hxUpper := hx.2
    have hratio : (x - X / 2) / X < Real.exp (-10) := by
      rw [div_lt_iff₀ hX]
      linarith
    unfold a
    exact (Real.log_lt_iff_lt_exp (div_pos hxMinus hX)).mpr hratio
  have hbNegTen : -10 < b := by
    have hratio : 1 < (x + X / 2) / X := by
      rw [lt_div_iff₀ hX]
      linarith
    have hlogPos : 0 < Real.log ((x + X / 2) / X) := Real.log_pos hratio
    unfold b
    linarith
  have hcontPhase : Continuous phase := by
    unfold phase
    have hadd : Continuous additivePhase :=
      continuous_iff_continuousAt.mpr (fun z ↦
        (hasDerivAt_additivePhase z).continuousAt)
    have hp : Continuous (stationaryPacketPhase X beta t) :=
      continuous_iff_continuousAt.mpr (fun w ↦
        (hasDerivAt_stationaryPacketPhase X beta t w).continuousAt)
    exact hadd.comp hp
  have hcontAmp0 : Continuous amp0 := by
    unfold amp0 sourcePacketAmplitude
    have hexp : Continuous (fun w : ℝ ↦ Real.exp (w / 2)) := by fun_prop
    have hinner : Continuous (fun w : ℝ ↦
        cutoff ((X * Real.exp w - x) / (X / 2))) :=
      hcutoffCont.comp (by fun_prop)
    exact ((Complex.continuous_ofReal.comp hexp).mul
      (Complex.continuous_ofReal.comp hinner)).mul continuous_const
  have hcontAmp1 : Continuous amp1 := by
    unfold amp1 sourcePacketAmplitude
    have hexp : Continuous (fun w : ℝ ↦ Real.exp (w / 2)) := by fun_prop
    have hinner : Continuous (fun w : ℝ ↦
        cutoff ((X * Real.exp w - x) / (X / 2))) :=
      hcutoffCont.comp (by fun_prop)
    have houter : Continuous (fun w : ℝ ↦ outer (w / 100)) :=
      houterCont.comp (by fun_prop)
    exact ((Complex.continuous_ofReal.comp hexp).mul
      (Complex.continuous_ofReal.comp hinner)).mul
        (Complex.continuous_ofReal.comp houter)
  have hwhole0 := sourceStationaryPacket_eq_onCutoffWindow_strict
    (X := X) (H := X / 2) (x := x) (beta := beta) (t := t)
    (cutoff := cutoff) (outer := fun _ ↦ 1)
    hX hH hxMinus hcutoffSupport
  have hwhole1 := sourceStationaryPacket_eq_onCutoffWindow_strict
    (X := X) (H := X / 2) (x := x) (beta := beta) (t := t)
    (cutoff := cutoff) (outer := outer)
    hX hH hxMinus hcutoffSupport
  rw [hwhole0, hwhole1]
  unfold stationaryPacketOn
  change (∫ w in a..b, phase w * amp0 w) -
      (∫ w in a..b, phase w * amp1 w) = _
  have hInt0 : IntervalIntegrable (fun w ↦ phase w * amp0 w) volume a b :=
    (hcontPhase.mul hcontAmp0).intervalIntegrable a b
  have hInt1 : IntervalIntegrable (fun w ↦ phase w * amp1 w) volume a b :=
    (hcontPhase.mul hcontAmp1).intervalIntegrable a b
  rw [← intervalIntegral.integral_sub hInt0 hInt1]
  have hdiffCont : Continuous (fun w ↦
      phase w * amp0 w - phase w * amp1 w) :=
    (hcontPhase.mul hcontAmp0).sub (hcontPhase.mul hcontAmp1)
  have hsplit :
      (∫ w : ℝ in a..(-10), phase w * amp0 w - phase w * amp1 w) +
          (∫ w : ℝ in (-10)..b, phase w * amp0 w - phase w * amp1 w) =
        ∫ w : ℝ in a..b, phase w * amp0 w - phase w * amp1 w :=
    intervalIntegral.integral_add_adjacent_intervals
      (hdiffCont.intervalIntegrable a (-10))
      (hdiffCont.intervalIntegrable (-10) b)
  have hright : (∫ w in (-10)..b, phase w * amp0 w - phase w * amp1 w) = 0 := by
    calc
      (∫ w in (-10)..b, phase w * amp0 w - phase w * amp1 w) =
          ∫ _w : ℝ in (-10)..b, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro w hw
        have hw' : w ∈ Set.Icc (-10) b := by
          simpa [Set.uIcc_of_le hbNegTen.le] using hw
        have hwLower : -10 ≤ w := hw'.1
        by_cases hwUpper : w ≤ 10
        · have hscaled : |w / 100| ≤ (1 : ℝ) / 10 := by
            rw [abs_le]
            constructor <;> norm_num at * <;> linarith
          have hout : outer (w / 100) = 1 := houterOne _ hscaled
          simp [amp0, amp1, sourcePacketAmplitude, hout]
        · have hexpOne : Real.exp (-10 : ℝ) < 1 :=
            Real.exp_lt_one_iff.mpr (by norm_num)
          have hxUpper : x ≤ 4 * X := by
            have hcollarUpper := hx.2
            have hmul := mul_lt_mul_of_pos_left hexpOne hX
            nlinarith
          have hcut : cutoff ((X * Real.exp w - x) / (X / 2)) = 0 := by
            exact cutoff_eq_zero_of_ten_lt_w hX hH (le_rfl : X / 2 ≤ X / 2)
              hxUpper hcutoffSupport (lt_of_not_ge hwUpper)
          simp [amp0, amp1, sourcePacketAmplitude, hcut]
      _ = 0 := by simp
  rw [← hsplit, hright, add_zero]
  apply intervalIntegral.integral_congr
  intro w hw
  unfold phase amp0 amp1 sourceLowerCollarAmplitudeDifference
  ring

/-- Pointwise strict-collar form of the packet-difference kernel used by the
endpoint Cauchy--Schwarz reduction. -/
theorem lowerOuterCollarPacketDifference_eq_lowerCollarIntegral
    {X x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hx : x ∈ lowerOuterCollar X)
    (hxStrict : X / 2 < x)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    lowerOuterCollarPacketDifference X (X / 2) beta t cutoff outer x =
      ∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w := by
  rw [lowerOuterCollarPacketDifference, Set.indicator_of_mem hx]
  exact sourceStationaryPacket_withoutOuter_sub_outer_eq_lowerCollarIntegral
    hX hx hxStrict hcutoffCont houterCont hcutoffSupport houterOne

/-- The endpoint packet-difference energy is exactly the energy of the finite
lower-collar integral.  The single point `x=X/2`, where the logarithmic lower
endpoint is not finite, is removed only by Lebesgue almost-everywhere equality. -/
theorem integral_norm_sq_lowerOuterCollarPacketDifference_eq_finiteIntegral
    {X beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    (∫ x : ℝ,
        ‖lowerOuterCollarPacketDifference
          X (X / 2) beta t cutoff outer x‖ ^ 2) =
      ∫ x : ℝ in lowerOuterCollar X,
        ‖∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
          additivePhase (stationaryPacketPhase X beta t w) *
            sourceLowerCollarAmplitudeDifference
              X (X / 2) x cutoff outer w‖ ^ 2 := by
  have hmeas : MeasurableSet (lowerOuterCollar X) := by
    exact measurableSet_Ico
  rw [← MeasureTheory.integral_indicator hmeas]
  apply integral_congr_ae
  have hne : ∀ᵐ x : ℝ, x ≠ X / 2 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hxEndpoint
  by_cases hx : x ∈ lowerOuterCollar X
  · have hxStrict : X / 2 < x :=
      lt_of_le_of_ne hx.1 (Ne.symm hxEndpoint)
    rw [Set.indicator_of_mem hx,
      lowerOuterCollarPacketDifference_eq_lowerCollarIntegral
        hX hx hxStrict hcutoffCont houterCont hcutoffSupport houterOne]
  · simp [lowerOuterCollarPacketDifference, hx]

/-- Nearest endpoint constructor: Cauchy--Schwarz and the exact collar identity
leave only the finite lower-collar energy as a quantitative obligation. -/
theorem norm_sq_lowerOuterCollarPairingError_le_finiteIntegralEnergy
    {X beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 0 < X)
    (hcutoffCont : Continuous cutoff) (houterCont : Continuous outer)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hg : MemLp g 2)
    (hDiff : MemLp
      (lowerOuterCollarPacketDifference
        X (X / 2) beta t cutoff outer) 2)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖lowerOuterCollarPairingError
        X (X / 2) beta t cutoff outer g‖ ^ 2 ≤
      ∫ x : ℝ in lowerOuterCollar X,
        ‖∫ w : ℝ in Real.log ((x - X / 2) / X)..(-10),
          additivePhase (stationaryPacketPhase X beta t w) *
            sourceLowerCollarAmplitudeDifference
              X (X / 2) x cutoff outer w‖ ^ 2 := by
  rw [← integral_norm_sq_lowerOuterCollarPacketDifference_eq_finiteIntegral
    hX hcutoffCont houterCont hcutoffSupport houterOne]
  exact norm_sq_lowerOuterCollarPairingError_le_packetDifference_energy
    hg hDiff hgNorm

end
end MAPMRTSourceLowerCollarPacketIdentity

#print axioms MAPMRTSourceLowerCollarPacketIdentity.sourceStationaryPacket_eq_onCutoffWindow_strict
#print axioms MAPMRTSourceLowerCollarPacketIdentity.sourceStationaryPacket_withoutOuter_sub_outer_eq_lowerCollarIntegral
#print axioms MAPMRTSourceLowerCollarPacketIdentity.lowerOuterCollarPacketDifference_eq_lowerCollarIntegral
#print axioms MAPMRTSourceLowerCollarPacketIdentity.integral_norm_sq_lowerOuterCollarPacketDifference_eq_finiteIntegral
#print axioms MAPMRTSourceLowerCollarPacketIdentity.norm_sq_lowerOuterCollarPairingError_le_finiteIntegralEnergy
