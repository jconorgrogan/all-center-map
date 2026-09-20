import MRTSourceLowerCollarPacketIdentity

/-!
# Resonant-cell energy on the full literal MRT lower collar

The resonant van der Corput estimate is naturally integrated only over
`[X/2, X/2 + 2*q*X)`.  The endpoint repair, however, is integrated over the
fixed outer collar `[X/2, X/2 + X*exp(-10))`.  When `2*q <= exp(-10)`, the
resonant packet vanishes identically on the difference.  This module proves
that support statement and transports the existing quantitative energy bound
to the literal outer collar.

No estimate for either off-resonance cell is asserted here.
-/

namespace MAPMRTSourceLowerCollarResonantEnergyWeld

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTSourceOuterCutoffEndpoint MAPMRTSourceLowerCollarVdC
open MAPMRTSourceLowerCollarResonance

noncomputable section

/-- Once `x` lies beyond the natural spatial support of the resonant cell,
the inner cutoff is zero at every resonant logarithmic ordinate. -/
theorem sourceLowerCollarResonantPacket_eq_zero_of_upper
    {X beta t x : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hx : X / 2 + 2 * lowerCollarResonanceRatio X beta t * X ≤ x)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0) :
    sourceLowerCollarResonantPacket X beta t cutoff outer x = 0 := by
  unfold sourceLowerCollarResonantPacket
  let q : ℝ := lowerCollarResonanceRatio X beta t
  have hq : 0 < q := hqPos
  let a : ℝ := Real.log (q / 2)
  let b : ℝ := Real.log (2 * q)
  change (∫ w : ℝ in a..b,
    additivePhase (stationaryPacketPhase X beta t w) *
      sourceLowerCollarAmplitudeDifference
        X (X / 2) x cutoff outer w) = 0
  have hab : a ≤ b := by
    unfold a b
    exact Real.log_le_log (by positivity) (by nlinarith)
  calc
    (∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) *
          sourceLowerCollarAmplitudeDifference
            X (X / 2) x cutoff outer w) =
        ∫ _w : ℝ in a..b, (0 : ℂ) := by
      apply intervalIntegral.integral_congr
      intro w hw
      have hw' : w ∈ Set.Icc a b := by
        simpa [Set.uIcc_of_le hab] using hw
      have hexp : Real.exp w ≤ 2 * q := by
        rw [← Real.exp_log (by positivity : 0 < 2 * q)]
        exact Real.exp_le_exp.mpr hw'.2
      have hnum : X * Real.exp w - x ≤ -(X / 2) := by
        have hmul := mul_le_mul_of_nonneg_left hexp hX.le
        nlinarith
      have hquot :
          (X * Real.exp w - x) / (X / 2) ≤ -1 := by
        rw [div_le_iff₀ (by positivity : 0 < X / 2)]
        linarith
      have hcut : cutoff ((X * Real.exp w - x) / (X / 2)) = 0 := by
        apply hcutoffSupport
        rw [abs_of_nonpos (hquot.trans (by norm_num))]
        linarith
      simp [sourceLowerCollarAmplitudeDifference, sourcePacketAmplitude, hcut]
    _ = 0 := by simp

/-- The resonant energy on the fixed outer collar is exactly its energy on
the smaller natural support window.  Half-open endpoints are kept literal. -/
theorem integral_norm_sq_resonantPacket_lowerOuterCollar_eq_endpointWindow
    {X beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hqTail : 2 * lowerCollarResonanceRatio X beta t ≤ Real.exp (-10))
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0) :
    (∫ x : ℝ in lowerOuterCollar X,
        ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2) =
      ∫ x : ℝ in Set.Ico (X / 2)
          (X / 2 + 2 * lowerCollarResonanceRatio X beta t * X),
        ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2 := by
  let q : ℝ := lowerCollarResonanceRatio X beta t
  have hq : 0 < q := hqPos
  let small : Set ℝ := Set.Ico (X / 2) (X / 2 + 2 * q * X)
  change (∫ x : ℝ in lowerOuterCollar X,
      ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2) =
    ∫ x : ℝ in small,
      ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2
  have hsmallMeas : MeasurableSet small := measurableSet_Ico
  have hcollarMeas : MeasurableSet (lowerOuterCollar X) := measurableSet_Ico
  have hsubset : small ⊆ lowerOuterCollar X := by
    intro x hx
    constructor
    · exact hx.1
    · have hmul := mul_le_mul_of_nonneg_left hqTail hX.le
      exact hx.2.trans_le (by nlinarith)
  rw [← MeasureTheory.integral_indicator hcollarMeas,
    ← MeasureTheory.integral_indicator hsmallMeas]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hxs : x ∈ small
  · have hxc : x ∈ lowerOuterCollar X := hsubset hxs
    simp [hxs, hxc]
  · by_cases hxc : x ∈ lowerOuterCollar X
    · have hxUpper : X / 2 + 2 * q * X ≤ x := by
        by_contra h
        exact hxs ⟨hxc.1, lt_of_not_ge h⟩
      have hz := sourceLowerCollarResonantPacket_eq_zero_of_upper
        (outer := outer) hX hqPos (by simpa [q] using hxUpper) hcutoffSupport
      simp [hxs, hxc, hz]
    · simp [hxs, hxc]

/-- Quantitative resonant-cell closure on the exact fixed lower collar.  This
is the existing finite-width van der Corput bound, with no unproved extension
from its natural spatial window. -/
theorem integral_norm_sq_sourceLowerCollarResonantPacket_on_lowerOuterCollar_le
    {X beta t B1 B2 Bout : ℝ}
    {cutoff cutoff' cutoff'' outer outer' : ℝ → ℝ}
    (hX : 0 < X) (hbeta : beta ≠ 0)
    (hqPos : 0 < lowerCollarResonanceRatio X beta t)
    (hqTail : 2 * lowerCollarResonanceRatio X beta t ≤ Real.exp (-10))
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bout)
    (houter'Cont : Continuous outer') :
    let q := lowerCollarResonanceRatio X beta t
    let a := Real.log (q / 2)
    let b := Real.log (2 * q)
    let K := 10 *
      (8 * B1 * q * Real.exp (b / 2) +
        (b - a) * (Real.exp (b / 2) *
          (4 * B1 * q + 32 * B2 * q ^ 2 + B1 * Bout * q / 25))) /
        Real.sqrt (|beta| * X * (q / 2))
    (∫ x : ℝ in lowerOuterCollar X,
      ‖sourceLowerCollarResonantPacket X beta t cutoff outer x‖ ^ 2) ≤
        2 * q * X * K ^ 2 := by
  dsimp
  rw [integral_norm_sq_resonantPacket_lowerOuterCollar_eq_endpointWindow
    hX hqPos hqTail hcutoffSupport]
  exact
    integral_norm_sq_sourceLowerCollarResonantPacket_on_endpointWindow_le
      hX hbeta hqPos hB1 hB2 hcutoffSupport hcutoff'Support
      hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
      houterDeriv houterBound houter'Bound houter'Cont

end
end MAPMRTSourceLowerCollarResonantEnergyWeld

#print axioms MAPMRTSourceLowerCollarResonantEnergyWeld.sourceLowerCollarResonantPacket_eq_zero_of_upper
#print axioms MAPMRTSourceLowerCollarResonantEnergyWeld.integral_norm_sq_resonantPacket_lowerOuterCollar_eq_endpointWindow
#print axioms MAPMRTSourceLowerCollarResonantEnergyWeld.integral_norm_sq_sourceLowerCollarResonantPacket_on_lowerOuterCollar_le
