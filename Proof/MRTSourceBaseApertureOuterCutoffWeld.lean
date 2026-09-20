import MRTSourceLowerCollarMemLpWeld
import MRTProposition51Supported

/-!
# Exact outer-cutoff insertion at the MAP base aperture

The endpoint `H=X/2` needs the quantitative lower-collar repair proved in the
preceding modules.  The MAP source input instead uses `baseAperture epsilon X`.
For `X ≥ 4` this aperture lies in the strict quarter range `H ≤ X/4`; there the
entire logarithmic cutoff window lies inside the region where the outer cutoff
is one.  Thus the correction vanishes exactly.  No monotonicity of the inner
cutoff in `H` is assumed.
-/

namespace MAPMRTSourceBaseApertureOuterCutoffWeld

open MeasureTheory Set
open MAPAllCenterApertureTransfer
open MAPMRTProposition51HardBranch MAPMRTProposition51Supported
open MAPMRTSourceOuterCutoffEndpoint

noncomputable section

/-- At the source-facing threshold `X ≥ 4`, the prescribed MAP aperture is in
the quarter range. -/
theorem baseAperture_le_quarter_of_four_le
    {epsilon X : ℝ} (hX : 4 ≤ X) :
    baseAperture epsilon X ≤ X / 4 := by
  have hXone : 1 ≤ X := by linarith
  have hreserve : apertureReserve epsilon ≤ 1 / 1200 := by
    unfold apertureReserve
    exact min_le_right _ _
  have hexponent : 2 / 15 + apertureReserve epsilon ≤ 1 / 2 := by
    linarith
  have hpow : Real.rpow X (2 / 15 + apertureReserve epsilon) ≤
      Real.rpow X (1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hsqrt : Real.sqrt X ≤ X / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hrpowHalf : Real.rpow X (1 / 2) = Real.sqrt X :=
    (Real.sqrt_eq_rpow X).symm
  rw [hrpowHalf] at hpow
  unfold baseAperture
  nlinarith

private theorem exp_neg_ten_lt_quarter :
    Real.exp (-10 : ℝ) < 1 / 4 := by
  have he : 11 < Real.exp (10 : ℝ) := by
    have he' := Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0)
    norm_num at he' ⊢
    exact he'
  rw [Real.exp_neg]
  rw [inv_eq_one_div]
  apply (div_lt_iff₀ (Real.exp_pos 10)).2
  nlinarith

/-- In the quarter range the inner cutoff can be nonzero only for
`-10 ≤ w ≤ 10`; hence inserting the outer cutoff is pointwise exact. -/
theorem sourcePacketAmplitude_eq_withoutOuter_of_quarterRange
    {X H x w : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hQuarter : H ≤ X / 4)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    sourcePacketAmplitude X H x cutoff outer w =
      sourcePacketAmplitude X H x cutoff (fun _ ↦ 1) w := by
  by_cases hcut : cutoff ((X * Real.exp w - x) / H) = 0
  · simp [sourcePacketAmplitude, hcut]
  have hwLower : -10 ≤ w := by
    by_contra hw
    have hexp : Real.exp w < Real.exp (-10) :=
      Real.exp_lt_exp.mpr (lt_of_not_ge hw)
    have hXexp : X * Real.exp w < X / 4 := by
      have hm := mul_lt_mul_of_pos_left
        (hexp.trans exp_neg_ten_lt_quarter) hX
      nlinarith
    have hxMinus : X / 4 ≤ x - H := by linarith [hx.1]
    have hnum : X * Real.exp w - x < -H := by linarith
    have hquot : (X * Real.exp w - x) / H < -1 := by
      rw [div_lt_iff₀ hH]
      linarith
    have habs : 1 ≤ |(X * Real.exp w - x) / H| := by
      rw [abs_of_neg (hquot.trans (by norm_num))]
      linarith
    exact hcut (hcutoffSupport _ habs)
  have hwUpper : w ≤ 10 := by
    by_contra hw
    exact hcut (cutoff_eq_zero_of_ten_lt_w
      hX hH (hQuarter.trans (by linarith)) hx.2
      hcutoffSupport (lt_of_not_ge hw))
  have hwScaled : |w / 100| ≤ (1 : ℝ) / 10 := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith
  simp [sourcePacketAmplitude, houterOne _ hwScaled]

/-- Packet-level exact insertion throughout the source support in the quarter
range. -/
theorem sourceStationaryPacket_eq_withoutOuter_of_quarterRange
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hQuarter : H ≤ X / 4)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    sourceStationaryPacket X H x beta t cutoff outer =
      sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1) := by
  unfold sourceStationaryPacket
  apply integral_congr_ae
  filter_upwards with w
  rw [sourcePacketAmplitude_eq_withoutOuter_of_quarterRange
    hX hH hQuarter hx hcutoffSupport houterOne]

/-- The lower-collar packet difference is identically zero at the MAP base
aperture once `X ≥ 4`. -/
theorem lowerOuterCollarPacketDifference_baseAperture_eq_zero
    {epsilon X beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 4 ≤ X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    lowerOuterCollarPacketDifference
      X (baseAperture epsilon X) beta t cutoff outer = 0 := by
  funext x
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < baseAperture epsilon X := baseAperture_pos hXpos
  have hQuarter : baseAperture epsilon X ≤ X / 4 :=
    baseAperture_le_quarter_of_four_le hX
  by_cases hx : x ∈ lowerOuterCollar X
  · have he : Real.exp (-10 : ℝ) < 1 :=
      Real.exp_lt_one_iff.mpr (by norm_num)
    have hxe : X * Real.exp (-10 : ℝ) < X :=
      by simpa using mul_lt_mul_of_pos_left he hXpos
    have hxIcc : x ∈ Set.Icc (X / 2) (4 * X) := by
      constructor
      · exact hx.1
      · have hupper : X / 2 + X * Real.exp (-10 : ℝ) < X / 2 + X :=
          by simpa [add_comm] using add_lt_add_left hxe (X / 2)
        exact (hx.2.trans hupper).le.trans (by linarith)
    have hp := sourceStationaryPacket_eq_withoutOuter_of_quarterRange
      (beta := beta) (t := t) hXpos hHpos hQuarter hxIcc
      hcutoffSupport houterOne
    simp [lowerOuterCollarPacketDifference, hx, hp]
  · simp [lowerOuterCollarPacketDifference, hx]

/-- Consequently the endpoint correction pairing itself is exactly zero for
the MAP base aperture. -/
theorem lowerOuterCollarPairingError_baseAperture_eq_zero
    {epsilon X beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    lowerOuterCollarPairingError
      X (baseAperture epsilon X) beta t cutoff outer g = 0 := by
  rw [lowerOuterCollarPairingError_eq_integral_mul_packetDifference,
    lowerOuterCollarPacketDifference_baseAperture_eq_zero
      hX hcutoffSupport houterOne]
  simp

/-- Source-facing exact outer-cutoff insertion at the actual MAP aperture.
This is the deterministic consumer to use in the HB decomposition. -/
theorem integral_mul_packet_withoutOuter_eq_outer_baseAperture
    {epsilon X beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hNoOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta t
        cutoff (fun _ ↦ 1)))
    (hOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta t
        cutoff outer)) :
    (∫ x : ℝ, g x *
      sourceStationaryPacket X (baseAperture epsilon X) x beta t
        cutoff (fun _ ↦ 1)) =
      ∫ x : ℝ, g x *
        sourceStationaryPacket X (baseAperture epsilon X) x beta t
          cutoff outer := by
  have hXpos : 0 < X := by linarith
  have hHpos : 0 < baseAperture epsilon X := baseAperture_pos hXpos
  have hHalf : baseAperture epsilon X ≤ X / 2 :=
    (baseAperture_le_quarter_of_four_le hX).trans (by linarith)
  rw [integral_mul_packet_withoutOuter_eq_outer_add_lowerOuterCollarPairingError
    hXpos hHpos hHalf hgSupport hcutoffSupport houterOne hNoOuter hOuter,
    lowerOuterCollarPairingError_baseAperture_eq_zero
      hX hcutoffSupport houterOne, add_zero]

end
end MAPMRTSourceBaseApertureOuterCutoffWeld

#print axioms MAPMRTSourceBaseApertureOuterCutoffWeld.baseAperture_le_quarter_of_four_le
#print axioms MAPMRTSourceBaseApertureOuterCutoffWeld.sourceStationaryPacket_eq_withoutOuter_of_quarterRange
#print axioms MAPMRTSourceBaseApertureOuterCutoffWeld.lowerOuterCollarPacketDifference_baseAperture_eq_zero
#print axioms MAPMRTSourceBaseApertureOuterCutoffWeld.lowerOuterCollarPairingError_baseAperture_eq_zero
#print axioms MAPMRTSourceBaseApertureOuterCutoffWeld.integral_mul_packet_withoutOuter_eq_outer_baseAperture
