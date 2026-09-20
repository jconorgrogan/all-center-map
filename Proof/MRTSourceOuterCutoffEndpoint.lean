import MRTSourceWholeLineExtension

/-!
# The endpoint correction for the outer cutoff in MRT equation (80)

At the literal endpoint `H = X / 2`, the source sentence asserting that the
outer cutoff is identically one on the support of the `x`-localized packet is
false at the lower boundary `x = X / 2`: arbitrarily negative logarithmic
variables can occur there.  The failure is confined exactly to the collar

`[X / 2, X / 2 + X * exp (-10))`.

This module proves that finite geometry, identifies the region on which the
outer insertion remains exact, and records the exact lower-collar correction
to the source pairing.  It does not assume a bound for that correction.
-/

namespace MAPMRTSourceOuterCutoffEndpoint

open MeasureTheory Set
open MAPMRTProposition51HardBranch

noncomputable section

/-- The lower collar forced by the range on which the source outer cutoff is
identically one (`|w / 100| ≤ 1 / 10`). -/
def lowerOuterCollar (X : ℝ) : Set ℝ :=
  Set.Ico (X / 2) (X / 2 + X * Real.exp (-10))

/-- If the inner cutoff is nonzero at a logarithmic point below `-10`, then
`x` lies in the exact lower collar.  This remains valid at `H = X / 2`. -/
theorem mem_lowerOuterCollar_of_cutoff_ne_zero_of_w_lt_neg_ten
    {X H x w : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff : cutoff ((X * Real.exp w - x) / H) ≠ 0)
    (hw : w < -10) :
    x ∈ lowerOuterCollar X := by
  have hquot : |(X * Real.exp w - x) / H| < 1 := by
    by_contra h
    exact hcutoff (hcutoffSupport _ (le_of_not_gt h))
  have hleft : -1 < (X * Real.exp w - x) / H :=
    (abs_lt.mp hquot).1
  have hnum : -H < X * Real.exp w - x := by
    simpa using (lt_div_iff₀ hH).mp hleft
  have hexp : Real.exp w < Real.exp (-10) :=
    Real.exp_lt_exp.mpr hw
  have hXexp : X * Real.exp w < X * Real.exp (-10) :=
    mul_lt_mul_of_pos_left hexp hX
  constructor
  · exact hxLower
  · linarith

/-- Above `w = 10` the inner cutoff cannot meet `[X/2,4X]` in the literal
half range. -/
theorem cutoff_eq_zero_of_ten_lt_w
    {X H x w : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hxUpper : x ≤ 4 * X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : 10 < w) :
    cutoff ((X * Real.exp w - x) / H) = 0 := by
  by_contra hcutoff
  have hquot : |(X * Real.exp w - x) / H| < 1 := by
    by_contra h
    exact hcutoff (hcutoffSupport _ (le_of_not_gt h))
  have hright : (X * Real.exp w - x) / H < 1 :=
    (abs_lt.mp hquot).2
  have hnum : X * Real.exp w - x < H := by
    simpa using (div_lt_iff₀ hH).mp hright
  have he11 : 11 < Real.exp (10 : ℝ) := by
    convert Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0) using 1 <;> norm_num
  have hew : Real.exp (10 : ℝ) < Real.exp w :=
    Real.exp_lt_exp.mpr hw
  have hXew : 11 * X < X * Real.exp w := by
    have h := mul_lt_mul_of_pos_left (he11.trans hew) hX
    simpa [mul_comm] using h
  linarith

/-- On the complement of the lower collar inside `[X/2,4X]`, insertion of
the source outer cutoff is pointwise exact. -/
theorem sourcePacketAmplitude_eq_withoutOuter_of_not_mem_lowerOuterCollar
    {X H x w : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hxNoCollar : x ∉ lowerOuterCollar X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    sourcePacketAmplitude X H x cutoff outer w =
      sourcePacketAmplitude X H x cutoff (fun _ ↦ 1) w := by
  by_cases hcutoff : cutoff ((X * Real.exp w - x) / H) = 0
  · simp [sourcePacketAmplitude, hcutoff]
  have hwLower : -10 ≤ w := by
    by_contra h
    exact hxNoCollar
      (mem_lowerOuterCollar_of_cutoff_ne_zero_of_w_lt_neg_ten
        hX hH hHalf hx.1 hcutoffSupport hcutoff (lt_of_not_ge h))
  have hwUpper : w ≤ 10 := by
    by_contra h
    exact hcutoff (cutoff_eq_zero_of_ten_lt_w
      hX hH hHalf hx.2 hcutoffSupport (lt_of_not_ge h))
  have hwScaled : |w / 100| ≤ (1 : ℝ) / 10 := by
    rw [abs_le]
    constructor <;> norm_num at * <;> linarith
  simp [sourcePacketAmplitude, houterOne _ hwScaled]

/-- Packet-level form of the exact outer insertion away from the lower
endpoint collar. -/
theorem sourceStationaryPacket_eq_withoutOuter_of_not_mem_lowerOuterCollar
    {X H x beta t : ℝ} {cutoff outer : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hx : x ∈ Set.Icc (X / 2) (4 * X))
    (hxNoCollar : x ∉ lowerOuterCollar X)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1) :
    sourceStationaryPacket X H x beta t cutoff outer =
      sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1) := by
  unfold sourceStationaryPacket
  apply integral_congr_ae
  filter_upwards with w
  rw [sourcePacketAmplitude_eq_withoutOuter_of_not_mem_lowerOuterCollar
    hX hH hHalf hx hxNoCollar hcutoffSupport houterOne]

/-- The exact correction term missed by the source's outer-cutoff insertion
at `H = X/2`.  A downstream proof must bound this term; it is not discarded. -/
def lowerOuterCollarPairingError
    (X H beta t : ℝ) (cutoff outer : ℝ → ℝ) (g : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ in lowerOuterCollar X,
    g x * (sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1) -
      sourceStationaryPacket X H x beta t cutoff outer)

/-- The literal packet difference whose collar energy is the sole quantitative
endpoint repair. -/
def lowerOuterCollarPacketDifference
    (X H beta t : ℝ) (cutoff outer : ℝ → ℝ) (x : ℝ) : ℂ :=
  Set.indicator (lowerOuterCollar X)
    (fun y ↦ sourceStationaryPacket X H y beta t cutoff (fun _ ↦ 1) -
      sourceStationaryPacket X H y beta t cutoff outer) x

/-- The collar correction is exactly the dual pairing with the packet
difference kernel. -/
theorem lowerOuterCollarPairingError_eq_integral_mul_packetDifference
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ} :
    lowerOuterCollarPairingError X H beta t cutoff outer g =
      ∫ x : ℝ, g x *
        lowerOuterCollarPacketDifference X H beta t cutoff outer x := by
  unfold lowerOuterCollarPairingError lowerOuterCollarPacketDifference
  have hmeas : MeasurableSet (lowerOuterCollar X) := by
    exact measurableSet_Ico
  rw [← integral_indicator hmeas]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ lowerOuterCollar X <;> simp [hx]

/-- Normalized `L²` Cauchy--Schwarz reduces the endpoint correction exactly to
the collar packet-difference energy.  No estimate for that energy is assumed or
hidden here. -/
theorem norm_sq_lowerOuterCollarPairingError_le_packetDifference_energy
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hg : MemLp g 2)
    (hDiff : MemLp
      (lowerOuterCollarPacketDifference X H beta t cutoff outer) 2)
    (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) = 1) :
    ‖lowerOuterCollarPairingError X H beta t cutoff outer g‖ ^ 2 ≤
      ∫ x : ℝ,
        ‖lowerOuterCollarPacketDifference X H beta t cutoff outer x‖ ^ 2 := by
  rw [lowerOuterCollarPairingError_eq_integral_mul_packetDifference]
  exact MAPMRTSourceWholeLineExtension.norm_sq_integral_mul_le_energy
    hg hDiff hgNorm

/-- Exact endpoint split for the source pairing.  Outside the lower collar,
support of `g` and the preceding packet identity remove the difference. -/
theorem integral_mul_packet_withoutOuter_eq_outer_add_lowerOuterCollarPairingError
    {X H beta t : ℝ} {cutoff outer : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHalf : H ≤ X / 2)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterOne : ∀ y, |y| ≤ (1 : ℝ) / 10 → outer y = 1)
    (hNoOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1)))
    (hOuter : Integrable (fun x : ℝ ↦ g x *
      sourceStationaryPacket X H x beta t cutoff outer)) :
    (∫ x : ℝ, g x * sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1)) =
      (∫ x : ℝ, g x * sourceStationaryPacket X H x beta t cutoff outer) +
        lowerOuterCollarPairingError X H beta t cutoff outer g := by
  let F : ℝ → ℂ := fun x ↦ g x *
    sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1)
  let G : ℝ → ℂ := fun x ↦ g x *
    sourceStationaryPacket X H x beta t cutoff outer
  have hdiff : ∀ x, F x - G x =
      Set.indicator (lowerOuterCollar X) (fun y ↦ F y - G y) x := by
    intro x
    by_cases hxI : x ∈ Set.Icc (X / 2) (4 * X)
    · by_cases hxC : x ∈ lowerOuterCollar X
      · simp [hxC]
      · have hpacket :=
          sourceStationaryPacket_eq_withoutOuter_of_not_mem_lowerOuterCollar
            (beta := beta) (t := t)
            hX hH hHalf hxI hxC hcutoffSupport houterOne
        simp [F, G, hxC, hpacket]
    · have hnotC : x ∉ lowerOuterCollar X := by
        intro hxC
        apply hxI
        have he : Real.exp (-10 : ℝ) < 1 :=
          Real.exp_lt_one_iff.mpr (by norm_num)
        constructor
        · exact hxC.1
        · have hXe : X * Real.exp (-10 : ℝ) < X :=
            by simpa using mul_lt_mul_of_pos_left he hX
          linarith [hxC.2]
      simp [F, G, hnotC, hgSupport x hxI]
  have hErr : Integrable
      (Set.indicator (lowerOuterCollar X) (fun x ↦ F x - G x)) := by
    have hFG : Integrable (fun x ↦ F x - G x) := by
      simpa [F, G] using hNoOuter.sub hOuter
    apply hFG.congr
    filter_upwards with x
    exact hdiff x
  calc
    (∫ x : ℝ, g x * sourceStationaryPacket X H x beta t cutoff (fun _ ↦ 1)) =
        ∫ x : ℝ, F x := rfl
    _ = ∫ x : ℝ, (G x + Set.indicator (lowerOuterCollar X)
        (fun y ↦ F y - G y) x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [← hdiff x]
      abel
    _ = (∫ x : ℝ, G x) + ∫ x : ℝ,
        Set.indicator (lowerOuterCollar X) (fun y ↦ F y - G y) x := by
      rw [integral_add hOuter hErr]
    _ = (∫ x : ℝ, g x * sourceStationaryPacket X H x beta t cutoff outer) +
        lowerOuterCollarPairingError X H beta t cutoff outer g := by
      have hmeas : MeasurableSet (lowerOuterCollar X) := by
        exact measurableSet_Ico
      unfold lowerOuterCollarPairingError
      rw [← integral_indicator hmeas]
      simp [F, G, mul_sub]

end

end MAPMRTSourceOuterCutoffEndpoint

#print axioms MAPMRTSourceOuterCutoffEndpoint.mem_lowerOuterCollar_of_cutoff_ne_zero_of_w_lt_neg_ten
#print axioms MAPMRTSourceOuterCutoffEndpoint.cutoff_eq_zero_of_ten_lt_w
#print axioms MAPMRTSourceOuterCutoffEndpoint.sourcePacketAmplitude_eq_withoutOuter_of_not_mem_lowerOuterCollar
#print axioms MAPMRTSourceOuterCutoffEndpoint.sourceStationaryPacket_eq_withoutOuter_of_not_mem_lowerOuterCollar
#print axioms MAPMRTSourceOuterCutoffEndpoint.lowerOuterCollarPairingError_eq_integral_mul_packetDifference
#print axioms MAPMRTSourceOuterCutoffEndpoint.norm_sq_lowerOuterCollarPairingError_le_packetDifference_energy
#print axioms MAPMRTSourceOuterCutoffEndpoint.integral_mul_packet_withoutOuter_eq_outer_add_lowerOuterCollarPairingError
