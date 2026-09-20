import MRTPacketEnergy
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The literal `x` support in MRT equations (80)--(84)

The packet occurs after duality against a function `g` supported on
`[X/2,4X]`.  We record that restriction explicitly.  This is essential for the
small-curvature estimate `Jₓ(t) ≪ H/X`; the unrestricted formula in `x` does
not have that bound.
-/

namespace MAPMRTSourcePacketSupport

open MeasureTheory Set
open MAPMRTProposition51HardBranch
open MAPMRTVanDerCorput

noncomputable section

/-- The equation-(80) packet on the support of the dual function in (72),(73). -/
def sourceRestrictedPacket
    (X H beta t : ℝ) (cutoff outerCutoff : ℝ → ℝ) (x : ℝ) : ℂ :=
  Set.indicator (Set.Icc (X / 2) (4 * X))
    (fun y ↦ sourceStationaryPacket X H y beta t cutoff outerCutoff) x

/-- With continuous cutoffs, the unrestricted packet depends continuously on
the dual variable `x`. -/
theorem continuous_sourceStationaryPacket_in_x
    {X H beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outerCutoff)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0) :
    Continuous (fun x ↦
      sourceStationaryPacket X H x beta t cutoff outerCutoff) := by
  have hinterval : Continuous (fun x ↦
      stationaryPacketOn X beta t
        (sourcePacketAmplitude X H x cutoff outerCutoff) (-100) 100) := by
    unfold stationaryPacketOn
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    unfold Function.uncurry sourcePacketAmplitude
    have hadd : Continuous MAPMRTCorollary53Source.additivePhase :=
      continuous_iff_continuousAt.mpr (fun y ↦
        (MAPMRTVanDerCorputProof.hasDerivAt_additivePhase y).continuousAt)
    have hphaseArg : Continuous (fun a : ℝ × ℝ ↦
        beta * X * Real.exp a.2 + t * a.2 / (2 * Real.pi)) := by
      fun_prop
    apply (hadd.comp (by
      simpa [stationaryPacketPhase] using hphaseArg)).mul
    fun_prop
  convert hinterval using 1
  funext x
  exact sourceStationaryPacket_eq_onOuterWindow houterSupport

/-- The square of the source packet, restricted to the literal support
`[X/2,4X]` of `g`, is integrable. -/
theorem integrable_norm_sourceRestrictedPacket_sq
    {X H beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outerCutoff)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0) :
    Integrable (fun x ↦
      ‖sourceRestrictedPacket X H beta t cutoff outerCutoff x‖ ^ 2) := by
  let J : ℝ → ℂ := fun x ↦
    sourceStationaryPacket X H x beta t cutoff outerCutoff
  have hJ : Continuous J :=
    continuous_sourceStationaryPacket_in_x hcutoff houter houterSupport
  have hsq : Continuous (fun x ↦ ‖J x‖ ^ 2) := hJ.norm.pow 2
  have hcompact : IntegrableOn (fun x ↦ ‖J x‖ ^ 2)
      (Set.Icc (X / 2) (4 * X)) :=
    hsq.continuousOn.integrableOn_compact isCompact_Icc
  have hindicator : Integrable
      (Set.indicator (Set.Icc (X / 2) (4 * X)) (fun x ↦ ‖J x‖ ^ 2)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact hcompact
  convert hindicator using 1
  funext x
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · simp [sourceRestrictedPacket, J, hx]
  · simp [sourceRestrictedPacket, J, hx]

/-- The restricted source packet is an `L²` function of `x`. -/
theorem memLp_sourceRestrictedPacket
    {X H beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hcutoff : Continuous cutoff) (houter : Continuous outerCutoff)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0) :
    MemLp (fun x ↦
      sourceRestrictedPacket X H beta t cutoff outerCutoff x) 2 := by
  have hcontinuous := continuous_sourceStationaryPacket_in_x
    (X := X) (H := H) (beta := beta) (t := t)
    hcutoff houter houterSupport
  have hmeas : AEStronglyMeasurable (fun x ↦
      sourceRestrictedPacket X H beta t cutoff outerCutoff x) := by
    unfold sourceRestrictedPacket
    exact hcontinuous.aestronglyMeasurable.indicator measurableSet_Icc
  exact (memLp_two_iff_integrable_sq_norm hmeas).2
    (integrable_norm_sourceRestrictedPacket_sq hcutoff houter houterSupport)

/-- The fixed outer window gives a global absolute bound for the literal
packet.  This is used only when `H` is a fixed proportion of `X`. -/
theorem norm_sourceStationaryPacket_le_outer
    {X H x beta t : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1) :
    ‖sourceStationaryPacket X H x beta t cutoff outerCutoff‖ ≤
      200 * Real.exp 50 := by
  rw [sourceStationaryPacket_eq_onOuterWindow houterSupport]
  refine (norm_stationaryPacketOn_le (C := Real.exp 50) ?_).trans_eq ?_
  · intro w hw
    have hw' : w ∈ Set.Icc (-100 : ℝ) 100 := by
      simpa [Set.uIcc_of_le (by norm_num : (-100 : ℝ) ≤ 100)] using hw
    unfold sourcePacketAmplitude
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hexp : Real.exp (w / 2) ≤ Real.exp 50 := by
      apply Real.exp_le_exp.mpr
      linarith [hw'.2]
    calc
      Real.exp (w / 2) * |cutoff ((X * Real.exp w - x) / H)| *
          |outerCutoff (w / 100)| ≤ Real.exp 50 * 1 * 1 := by
        gcongr
        · exact hcutoffBound _
        · exact houterBound _
      _ = Real.exp 50 := by ring
  · norm_num

/-- The triangle-inequality estimate in the second case below (83), on the
literal support of `g`, throughout the printed half-range `H ≤ X/2`.

For `H ≤ X/4` this is the sharp logarithmic-window calculation.  In the short
remaining collar `X/4 < H ≤ X/2`, the fixed outer window is enough. -/
theorem norm_sourceRestrictedPacket_le_trivial
    {X H beta t x : ℝ} {cutoff outerCutoff : ℝ → ℝ}
    (hH : 1 ≤ H) (hHalf : H ≤ X / 2)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outerCutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outerCutoff y| ≤ 1) :
    ‖sourceRestrictedPacket X H beta t cutoff outerCutoff x‖ ≤
      800 * Real.exp 50 * H / X := by
  have hX : 0 < X := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · simp only [sourceRestrictedPacket, Set.indicator_of_mem hx]
    by_cases hquarter : H ≤ X / 4
    · have hsmall := MAPMRTProposition51HardBranch.norm_sourceStationaryPacket_le
        (beta := beta) (t := t) hX hHpos hquarter hx.1 hx.2
        hcutoffSupport hcutoffBound houterBound
      refine hsmall.trans ?_
      have hexp : 1 ≤ Real.exp 50 := by
        simpa using Real.exp_one_le_iff.mpr (by norm_num : (0 : ℝ) ≤ 50)
      have hscale : 24 ≤ 800 * Real.exp 50 := by nlinarith
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hscale (le_trans zero_le_one hH)) hX.le
    · have houterPacket := norm_sourceStationaryPacket_le_outer
        (X := X) (H := H) (x := x) (beta := beta) (t := t)
        houterSupport hcutoffBound houterBound
      refine houterPacket.trans ?_
      have hquarter' : X / 4 < H := lt_of_not_ge hquarter
      have hexp : 0 < Real.exp 50 := Real.exp_pos 50
      apply (le_div_iff₀ hX).2
      nlinarith
  · simp [sourceRestrictedPacket, hx]
    positivity

#print axioms MAPMRTSourcePacketSupport.integrable_norm_sourceRestrictedPacket_sq
#print axioms MAPMRTSourcePacketSupport.memLp_sourceRestrictedPacket
#print axioms MAPMRTSourcePacketSupport.norm_sourceRestrictedPacket_le_trivial

end
end MAPMRTSourcePacketSupport
