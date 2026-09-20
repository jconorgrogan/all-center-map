import MRTSourcePacketOuterIntersection
import MRTSourcePacketEquation84CollarCollection

/-! Premise-free equation (84) on the outer-intersection collar. -/

namespace MAPMRTSourcePacketEquation84Collar

set_option maxHeartbeats 800000

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof MAPMRTVanDerCorput
open MAPMRTNonstationaryPhaseTwoIBP MAPMRTNonstationaryPhaseInverse
open MAPMRTSourcePacketAmplitudeC2
open MAPMRTSourcePacketOuterIntersection
open MAPMRTSourcePacketEquation84CollarCollection

noncomputable section

/-- The literal two-IBP expression on the intersection of the cutoff and outer
windows. -/
theorem norm_sourceStationaryPacket_equation84_collar_exact
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hCollar : X / 4 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcenter : 4 * max (|beta| * H) (X / H) ≤
      |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let D := |t / (2 * Real.pi) + beta * x|
    let d := 3 * D / 4
    let P := 9 * |beta| * X / 2
    let A0 := 600
    let A1 := 300 + 6 * B1 + 3 * D1
    let A2 := (X / H) *
      (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2)
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (1 / d) ^ 2 * A2 +
        3 * (1 / d) * (P / d ^ 2) * A1 +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) * A0 := by
  dsimp
  let a := sourcePacketIntersectionLeft X H x
  let b := sourcePacketIntersectionRight X H x
  let p : ℝ → ℝ := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi)
  let p' : ℝ → ℝ := fun w ↦ beta * X * Real.exp w
  let E : ℝ → ℂ := fun w ↦ additivePhase (stationaryPacketPhase X beta t w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p'
  let qdd : ℝ → ℂ := inversePhaseDerivativeSecond p p' p'
  let amp : ℝ → ℂ := sourcePacketAmplitude X H x cutoff outer
  let amp' : ℝ → ℂ := sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer'
  let amp'' : ℝ → ℂ :=
    sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer''
  let D := |t / (2 * Real.pi) + beta * x|
  let d := 3 * D / 4
  let P := 9 * |beta| * X / 2
  let A0 := (600 : ℝ)
  let A1 := 300 + 6 * B1 + 3 * D1
  let A2 := (X / H) *
    (100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2)
  have hgeom := sourcePacketIntersection_geometry hX hH hHalf hxLower hxUpper
  have hab : a ≤ b := by simpa [a, b] using hgeom.2.1
  have hratio : 0 < X / H := div_pos hX hH
  have hDpos : 0 < D := by
    have : 0 < 4 * max (|beta| * H) (X / H) := by positivity
    exact lt_of_lt_of_le this (by simpa [D] using hcenter)
  have hdpos : 0 < d := by unfold d; positivity
  have hscale : 4 * |beta| * H ≤ D := by
    calc
      4 * |beta| * H = 4 * (|beta| * H) := by ring
      _ ≤ 4 * max (|beta| * H) (X / H) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      _ ≤ D := by simpa [D] using hcenter
  have hpLower : ∀ w ∈ Set.Icc a b, d ≤ |p w| := by
    intro w hw
    exact stationaryPacketPhase_deriv_lower_on_intersectionWindow
      hX hH hHalf hxLower hxUpper (by simp [D]) hscale
      (by simpa [a, b, p, d] using hw)
  have hp0 : ∀ w ∈ Set.Icc a b, p w ≠ 0 := by
    intro w hw hz
    have := hpLower w hw
    rw [hz, abs_zero] at this
    linarith
  have hpUpper : ∀ w ∈ Set.Icc a b, |p' w| ≤ P := by
    intro w hw
    exact stationaryPacketPhase_exp_deriv_upper_on_intersectionWindow
      hX hH hHalf hxLower hxUpper (by simpa [a, b] using hw)
  have hPnonneg : 0 ≤ P := by unfold P; positivity
  have hphase : ∀ w ∈ Set.Icc a b,
      HasDerivAt (stationaryPacketPhase X beta t) (p w) w := by
    intro w hw
    exact hasDerivAt_stationaryPacketPhase X beta t w
  have hpderiv : ∀ w ∈ Set.Icc a b, HasDerivAt p (p' w) w := by
    intro w hw
    exact hasDerivAt_stationaryPacketPhase_firstDerivative X beta t w
  have hp'deriv : ∀ w ∈ Set.Icc a b, HasDerivAt p' (p' w) w := by
    intro w hw
    unfold p'
    simpa [mul_assoc] using (Real.hasDerivAt_exp w).const_mul (beta * X)
  have hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w := by
    intro w hw
    exact hasDerivAt_additivePhase_comp (hphase w hw)
  have hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w := by
    intro w hw
    exact hasDerivAt_inversePhaseDerivative (hp0 w hw) (hpderiv w hw)
  have hqd : ∀ w ∈ Set.Icc a b, HasDerivAt qd (qdd w) w := by
    intro w hw
    exact hasDerivAt_inversePhaseDerivativeDeriv (hp0 w hw)
      (hpderiv w hw) (hp'deriv w hw)
  have hamp : ∀ w ∈ Set.Icc a b, HasDerivAt amp (amp' w) w := by
    intro w hw
    exact hasDerivAt_sourcePacketAmplitude hcutoffDeriv houterDeriv
  have hamp' : ∀ w ∈ Set.Icc a b, HasDerivAt amp' (amp'' w) w := by
    intro w hw
    exact hasDerivAt_sourcePacketAmplitudeDeriv hcutoffDeriv hcutoffSecond
      houterDeriv houterSecond
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffDeriv y).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (hcutoffSecond y).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterDeriv y).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun y ↦ (houterSecond y).continuousAt)
  have hEdCont : ContinuousOn Ed (Set.Icc a b) := by
    have hECont : ContinuousOn E (Set.Icc a b) :=
      fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
    have hpCont : ContinuousOn p (Set.Icc a b) :=
      fun w hw ↦ (hpderiv w hw).continuousAt.continuousWithinAt
    unfold Ed
    exact ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn hpCont)).mul hECont
  have hqddCont : ContinuousOn qdd (Set.Icc a b) := by
    unfold qdd inversePhaseDerivativeSecond p p'
    apply ContinuousOn.mul
    · apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · fun_prop
      · fun_prop
      · intro w hw
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (pow_ne_zero 3 (hp0 w hw))
    · exact continuousOn_const
  have hamp''Cont : ContinuousOn amp'' (Set.Icc a b) := by
    unfold amp'' sourcePacketAmplitudeSecond
    fun_prop
  have hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w := by
    intro w hw
    exact inversePhaseDerivative_mul_phaseDeriv (hp0 w hw)
  have hends := sourcePacketAmplitude_intersection_endpoints
    hX hH hHalf hxLower hxUpper
    (hcutoffSupport (-1) (by norm_num)) (hcutoffSupport 1 (by norm_num))
    (hcutoff'Support (-1) (by norm_num)) (hcutoff'Support 1 (by norm_num))
    (houterSupport (-1) (by norm_num)) (houter'Support (-1) (by norm_num))
  have hA0 : (∫ w : ℝ in a..b, ‖amp w‖) ≤ A0 := by
    exact integral_norm_sourcePacketAmplitude_on_intersection_le
      hX hH hHalf hxLower hxUpper hcutoffBound houterBound hcutoffCont houterCont
  have hA1 : (∫ w : ℝ in a..b, ‖amp' w‖) ≤ A1 := by
    exact integral_norm_sourcePacketAmplitudeDeriv_on_intersection_le
      hX hH hHalf hxLower hxUpper hcutoffBound houterBound houter'Bound
      hcutoffDeriv houterDeriv hcutoff'Cont houter'Cont hcutoff'Int hD1
  have hA2 : (∫ w : ℝ in a..b, ‖amp'' w‖) ≤ A2 := by
    exact integral_norm_sourcePacketAmplitudeSecond_on_intersection_le
      hX hH hCollar hHalf hxLower hxUpper hcutoffBound houterBound
      houter'Bound houter''Bound hcutoffDeriv hcutoffSecond houterDeriv houterSecond
      hcutoff''Cont houter''Cont hcutoff'Int hcutoff''Int hD1 hD2
  have hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ 1 / d := by
    intro w hw
    exact norm_inversePhaseDerivative_le hdpos (hpLower w hw)
  have hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ P / d ^ 2 := by
    intro w hw
    exact norm_inversePhaseDerivativeDeriv_le hdpos hPnonneg
      (hpLower w hw) (hpUpper w hw)
  have hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤
      P / d ^ 2 + 2 * P ^ 2 / d ^ 3 := by
    intro w hw
    exact norm_inversePhaseDerivativeSecond_le hdpos hPnonneg hPnonneg
      (hpLower w hw) (hpUpper w hw) (hpUpper w hw)
  have hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1 := by
    intro w hw
    exact norm_additivePhase _
  have hibp := norm_integral_le_two_ibp_budgets hab hE hq hqd hamp hamp'
    hEdCont hqddCont hamp''Cont hinverse hends.1 hends.2.1 hends.2.2.1 hends.2.2.2
    hA0 hA1 hA2 hQ0 hQ1 hQ2 hEUnit (by positivity) (by positivity) (by positivity)
  rw [sourceStationaryPacket_eq_onIntersectionWindow hX hH hHalf hxLower hxUpper
    hcutoffSupport houterSupport]
  exact hibp

/-- Premise-free source-facing equation (84) throughout the missing collar. -/
theorem norm_sourceStationaryPacket_equation84_collar
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H)
    (hCollar : X / 4 < H) (hHalf : H ≤ X / 2)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcenter : 4 * max (|beta| * H) (X / H) ≤ |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
    (houterSupport : ∀ y, 1 ≤ |y| → outer y = 0)
    (houter'Support : ∀ y, 1 ≤ |y| → outer' y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (houterBound : ∀ y, |outer y| ≤ 1)
    (houter'Bound : ∀ y, |outer' y| ≤ B1)
    (houter''Bound : ∀ y, |outer'' y| ≤ B2)
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffSecond : ∀ y, HasDerivAt cutoff' (cutoff'' y) y)
    (houterDeriv : ∀ y, HasDerivAt outer (outer' y) y)
    (houterSecond : ∀ y, HasDerivAt outer' (outer'' y) y)
    (hcutoff''Cont : Continuous cutoff'') (houter''Cont : Continuous outer'')
    (hcutoff'Int : Integrable (fun y ↦ |cutoff' y|))
    (hcutoff''Int : Integrable (fun y ↦ |cutoff'' y|))
    (hD1 : (∫ y : ℝ, |cutoff' y|) ≤ D1)
    (hD2 : (∫ y : ℝ, |cutoff'' y|) ≤ D2) :
    let D := |t / (2 * Real.pi) + beta * x|
    let K1 := 300 + 6 * B1 + 3 * D1
    let K2 := 100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (150000 + 24 * K1 + 4 * K2) * (X / H) / D ^ 2 := by
  dsimp
  let D := |t / (2 * Real.pi) + beta * x|
  let R := X / H
  let P := 9 * |beta| * X / 2
  let A0 := (600 : ℝ)
  let K1 := 300 + 6 * B1 + 3 * D1
  let K2 := 100 + 10 * B1 + B2 + 10 * (1 + B1) * D1 + 14 * D2
  let A1 := K1
  let A2 := R * K2
  have hexact := norm_sourceStationaryPacket_equation84_collar_exact
    hX hH hCollar hHalf hxLower hxUpper hcenter hcutoffSupport hcutoff'Support
    houterSupport houter'Support hcutoffBound houterBound houter'Bound houter''Bound
    hcutoffDeriv hcutoffSecond houterDeriv houterSecond hcutoff''Cont houter''Cont
    hcutoff'Int hcutoff''Int hD1 hD2
  have hDpos : 0 < D := by
    have : 0 < 4 * max (|beta| * H) (X / H) := by positivity
    exact lt_of_lt_of_le this (by simpa [D] using hcenter)
  have hRLower : 2 ≤ R := by unfold R; rw [le_div_iff₀ hH]; linarith
  have hRUpper : R ≤ 4 := by unfold R; rw [div_le_iff₀ hH]; linarith
  have hP0 : 0 ≤ P := by unfold P; positivity
  have hscale : 4 * |beta| * H ≤ D := by
    calc
      4 * |beta| * H = 4 * (|beta| * H) := by ring
      _ ≤ 4 * max (|beta| * H) (X / H) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      _ ≤ D := by simpa [D] using hcenter
  have hP : P ≤ 2 * R * D := by
    unfold P R
    have hm := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 9 * X / (8 * H))
    calc
      9 * |beta| * X / 2 = (9 * X / (8 * H)) * (4 * |beta| * H) := by
        field_simp [ne_of_gt hH]
        ring
      _ ≤ (9 * X / (8 * H)) * D := hm
      _ ≤ 2 * (X / H) * D := by
        gcongr
        field_simp [ne_of_gt hH]
        nlinarith [hX]
  have hB1 : 0 ≤ B1 := le_trans (abs_nonneg (outer' 0)) (houter'Bound 0)
  have hB2 : 0 ≤ B2 := le_trans (abs_nonneg (outer'' 0)) (houter''Bound 0)
  have hD1n : 0 ≤ D1 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD1
  have hD2n : 0 ≤ D2 := le_trans (integral_nonneg (fun _ ↦ abs_nonneg _)) hD2
  have hK1 : 0 ≤ K1 := by unfold K1; positivity
  have hK2 : 0 ≤ K2 := by unfold K2; positivity
  have hA0n : 0 ≤ A0 := by unfold A0; norm_num
  have hA1n : 0 ≤ A1 := by unfold A1; exact hK1
  have hA2n : 0 ≤ A2 := by unfold A2; positivity
  have hcollect := equation84_collar_budget_collection
    (D := D) (R := R) (P := P) (A0 := A0) (A1 := A1) (A2 := A2)
    (K1 := K1) (K2 := K2) hDpos hRLower hRUpper hP hP0
    hA0n hA1n hA2n hK1 hK2 (by simp [A0]) (by simp [A1]) (by simp [A2])
  exact hexact.trans (by simpa [D, R, P, A0, A1, A2, K1, K2] using hcollect)

#print axioms norm_sourceStationaryPacket_equation84_collar_exact
#print axioms norm_sourceStationaryPacket_equation84_collar

end
end MAPMRTSourcePacketEquation84Collar
