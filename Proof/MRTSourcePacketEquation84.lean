import MRTSourcePacketAmplitudeBudgets

/-! MRT equation (84) on the exact logarithmic packet window. -/

namespace MAPMRTSourcePacketEquation84

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof MAPMRTVanDerCorput
open MAPMRTNonstationaryPhaseTwoIBP MAPMRTNonstationaryPhaseInverse
open MAPMRTSourcePacketAmplitudeC2 MAPMRTSourcePacketAmplitudeC2Budget
open MAPMRTSourcePacketAmplitudeBudgets

noncomputable section

/-- The exact quantitative two-IBP estimate behind (84).  All three amplitude
budgets are proved from the literal source cutoffs; the displayed expression
is the direct output of the reusable two-IBP engine before harmless constant
collection. -/
theorem norm_sourceStationaryPacket_equation84_exact
    {X H x beta t D1 D2 B1 B2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hcenter : 4 * max (|beta| * H) (X / H) ≤
      |t / (2 * Real.pi) + beta * x|)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoff'Support : ∀ y, 1 ≤ |y| → cutoff' y = 0)
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
    let P := 17 * |beta| * X / 4
    let A0 := 24 * H / X
    let A1 := 10 * (1 + B1) * (1 + D1)
    let A2 := (X / H) *
      (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)
    ‖sourceStationaryPacket X H x beta t cutoff outer‖ ≤
      (1 / d) ^ 2 * A2 +
        3 * (1 / d) * (P / d ^ 2) * A1 +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) * A0 := by
  dsimp
  let a : ℝ := Real.log ((x - H) / X)
  let b : ℝ := Real.log ((x + H) / X)
  let p : ℝ → ℝ := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi)
  let p' : ℝ → ℝ := fun w ↦ beta * X * Real.exp w
  let E : ℝ → ℂ := fun w ↦ additivePhase (stationaryPacketPhase X beta t w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p'
  let qdd : ℝ → ℂ := inversePhaseDerivativeSecond p p' p'
  let amp : ℝ → ℂ := sourcePacketAmplitude X H x cutoff outer
  let amp' : ℝ → ℂ :=
    sourcePacketAmplitudeDeriv X H x cutoff cutoff' outer outer'
  let amp'' : ℝ → ℂ :=
    sourcePacketAmplitudeSecond X H x cutoff cutoff' cutoff'' outer outer' outer''
  let D : ℝ := |t / (2 * Real.pi) + beta * x|
  let d : ℝ := 3 * D / 4
  let P : ℝ := 17 * |beta| * X / 4
  let A0 : ℝ := 24 * H / X
  let A1 : ℝ := 10 * (1 + B1) * (1 + D1)
  let A2 : ℝ := (X / H) *
    (10 + 10 * (1 + B1) * D1 + 20 * D2 + B1 + B2)
  have hxMinus : 0 < x - H := by linarith
  have hxPlus : 0 < x + H := by linarith
  have hab : a ≤ b := by
    unfold a b
    apply Real.log_le_log (div_pos hxMinus hX)
    exact div_le_div_of_nonneg_right (by linarith) hX.le
  have hDpos : 0 < D := by
    have hratio : 0 < X / H := div_pos hX hH
    have : 0 < 4 * max (|beta| * H) (X / H) := by positivity
    exact lt_of_lt_of_le this hcenter
  have hdpos : 0 < d := by unfold d; positivity
  have hscale : 4 * |beta| * H ≤ D := by
    calc
      4 * |beta| * H = 4 * (|beta| * H) := by ring
      _ ≤ 4 * max (|beta| * H) (X / H) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
      _ ≤ D := by simpa [D] using hcenter
  have hpLower : ∀ w ∈ Set.Icc a b, d ≤ |p w| := by
    intro w hw
    exact stationaryPacketPhase_deriv_lower_on_cutoffWindow hX hH hHquarter
      hxLower hDpos.le (by simp [D]) hscale
      (by simpa [sourcePacketWindow, a, b] using hw)
  have hp0 : ∀ w ∈ Set.Icc a b, p w ≠ 0 := by
    intro w hw hz
    have := hpLower w hw
    rw [hz, abs_zero] at this
    linarith
  have hpUpper : ∀ w ∈ Set.Icc a b, |p' w| ≤ P := by
    intro w hw
    have hexpUpper : Real.exp w ≤ (x + H) / X := by
      rw [← Real.exp_log (div_pos hxPlus hX)]
      exact Real.exp_le_exp.mpr hw.2
    have hxe : X * Real.exp w ≤ x + H := by
      simpa [mul_comm] using (le_div_iff₀ hX).mp hexpUpper
    have hxH : x + H ≤ 17 * X / 4 := by linarith
    unfold p' P
    rw [abs_mul, abs_mul, abs_of_pos hX, abs_of_pos (Real.exp_pos w)]
    calc
      |beta| * X * Real.exp w = |beta| * (X * Real.exp w) := by ring
      _ ≤ |beta| * (17 * X / 4) :=
        mul_le_mul_of_nonneg_left (hxe.trans hxH) (abs_nonneg beta)
      _ = 17 * |beta| * X / 4 := by ring
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
  have hends := sourcePacketAmplitude_cutoffWindow_endpoints
    (X := X) (H := H) (x := x) (cutoff := cutoff) (cutoff' := cutoff')
    (outer := outer) (outer' := outer') hX hH hHquarter hxLower
    (hcutoffSupport (-1) (by norm_num)) (hcutoffSupport 1 (by norm_num))
    (hcutoff'Support (-1) (by norm_num)) (hcutoff'Support 1 (by norm_num))
  have hA0 : (∫ w : ℝ in a..b, ‖amp w‖) ≤ A0 := by
    exact integral_norm_sourcePacketAmplitude_le hX hH hHquarter hxLower hxUpper
      hcutoffBound houterBound hcutoffCont houterCont
  have hA1 : (∫ w : ℝ in a..b, ‖amp' w‖) ≤ A1 := by
    exact integral_norm_sourcePacketAmplitudeDeriv_on_cutoffWindow_le
      hX hH hHquarter hxLower hxUpper hcutoffBound houterBound houter'Bound
      hcutoffDeriv houterDeriv hcutoff'Cont houter'Cont hcutoff'Int hD1
  have hA2 : (∫ w : ℝ in a..b, ‖amp'' w‖) ≤ A2 := by
    exact integral_norm_sourcePacketAmplitudeSecond_le
      hX hH hHquarter hxLower hxUpper hcutoffBound houterBound
      houter'Bound houter''Bound hcutoffDeriv hcutoffSecond
      houterDeriv houterSecond hcutoff''Cont houter''Cont
      hcutoff'Int hcutoff''Int hD1 hD2
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
    hEdCont hqddCont hamp''Cont hinverse hends.1 hends.2.1
    hends.2.2.1 hends.2.2.2 hA0 hA1 hA2 hQ0 hQ1 hQ2 hEUnit
    (by positivity) (by positivity) (by positivity)
  rw [sourceStationaryPacket_eq_onCutoffWindow hX hH hHquarter hxLower
    hcutoffSupport]
  exact hibp

#print axioms norm_sourceStationaryPacket_equation84_exact

end
end MAPMRTSourcePacketEquation84
