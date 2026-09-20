import MRTSourceLowerCollarOffResonanceBudget

/-! # Boundary-aware two-IBP for the stationary packet phase -/

namespace MAPMRTSourceLowerCollarPhaseTwoIBP

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof MAPMRTVanDerCorput
open MAPMRTNonstationaryPhaseInverse
open MAPMRTNonstationaryPhaseTwoIBPEndpointBound

noncomputable section

set_option maxHeartbeats 800000 in
/-- Exact quantitative specialization of the boundary-aware two-IBP engine to
`β X exp(w)+t/(2π)`.  All four cell boundary values remain explicit. -/
theorem norm_stationaryPhaseIntegral_le_two_ibp_endpoint_budgets
    {X beta t a b d P A0 A1 A2 L0 R0 L1 R1 : ℝ}
    {amplitude amplitude' amplitude'' : ℝ → ℂ}
    (hab : a ≤ b) (hd : 0 < d) (hP : 0 ≤ P)
    (hpLower : ∀ w ∈ Set.Icc a b,
      d ≤ |beta * X * Real.exp w + t / (2 * Real.pi)|)
    (hpUpper : ∀ w ∈ Set.Icc a b, |beta * X * Real.exp w| ≤ P)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (ha' : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude' (amplitude'' w) w)
    (ha''Cont : ContinuousOn amplitude'' (Set.Icc a b))
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hA2 : (∫ w : ℝ in a..b, ‖amplitude'' w‖) ≤ A2)
    (hL0 : ‖amplitude a‖ ≤ L0) (hR0 : ‖amplitude b‖ ≤ R0)
    (hL1 : ‖amplitude' a‖ ≤ L1) (hR1 : ‖amplitude' b‖ ≤ R1) :
    ‖∫ w : ℝ in a..b,
        additivePhase (stationaryPacketPhase X beta t w) * amplitude w‖ ≤
      (L0 + R0) * (1 / d) +
      ((L1 + R1) * (1 / d) +
        (L0 + R0) * (P / d ^ 2)) *
          (1 / d) +
      ((1 / d) ^ 2 * A2 +
        3 * (1 / d) * (P / d ^ 2) * A1 +
        ((1 / d) *
            (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) * A0) := by
  let p : ℝ → ℝ := fun w ↦ beta * X * Real.exp w + t / (2 * Real.pi)
  let p' : ℝ → ℝ := fun w ↦ beta * X * Real.exp w
  let E : ℝ → ℂ := fun w ↦ additivePhase (stationaryPacketPhase X beta t w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p'
  let qdd : ℝ → ℂ := inversePhaseDerivativeSecond p p' p'
  have hp0 : ∀ w ∈ Set.Icc a b, p w ≠ 0 := by
    intro w hw hz
    have hl := hpLower w hw
    unfold p at hz
    rw [hz, abs_zero] at hl
    linarith
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
  have hEdCont : ContinuousOn Ed (Set.Icc a b) := by
    have hECont : ContinuousOn E (Set.Icc a b) :=
      fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
    have hpCont : ContinuousOn p (Set.Icc a b) :=
      fun w hw ↦ (hpderiv w hw).continuousAt.continuousWithinAt
    unfold Ed
    exact ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn hpCont)).mul hECont
  have hqddCont : ContinuousOn qdd (Set.Icc a b) := by
    have hpCont : ContinuousOn p (Set.Icc a b) :=
      fun w hw ↦ (hpderiv w hw).continuousAt.continuousWithinAt
    have hp'Cont : ContinuousOn p' (Set.Icc a b) :=
      fun w hw ↦ (hp'deriv w hw).continuousAt.continuousWithinAt
    unfold qdd inversePhaseDerivativeSecond
    apply ContinuousOn.mul
    · apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · exact (hp'Cont.mul hpCont).sub
          (continuousOn_const.mul (hp'Cont.pow 2))
      · exact continuousOn_const.mul (hpCont.pow 3)
      · intro w hw
        exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
          (pow_ne_zero 3 (hp0 w hw))
    · exact continuousOn_const
  have hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w := by
    intro w hw
    exact inversePhaseDerivative_mul_phaseDeriv (hp0 w hw)
  have hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ 1 / d := by
    intro w hw
    exact norm_inversePhaseDerivative_le hd (hpLower w hw)
  have hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ P / d ^ 2 := by
    intro w hw
    exact norm_inversePhaseDerivativeDeriv_le hd hP
      (hpLower w hw) (by
        change |beta * X * Real.exp w| ≤ P
        exact hpUpper w hw)
  have hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤
      P / d ^ 2 + 2 * P ^ 2 / d ^ 3 := by
    intro w hw
    exact norm_inversePhaseDerivativeSecond_le hd hP hP
      (hpLower w hw) (by
        change |beta * X * Real.exp w| ≤ P
        exact hpUpper w hw)
      (by
        change |beta * X * Real.exp w| ≤ P
        exact hpUpper w hw)
  have hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1 := by
    intro w hw
    exact norm_additivePhase _
  exact norm_integral_le_two_ibp_endpoint_budgets hab hE hq hqd ha ha'
    hEdCont hqddCont ha''Cont hinverse hA0 hA1 hA2 hQ0 hQ1 hQ2 hEUnit
    hL0 hR0 hL1 hR1 (by positivity) (by positivity) (by positivity)

end
end MAPMRTSourceLowerCollarPhaseTwoIBP

#print axioms MAPMRTSourceLowerCollarPhaseTwoIBP.norm_stationaryPhaseIntegral_le_two_ibp_endpoint_budgets
