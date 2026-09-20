import MRTOffDiagonalPhase

/-!
# The distinct-frequency two-IBP specialization

This module specializes the proved inverse-phase and two-integration-by-parts
engines to the exact phase after `w'=w+h`.  It leaves only the literal
truncated-amplitude localization and its three `L¹` budgets.
-/

namespace MAPMRTOffDiagonalTwoIBP

open MeasureTheory Set
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTVanDerCorputProof MAPMRTVanDerCorput
open MAPMRTNonstationaryPhaseTwoIBP MAPMRTNonstationaryPhaseInverse
open MAPMRTOffDiagonalPhase

noncomputable section

/-- Exact two-IBP bound for the off-diagonal phase.  The large constant
`8π` is the source-faithful threshold which makes the phase derivative
uniformly invertible on the localized amplitude interval. -/
theorem norm_offDiagonalIntegral_le_two_ibp_budgets
    {X H beta s s' h a b A0 A1 A2 : ℝ}
    {amplitude amplitude' amplitude'' : ℝ → ℂ}
    (hab : a ≤ b) (hH : 0 < H) (hhard : 1 < |beta| * H)
    (hsep : 8 * Real.pi * |beta| * H ≤ |s - s'|)
    (hclose : ∀ w ∈ Set.Icc a b,
      |X * Real.exp w - X * Real.exp (w + h)| ≤ 2 * H)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (ha' : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude' (amplitude'' w) w)
    (ha''Cont : ContinuousOn amplitude'' (Set.Icc a b))
    (ha_left : amplitude a = 0) (ha_right : amplitude b = 0)
    (ha'_left : amplitude' a = 0) (ha'_right : amplitude' b = 0)
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hA2 : (∫ w : ℝ in a..b, ‖amplitude'' w‖) ≤ A2) :
    let d := |s - s'| / (4 * Real.pi)
    let P := |s - s'|
    ‖∫ w : ℝ in a..b,
        additivePhase (offDiagonalPhase X beta s s' h w) * amplitude w‖ ≤
      (1 / d) ^ 2 * A2 + 3 * (1 / d) * (P / d ^ 2) * A1 +
        ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
          (P / d ^ 2) ^ 2) * A0 := by
  dsimp
  let p : ℝ → ℝ := offDiagonalPhaseDeriv X beta s s' h
  let p' : ℝ → ℝ := offDiagonalPhaseSecond X beta h
  let E : ℝ → ℂ := fun w ↦
    additivePhase (offDiagonalPhase X beta s s' h w)
  let Ed : ℝ → ℂ := fun w ↦
    ((2 * Real.pi : ℂ) * Complex.I * (p w : ℂ)) * E w
  let q : ℝ → ℂ := inversePhaseDerivative p
  let qd : ℝ → ℂ := inversePhaseDerivativeDeriv p p'
  let qdd : ℝ → ℂ := inversePhaseDerivativeSecond p p' p'
  let d : ℝ := |s - s'| / (4 * Real.pi)
  let P : ℝ := |s - s'|
  have hdelta : 0 < |s - s'| := by
    have hbetaH : 0 < |beta| * H := lt_trans zero_lt_one hhard
    have hpi : 0 < 8 * Real.pi := by positivity
    have : 0 < 8 * Real.pi * (|beta| * H) := mul_pos hpi hbetaH
    rw [show 8 * Real.pi * (|beta| * H) =
      8 * Real.pi * |beta| * H by ring] at this
    exact this.trans_le hsep
  have hd : 0 < d := by unfold d; positivity
  have hP : 0 ≤ P := by unfold P; positivity
  have hpLower : ∀ w ∈ Set.Icc a b, d ≤ |p w| := by
    intro w hw
    exact offDiagonalPhaseDeriv_lower hH (hclose w hw) hsep
  have hp0 : ∀ w ∈ Set.Icc a b, p w ≠ 0 := by
    intro w hw hpz
    have hl := hpLower w hw
    rw [hpz, abs_zero] at hl
    linarith
  have hpUpper : ∀ w ∈ Set.Icc a b, |p' w| ≤ P := by
    intro w hw
    exact (offDiagonalPhase_higherDerivs_upper (hclose w hw) hsep).1
  have hphase : ∀ w ∈ Set.Icc a b,
      HasDerivAt (offDiagonalPhase X beta s s' h) (p w) w := by
    intro w hw
    exact hasDerivAt_offDiagonalPhase X beta s s' h w
  have hpderiv : ∀ w ∈ Set.Icc a b, HasDerivAt p (p' w) w := by
    intro w hw
    exact hasDerivAt_offDiagonalPhaseDeriv X beta s s' h w
  have hp'deriv : ∀ w ∈ Set.Icc a b, HasDerivAt p' (p' w) w := by
    intro w hw
    exact hasDerivAt_offDiagonalPhaseSecond X beta h w
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
  have hpCont : ContinuousOn p (Set.Icc a b) :=
    fun w hw ↦ (hpderiv w hw).continuousAt.continuousWithinAt
  have hp'Cont : ContinuousOn p' (Set.Icc a b) :=
    fun w hw ↦ (hp'deriv w hw).continuousAt.continuousWithinAt
  have hqddCont : ContinuousOn qdd (Set.Icc a b) := by
    unfold qdd inversePhaseDerivativeSecond p p'
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
      (hpLower w hw) (hpUpper w hw)
  have hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤
      P / d ^ 2 + 2 * P ^ 2 / d ^ 3 := by
    intro w hw
    exact norm_inversePhaseDerivativeSecond_le hd hP hP
      (hpLower w hw) (hpUpper w hw) (hpUpper w hw)
  have hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1 := by
    intro w hw
    exact norm_additivePhase _
  exact norm_integral_le_two_ibp_budgets hab hE hq hqd ha ha'
    hEdCont hqddCont ha''Cont hinverse ha_left ha_right ha'_left ha'_right
    hA0 hA1 hA2 hQ0 hQ1 hQ2 hEUnit
    (by positivity) (by positivity) (by positivity)

#print axioms norm_offDiagonalIntegral_le_two_ibp_budgets

end
end MAPMRTOffDiagonalTwoIBP
