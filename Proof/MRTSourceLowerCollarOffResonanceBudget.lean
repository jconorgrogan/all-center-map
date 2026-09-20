import MRTSourceLowerCollarOffResonance

/-! # Integrated amplitude budgets on a lower-collar off-resonance cell -/

namespace MAPMRTSourceLowerCollarOffResonanceBudget

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTVanDerCorput
open MAPMRTSourceLowerCollarVdC MAPMRTSourceLowerCollarOffResonance
open MAPMRTSourceLowerCollarAmplitudeGain
open MAPMRTSourcePacketAmplitudeC2

noncomputable section

/-- Exact elementary antiderivative budget used on both off-resonance cells. -/
theorem intervalIntegral_exp_half_mul_le
    {a b C : ℝ} (hab : a ≤ b) (hC : 0 ≤ C) :
    (∫ w : ℝ in a..b, Real.exp (w / 2) * C) ≤
      2 * C * Real.exp (b / 2) := by
  let F : ℝ → ℝ := fun w ↦ 2 * C * Real.exp (w / 2)
  have hD : ∀ w, HasDerivAt F (Real.exp (w / 2) * C) w := by
    intro w
    unfold F
    convert (Real.hasDerivAt_exp (w / 2) |>.scomp w
      ((hasDerivAt_id w).div_const 2)).const_mul (2 * C) using 1 <;> ring
  have hderiv : deriv F = fun w ↦ Real.exp (w / 2) * C := by
    funext w
    exact (hD w).deriv
  have heq : (∫ w : ℝ in a..b, Real.exp (w / 2) * C) =
      2 * C * Real.exp (b / 2) - 2 * C * Real.exp (a / 2) := by
    simpa [F] using intervalIntegral.integral_deriv_eq_sub' F hderiv
      (fun w _ ↦ (hD w).differentiableAt) (by fun_prop)
  rw [heq]
  have : 0 ≤ 2 * C * Real.exp (a / 2) := by positivity
  linarith

/-- A continuous amplitude dominated by `C exp(w/2)` has the corresponding
explicit L1 budget. -/
theorem integral_norm_le_exp_half_budget
    {a b C : ℝ} {f : ℝ → ℂ}
    (hab : a ≤ b) (hC : 0 ≤ C)
    (hf : ContinuousOn f (Set.Icc a b))
    (hpoint : ∀ w ∈ Set.Icc a b, ‖f w‖ ≤ Real.exp (w / 2) * C) :
    (∫ w : ℝ in a..b, ‖f w‖) ≤ 2 * C * Real.exp (b / 2) := by
  calc
    _ ≤ ∫ w : ℝ in a..b, Real.exp (w / 2) * C := by
      apply intervalIntegral.integral_mono_on hab
      · apply ContinuousOn.intervalIntegrable
        simpa [Set.uIcc_of_le hab] using hf.norm
      · exact (by fun_prop : Continuous (fun w : ℝ ↦
          Real.exp (w / 2) * C)).continuousOn.intervalIntegrable
      · exact hpoint
    _ ≤ _ := intervalIntegral_exp_half_mul_le hab hC

/-- All three literal amplitude budgets on any tail interval whose right
endpoint satisfies `exp(b)≤U`. -/
theorem sourceLowerCollarAmplitudeDifference_budgets_on_tailInterval
    {X x a b U B1 B2 Bo1 Bo2 : ℝ}
    {cutoff cutoff' cutoff'' outer outer' outer'' : ℝ → ℝ}
    (hab : a ≤ b) (hX : 0 < X) (hxLower : X / 2 ≤ x)
    (hU : 0 < U) (hexpb : Real.exp b ≤ U)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2)
    (hcutoffSupport : ∀ z, 1 ≤ |z| → cutoff z = 0)
    (hcutoff'Support : ∀ z, 1 ≤ |z| → cutoff' z = 0)
    (hcutoffDeriv : ∀ z, HasDerivAt cutoff (cutoff' z) z)
    (hcutoffSecond : ∀ z, HasDerivAt cutoff' (cutoff'' z) z)
    (hcutoff'Bound : ∀ z, |cutoff' z| ≤ B1)
    (hcutoff''Bound : ∀ z, |cutoff'' z| ≤ B2)
    (houterDeriv : ∀ z, HasDerivAt outer (outer' z) z)
    (houterSecond : ∀ z, HasDerivAt outer' (outer'' z) z)
    (houterBound : ∀ z, |outer z| ≤ 1)
    (houter'Bound : ∀ z, |outer' z| ≤ Bo1)
    (houter''Bound : ∀ z, |outer'' z| ≤ Bo2)
    (hcutoff''Cont : Continuous cutoff'')
    (houter''Cont : Continuous outer'') :
    let C0 := 4 * B1 * U
    let C1 := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
    let C2 := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
      2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
    (∫ w : ℝ in a..b,
      ‖sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w‖) ≤
        2 * C0 * Real.exp (b / 2) ∧
    (∫ w : ℝ in a..b,
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖) ≤
        2 * C1 * Real.exp (b / 2) ∧
    (∫ w : ℝ in a..b,
      ‖sourceLowerCollarAmplitudeDifferenceSecond
        X (X / 2) x cutoff cutoff' cutoff'' outer outer' outer'' w‖) ≤
        2 * C2 * Real.exp (b / 2) := by
  dsimp
  let C0 : ℝ := 4 * B1 * U
  let C1 : ℝ := 2 * B1 * U + 8 * B2 * U ^ 2 + B1 * Bo1 * U / 50
  let C2 : ℝ := B1 * U + 24 * B2 * U ^ 2 + B1 * Bo1 * U / 50 +
    2 * B2 * Bo1 * U ^ 2 / 25 + B1 * Bo2 * U / 5000
  have hBo1 : 0 ≤ Bo1 :=
    (abs_nonneg (outer' 0)).trans (houter'Bound 0)
  have hBo2 : 0 ≤ Bo2 :=
    (abs_nonneg (outer'' 0)).trans (houter''Bound 0)
  have hC0 : 0 ≤ C0 := by unfold C0; positivity
  have hC1 : 0 ≤ C1 := by unfold C1; positivity
  have hC2 : 0 ≤ C2 := by unfold C2; positivity
  have hcutoffCont : Continuous cutoff :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffDeriv z).continuousAt)
  have hcutoff'Cont : Continuous cutoff' :=
    continuous_iff_continuousAt.mpr (fun z ↦ (hcutoffSecond z).continuousAt)
  have houterCont : Continuous outer :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterDeriv z).continuousAt)
  have houter'Cont : Continuous outer' :=
    continuous_iff_continuousAt.mpr (fun z ↦ (houterSecond z).continuousAt)
  have hampCont : ContinuousOn
      (sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer)
      (Set.Icc a b) := by
    apply Continuous.continuousOn
    unfold sourceLowerCollarAmplitudeDifference sourcePacketAmplitude
    fun_prop
  have hamp'Cont : ContinuousOn
      (sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer') (Set.Icc a b) := by
    intro w hw
    have hd := hasDerivAt_sourceLowerCollarAmplitudeDifferenceDeriv
        (X := X) (H := X / 2) (x := x) (w := w)
        hcutoffDeriv hcutoffSecond houterDeriv houterSecond
    exact hd.continuousAt.continuousWithinAt
  have hamp''Cont : ContinuousOn
      (sourceLowerCollarAmplitudeDifferenceSecond
        X (X / 2) x cutoff cutoff' cutoff'' outer outer' outer'')
      (Set.Icc a b) := by
    apply Continuous.continuousOn
    unfold sourceLowerCollarAmplitudeDifferenceSecond sourcePacketAmplitudeSecond
    fun_prop
  have hwU : ∀ w ∈ Set.Icc a b, Real.exp w ≤ U := by
    intro w hw
    exact (Real.exp_le_exp.mpr hw.2).trans hexpb
  have h0point : ∀ w ∈ Set.Icc a b,
      ‖sourceLowerCollarAmplitudeDifference X (X / 2) x cutoff outer w‖ ≤
        Real.exp (w / 2) * C0 := by
    intro w hw
    have h := norm_sourcePacketAmplitude_difference_on_resonanceCell_le
      (X := X) (x := x) (q := U / 2) (w := w) (B := B1)
      hX (by positivity) hxLower (by
        convert hwU w hw using 1 <;> ring) hB1
      hcutoffSupport hcutoffDeriv hcutoff'Bound houterBound
    unfold C0
    change ‖sourcePacketAmplitude X (X / 2) x cutoff (fun _ ↦ 1) w -
      sourcePacketAmplitude X (X / 2) x cutoff outer w‖ ≤ _
    exact h.trans_eq (by ring)
  have h1point : ∀ w ∈ Set.Icc a b,
      ‖sourceLowerCollarAmplitudeDifferenceDeriv
        X (X / 2) x cutoff cutoff' outer outer' w‖ ≤
        Real.exp (w / 2) * C1 := by
    intro w hw
    have h := norm_sourceLowerCollarAmplitudeDifferenceDeriv_on_resonanceCell_le
      (X := X) (x := x) (q := U / 2) (w := w)
      (B1 := B1) (B2 := B2) (Bout := Bo1)
      hX (by positivity) hxLower (by
        convert hwU w hw using 1 <;> ring) hB1 hB2
      hcutoffSupport hcutoff'Support hcutoffDeriv hcutoffSecond
      hcutoff'Bound hcutoff''Bound houterBound houter'Bound
    unfold C1
    convert h using 1 <;> ring
  have h2point : ∀ w ∈ Set.Icc a b,
      ‖sourceLowerCollarAmplitudeDifferenceSecond
        X (X / 2) x cutoff cutoff' cutoff'' outer outer' outer'' w‖ ≤
        Real.exp (w / 2) * C2 := by
    intro w hw
    exact norm_sourceLowerCollarAmplitudeDifferenceSecond_le hX hxLower hU.le
      (hwU w hw) hB1 hB2 hcutoffSupport hcutoff'Support
      hcutoffDeriv hcutoffSecond hcutoff'Bound hcutoff''Bound
      houterBound houter'Bound houter''Bound
  exact ⟨integral_norm_le_exp_half_budget hab hC0 hampCont h0point,
    integral_norm_le_exp_half_budget hab hC1 hamp'Cont h1point,
    integral_norm_le_exp_half_budget hab hC2 hamp''Cont h2point⟩

end
end MAPMRTSourceLowerCollarOffResonanceBudget

#print axioms MAPMRTSourceLowerCollarOffResonanceBudget.intervalIntegral_exp_half_mul_le
#print axioms MAPMRTSourceLowerCollarOffResonanceBudget.integral_norm_le_exp_half_budget
#print axioms MAPMRTSourceLowerCollarOffResonanceBudget.sourceLowerCollarAmplitudeDifference_budgets_on_tailInterval
