import MRTNonstationaryPhaseInverse

/-!
# One integration by parts for the low-frequency MRT projection

The low-frequency argument on p. 47 uses exactly one integration by parts.
This module provides that calculus step without importing the stronger
two-integration engine or hiding endpoint terms.
-/

namespace MAPMRTProposition51ProjectionOneIBP

open MeasureTheory Set

noncomputable section

/-- Exact one-fold integration-by-parts identity. -/
theorem one_integration_by_parts_identity
    {a b : ℝ} {E Ed q qd amplitude amplitude' : ℝ → ℂ}
    (hab : a ≤ b)
    (hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w)
    (hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (hEdCont : ContinuousOn Ed (Set.Icc a b))
    (hqdCont : ContinuousOn qd (Set.Icc a b))
    (ha'Cont : ContinuousOn amplitude' (Set.Icc a b))
    (hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w)
    (ha_left : amplitude a = 0) (ha_right : amplitude b = 0) :
    (∫ w : ℝ in a..b, E w * amplitude w) =
      -(∫ w : ℝ in a..b,
        (amplitude' w * q w + amplitude w * qd w) * E w) := by
  let u : ℝ → ℂ := fun w ↦ amplitude w * q w
  let ud : ℝ → ℂ := fun w ↦ amplitude' w * q w + amplitude w * qd w
  have hu : ∀ w ∈ Set.Icc a b, HasDerivAt u (ud w) w := by
    intro w hw
    exact (ha w hw).mul (hq w hw)
  have hECont : ContinuousOn E (Set.Icc a b) :=
    fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hqCont : ContinuousOn q (Set.Icc a b) :=
    fun w hw ↦ (hq w hw).continuousAt.continuousWithinAt
  have haCont : ContinuousOn amplitude (Set.Icc a b) :=
    fun w hw ↦ (ha w hw).continuousAt.continuousWithinAt
  have huCont : ContinuousOn u (Set.Icc a b) := haCont.mul hqCont
  have hudCont : ContinuousOn ud (Set.Icc a b) := by
    unfold ud
    exact (ha'Cont.mul hqCont).add (haCont.mul hqdCont)
  have hiEd : IntervalIntegrable Ed volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hEdCont
  have hiud : IntervalIntegrable ud volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hudCont
  have hibp : (∫ w : ℝ in a..b, u w * Ed w) =
      u b * E b - u a * E a - ∫ w : ℝ in a..b, ud w * E w := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (by simpa [Set.uIcc_of_le hab] using hu)
      (by simpa [Set.uIcc_of_le hab] using hE) hiud hiEd
  have hrewrite : ∀ w ∈ Set.uIcc a b,
      E w * amplitude w = u w * Ed w := by
    intro w hw
    have hw' : w ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hw
    unfold u
    rw [mul_assoc, hinverse w hw']
    ac_rfl
  rw [intervalIntegral.integral_congr hrewrite, hibp]
  simp [u, ud, ha_left, ha_right]

/-- Quantitative one-IBP consequence with separate amplitude and inverse-phase
budgets.  This is the exact norm interface used by the p. 47 specialization. -/
theorem norm_integral_le_one_ibp_budgets
    {a b A0 A1 Q0 Q1 : ℝ}
    {E Ed q qd amplitude amplitude' : ℝ → ℂ}
    (hab : a ≤ b)
    (hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w)
    (hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (hEdCont : ContinuousOn Ed (Set.Icc a b))
    (hqdCont : ContinuousOn qd (Set.Icc a b))
    (ha'Cont : ContinuousOn amplitude' (Set.Icc a b))
    (hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w)
    (ha_left : amplitude a = 0) (ha_right : amplitude b = 0)
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ Q0)
    (hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ Q1)
    (hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1)
    (hQ0nonneg : 0 ≤ Q0) (hQ1nonneg : 0 ≤ Q1) :
    ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤ Q0 * A1 + Q1 * A0 := by
  rw [one_integration_by_parts_identity hab hE hq ha hEdCont hqdCont ha'Cont
    hinverse ha_left ha_right, norm_neg]
  let integrand : ℝ → ℂ := fun w ↦
    (amplitude' w * q w + amplitude w * qd w) * E w
  have hqCont : ContinuousOn q (Set.Icc a b) :=
    fun w hw ↦ (hq w hw).continuousAt.continuousWithinAt
  have haCont : ContinuousOn amplitude (Set.Icc a b) :=
    fun w hw ↦ (ha w hw).continuousAt.continuousWithinAt
  have hECont : ContinuousOn E (Set.Icc a b) :=
    fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable integrand volume a b := by
    apply ContinuousOn.intervalIntegrable
    have hiCont : ContinuousOn integrand (Set.Icc a b) := by
      unfold integrand
      exact ((ha'Cont.mul hqCont).add (haCont.mul hqdCont)).mul hECont
    simpa [Set.uIcc_of_le hab] using hiCont
  have hmajorInt : IntervalIntegrable
      (fun w ↦ Q0 * ‖amplitude' w‖ + Q1 * ‖amplitude w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using
      (continuousOn_const.mul ha'Cont.norm).add
        (continuousOn_const.mul haCont.norm)
  calc
    ‖∫ w : ℝ in a..b, integrand w‖ ≤
        ∫ w : ℝ in a..b, ‖integrand w‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ w : ℝ in a..b,
        (Q0 * ‖amplitude' w‖ + Q1 * ‖amplitude w‖) := by
      apply intervalIntegral.integral_mono_on hab hint.norm hmajorInt
      intro w hw
      simp only [integrand, norm_mul, hEUnit w hw, mul_one]
      calc
        ‖amplitude' w * q w + amplitude w * qd w‖ ≤
            ‖amplitude' w * q w‖ + ‖amplitude w * qd w‖ := norm_add_le _ _
        _ = ‖amplitude' w‖ * ‖q w‖ + ‖amplitude w‖ * ‖qd w‖ := by
          simp only [norm_mul]
        _ ≤ Q0 * ‖amplitude' w‖ + Q1 * ‖amplitude w‖ := by
          have h0 := hQ0 w hw
          have h1 := hQ1 w hw
          nlinarith [norm_nonneg (amplitude' w), norm_nonneg (amplitude w)]
    _ = Q0 * (∫ w : ℝ in a..b, ‖amplitude' w‖) +
          Q1 * (∫ w : ℝ in a..b, ‖amplitude w‖) := by
      rw [intervalIntegral.integral_add
        (by exact (ContinuousOn.intervalIntegrable
          (by simpa [Set.uIcc_of_le hab] using continuousOn_const.mul ha'Cont.norm)))
        (by exact (ContinuousOn.intervalIntegrable
          (by simpa [Set.uIcc_of_le hab] using continuousOn_const.mul haCont.norm))),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
    _ ≤ Q0 * A1 + Q1 * A0 := by
      gcongr

end
end MAPMRTProposition51ProjectionOneIBP

#print axioms MAPMRTProposition51ProjectionOneIBP.one_integration_by_parts_identity
#print axioms MAPMRTProposition51ProjectionOneIBP.norm_integral_le_one_ibp_budgets
