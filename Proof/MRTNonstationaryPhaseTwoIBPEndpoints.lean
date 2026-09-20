import MRTNonstationaryPhaseTwoIBP

/-! # Two integrations by parts with exposed artificial-cell boundaries -/

namespace MAPMRTNonstationaryPhaseTwoIBPEndpoints

open MeasureTheory Set

noncomputable section

/-- Exact two-IBP identity without imposing vanishing at the endpoints.  This
is needed when a stationary cell is excised and the two artificial cut points
carry boundary terms. -/
theorem two_integration_by_parts_identity_with_boundary
    {a b : ℝ} {E Ed q qd qdd amplitude amplitude' amplitude'' : ℝ → ℂ}
    (hab : a ≤ b)
    (hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w)
    (hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w)
    (hqd : ∀ w ∈ Set.Icc a b, HasDerivAt qd (qdd w) w)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (ha' : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude' (amplitude'' w) w)
    (hEdCont : ContinuousOn Ed (Set.Icc a b))
    (hqddCont : ContinuousOn qdd (Set.Icc a b))
    (ha''Cont : ContinuousOn amplitude'' (Set.Icc a b))
    (hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w) :
    (∫ w : ℝ in a..b, E w * amplitude w) =
      amplitude b * q b * E b - amplitude a * q a * E a -
        (amplitude' b * q b + amplitude b * qd b) * q b * E b +
        (amplitude' a * q a + amplitude a * qd a) * q a * E a +
        ∫ w : ℝ in a..b,
          (((amplitude'' w * q w + amplitude' w * qd w) +
                (amplitude' w * qd w + amplitude w * qdd w)) * q w +
            (amplitude' w * q w + amplitude w * qd w) * qd w) * E w := by
  let u : ℝ → ℂ := fun w ↦ amplitude w * q w
  let ud : ℝ → ℂ := fun w ↦ amplitude' w * q w + amplitude w * qd w
  let udd : ℝ → ℂ := fun w ↦
    (amplitude'' w * q w + amplitude' w * qd w) +
      (amplitude' w * qd w + amplitude w * qdd w)
  let v : ℝ → ℂ := fun w ↦ ud w * q w
  let vd : ℝ → ℂ := fun w ↦ udd w * q w + ud w * qd w
  have hu : ∀ w ∈ Set.Icc a b, HasDerivAt u (ud w) w := by
    intro w hw
    exact (ha w hw).mul (hq w hw)
  have hud : ∀ w ∈ Set.Icc a b, HasDerivAt ud (udd w) w := by
    intro w hw
    exact (ha' w hw).mul (hq w hw) |>.add ((ha w hw).mul (hqd w hw))
  have hv : ∀ w ∈ Set.Icc a b, HasDerivAt v (vd w) w := by
    intro w hw
    exact (hud w hw).mul (hq w hw)
  have hECont : ContinuousOn E (Set.Icc a b) :=
    fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hqCont : ContinuousOn q (Set.Icc a b) :=
    fun w hw ↦ (hq w hw).continuousAt.continuousWithinAt
  have hqdCont : ContinuousOn qd (Set.Icc a b) :=
    fun w hw ↦ (hqd w hw).continuousAt.continuousWithinAt
  have haCont : ContinuousOn amplitude (Set.Icc a b) :=
    fun w hw ↦ (ha w hw).continuousAt.continuousWithinAt
  have ha'Cont : ContinuousOn amplitude' (Set.Icc a b) :=
    fun w hw ↦ (ha' w hw).continuousAt.continuousWithinAt
  have huCont : ContinuousOn u (Set.Icc a b) := haCont.mul hqCont
  have hudCont : ContinuousOn ud (Set.Icc a b) :=
    (ha'Cont.mul hqCont).add (haCont.mul hqdCont)
  have huddCont : ContinuousOn udd (Set.Icc a b) :=
    ((ha''Cont.mul hqCont).add (ha'Cont.mul hqdCont)).add
      ((ha'Cont.mul hqdCont).add (haCont.mul hqddCont))
  have hvCont : ContinuousOn v (Set.Icc a b) := hudCont.mul hqCont
  have hvdCont : ContinuousOn vd (Set.Icc a b) :=
    (huddCont.mul hqCont).add (hudCont.mul hqdCont)
  have hiEd : IntervalIntegrable Ed volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hEdCont
  have hiud : IntervalIntegrable ud volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hudCont
  have hivd : IntervalIntegrable vd volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hvdCont
  have hibp1 : (∫ w : ℝ in a..b, u w * Ed w) =
      u b * E b - u a * E a - ∫ w : ℝ in a..b, ud w * E w := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (by simpa [Set.uIcc_of_le hab] using hu)
      (by simpa [Set.uIcc_of_le hab] using hE) hiud hiEd
  have hibp2 : (∫ w : ℝ in a..b, v w * Ed w) =
      v b * E b - v a * E a - ∫ w : ℝ in a..b, vd w * E w := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (by simpa [Set.uIcc_of_le hab] using hv)
      (by simpa [Set.uIcc_of_le hab] using hE) hivd hiEd
  have hfirstIntegrand : ∀ w ∈ Set.uIcc a b,
      E w * amplitude w = u w * Ed w := by
    intro w hw
    have hw' : w ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hw
    unfold u
    rw [mul_assoc, hinverse w hw']
    ac_rfl
  have hsecondIntegrand : ∀ w ∈ Set.uIcc a b,
      ud w * E w = v w * Ed w := by
    intro w hw
    have hw' : w ∈ Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hw
    unfold v
    rw [mul_assoc, hinverse w hw']
  rw [intervalIntegral.integral_congr hfirstIntegrand, hibp1]
  rw [intervalIntegral.integral_congr hsecondIntegrand, hibp2]
  simp only [u, ud, udd, v, vd]
  ring


end
end MAPMRTNonstationaryPhaseTwoIBPEndpoints

#print axioms MAPMRTNonstationaryPhaseTwoIBPEndpoints.two_integration_by_parts_identity_with_boundary
