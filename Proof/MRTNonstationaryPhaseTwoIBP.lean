import MRTVanDerCorputCore

/-!
# Two integrations by parts for a nonstationary oscillatory integral

This is the calculus engine used twice on page 50 of MRT: once for equation
(84), and once for the distinct-frequency packet correlation.  The inverse
phase derivative is represented by `q`; this keeps the theorem independent of
the particular exponential phase while exposing every derivative which must be
estimated in the source specializations.
-/

namespace MAPMRTNonstationaryPhaseTwoIBP

open MeasureTheory Set

noncomputable section

/-- Exact two-fold integration-by-parts identity.  If `E' = Ed` and
`q * Ed = E`, then the oscillatory amplitude can be divided by the phase
derivative twice.  The endpoint hypotheses are the literal compact-support
boundary conditions used for the MRT cutoffs. -/
theorem two_integration_by_parts_identity
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
    (hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w)
    (ha_left : amplitude a = 0) (ha_right : amplitude b = 0)
    (ha'_left : amplitude' a = 0) (ha'_right : amplitude' b = 0) :
    (∫ w : ℝ in a..b, E w * amplitude w) =
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
  have huEnds : u a = 0 ∧ u b = 0 := by simp [u, ha_left, ha_right]
  have hudEnds : ud a = 0 ∧ ud b = 0 := by
    simp [ud, ha_left, ha_right, ha'_left, ha'_right]
  have hvEnds : v a = 0 ∧ v b = 0 := by simp [v, hudEnds]
  rw [intervalIntegral.integral_congr hfirstIntegrand, hibp1,
    huEnds.1, huEnds.2]
  simp only [zero_mul, sub_zero, zero_sub]
  rw [intervalIntegral.integral_congr hsecondIntegrand, hibp2,
    hvEnds.1, hvEnds.2]
  simp only [zero_mul, sub_zero, zero_sub, neg_neg]
  rfl

/-- Quantitative consequence of the exact two-IBP identity.  The three
amplitude `L¹` budgets and three inverse-phase derivative sup bounds are kept
separate so the two MRT applications can retain their literal scales. -/
theorem norm_integral_le_two_ibp_budgets
    {a b A0 A1 A2 Q0 Q1 Q2 : ℝ}
    {E Ed q qd qdd amplitude amplitude' amplitude'' : ℝ → ℂ}
    (hab : a ≤ b)
    (hE : ∀ w ∈ Set.Icc a b, HasDerivAt E (Ed w) w)
    (hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w)
    (hqd : ∀ w ∈ Set.Icc a b, HasDerivAt qd (qdd w) w)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (ha' : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude' (amplitude'' w) w)
    (hEdCont : ContinuousOn Ed (Set.Icc a b))
    (hqddCont : ContinuousOn qdd (Set.Icc a b))
    (ha''Cont : ContinuousOn amplitude'' (Set.Icc a b))
    (hinverse : ∀ w ∈ Set.Icc a b, q w * Ed w = E w)
    (ha_left : amplitude a = 0) (ha_right : amplitude b = 0)
    (ha'_left : amplitude' a = 0) (ha'_right : amplitude' b = 0)
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hA2 : (∫ w : ℝ in a..b, ‖amplitude'' w‖) ≤ A2)
    (hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ Q0)
    (hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ Q1)
    (hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤ Q2)
    (hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1)
    (hQ0nonneg : 0 ≤ Q0) (hQ1nonneg : 0 ≤ Q1) (hQ2nonneg : 0 ≤ Q2) :
    ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤
      Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
        (Q0 * Q2 + Q1 ^ 2) * A0 := by
  have hid := two_integration_by_parts_identity hab hE hq hqd ha ha'
    hEdCont hqddCont ha''Cont hinverse ha_left ha_right ha'_left ha'_right
  rw [hid]
  let vd : ℝ → ℂ := fun w ↦
    (((amplitude'' w * q w + amplitude' w * qd w) +
          (amplitude' w * qd w + amplitude w * qdd w)) * q w +
      (amplitude' w * q w + amplitude w * qd w) * qd w) * E w
  have hqCont : ContinuousOn q (Set.Icc a b) :=
    fun w hw ↦ (hq w hw).continuousAt.continuousWithinAt
  have hqdCont : ContinuousOn qd (Set.Icc a b) :=
    fun w hw ↦ (hqd w hw).continuousAt.continuousWithinAt
  have haCont : ContinuousOn amplitude (Set.Icc a b) :=
    fun w hw ↦ (ha w hw).continuousAt.continuousWithinAt
  have ha'Cont : ContinuousOn amplitude' (Set.Icc a b) :=
    fun w hw ↦ (ha' w hw).continuousAt.continuousWithinAt
  have hECont : ContinuousOn E (Set.Icc a b) :=
    fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hvdCont : ContinuousOn vd (Set.Icc a b) := by
    unfold vd
    fun_prop
  have hivd : IntervalIntegrable vd volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hvdCont
  have hmajorCont : ContinuousOn
      (fun w ↦ Q0 ^ 2 * ‖amplitude'' w‖ +
        3 * Q0 * Q1 * ‖amplitude' w‖ +
          (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖) (Set.Icc a b) := by
    fun_prop
  have himajor : IntervalIntegrable
      (fun w ↦ Q0 ^ 2 * ‖amplitude'' w‖ +
        3 * Q0 * Q1 * ‖amplitude' w‖ +
          (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using hmajorCont
  have hpoint : ∀ w ∈ Set.Icc a b,
      ‖vd w‖ ≤ Q0 ^ 2 * ‖amplitude'' w‖ +
        3 * Q0 * Q1 * ‖amplitude' w‖ +
          (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖ := by
    intro w hw
    have h0 := hQ0 w hw
    have h1 := hQ1 w hw
    have h2 := hQ2 w hw
    have ha2q : ‖amplitude'' w * q w‖ ≤ ‖amplitude'' w‖ * Q0 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
    have ha1qd : ‖amplitude' w * qd w‖ ≤ ‖amplitude' w‖ * Q1 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have ha0qdd : ‖amplitude w * qdd w‖ ≤ ‖amplitude w‖ * Q2 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    have ha1q : ‖amplitude' w * q w‖ ≤ ‖amplitude' w‖ * Q0 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h0 (norm_nonneg _)
    have ha0qd : ‖amplitude w * qd w‖ ≤ ‖amplitude w‖ * Q1 := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    have hblock1 :
        ‖(amplitude'' w * q w + amplitude' w * qd w) +
            (amplitude' w * qd w + amplitude w * qdd w)‖ ≤
          (‖amplitude'' w‖ * Q0 + ‖amplitude' w‖ * Q1) +
            (‖amplitude' w‖ * Q1 + ‖amplitude w‖ * Q2) := by
      exact (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add ha2q ha1qd))
        ((norm_add_le _ _).trans (add_le_add ha1qd ha0qdd)))
    have hblock2 :
        ‖amplitude' w * q w + amplitude w * qd w‖ ≤
          ‖amplitude' w‖ * Q0 + ‖amplitude w‖ * Q1 := by
      exact (norm_add_le _ _).trans (add_le_add ha1q ha0qd)
    have hraw :
        ‖vd w‖ ≤
          ((‖amplitude'' w‖ * Q0 + ‖amplitude' w‖ * Q1) +
            (‖amplitude' w‖ * Q1 + ‖amplitude w‖ * Q2)) * Q0 +
          (‖amplitude' w‖ * Q0 + ‖amplitude w‖ * Q1) * Q1 := by
      unfold vd
      rw [norm_mul, hEUnit w hw, mul_one]
      calc
        ‖(((amplitude'' w * q w + amplitude' w * qd w) +
              (amplitude' w * qd w + amplitude w * qdd w)) * q w +
            (amplitude' w * q w + amplitude w * qd w) * qd w)‖ ≤
            ‖((amplitude'' w * q w + amplitude' w * qd w) +
              (amplitude' w * qd w + amplitude w * qdd w)) * q w‖ +
              ‖(amplitude' w * q w + amplitude w * qd w) * qd w‖ :=
          norm_add_le _ _
        _ = ‖(amplitude'' w * q w + amplitude' w * qd w +
                (amplitude' w * qd w + amplitude w * qdd w))‖ * ‖q w‖ +
              ‖amplitude' w * q w + amplitude w * qd w‖ * ‖qd w‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ ((‖amplitude'' w‖ * Q0 + ‖amplitude' w‖ * Q1) +
              (‖amplitude' w‖ * Q1 + ‖amplitude w‖ * Q2)) * Q0 +
            (‖amplitude' w‖ * Q0 + ‖amplitude w‖ * Q1) * Q1 := by
          apply add_le_add
          · exact mul_le_mul hblock1 h0 (norm_nonneg _)
              (by positivity)
          · exact mul_le_mul hblock2 h1 (norm_nonneg _)
              (by positivity)
    calc
      ‖vd w‖ ≤ _ := hraw
      _ = Q0 ^ 2 * ‖amplitude'' w‖ +
          3 * Q0 * Q1 * ‖amplitude' w‖ +
            (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖ := by ring
  have hnorm : ‖∫ w : ℝ in a..b, vd w‖ ≤
      ∫ w : ℝ in a..b,
        (Q0 ^ 2 * ‖amplitude'' w‖ +
          3 * Q0 * Q1 * ‖amplitude' w‖ +
            (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖) := by
    calc
      ‖∫ w : ℝ in a..b, vd w‖ ≤ ∫ w : ℝ in a..b, ‖vd w‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ _ := intervalIntegral.integral_mono_on hab hivd.norm himajor hpoint
  have hA0nonneg : 0 ≤ A0 :=
    le_trans (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _)) hA0
  have hA1nonneg : 0 ≤ A1 :=
    le_trans (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _)) hA1
  have hA2nonneg : 0 ≤ A2 :=
    le_trans (intervalIntegral.integral_nonneg hab (fun _ _ ↦ norm_nonneg _)) hA2
  have hiA0 : IntervalIntegrable (fun w ↦ ‖amplitude w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using haCont.norm
  have hiA1 : IntervalIntegrable (fun w ↦ ‖amplitude' w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using ha'Cont.norm
  have hiA2 : IntervalIntegrable (fun w ↦ ‖amplitude'' w‖) volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa [Set.uIcc_of_le hab] using ha''Cont.norm
  calc
    ‖∫ w : ℝ in a..b, vd w‖ ≤ _ := hnorm
    _ = Q0 ^ 2 * (∫ w : ℝ in a..b, ‖amplitude'' w‖) +
        3 * Q0 * Q1 * (∫ w : ℝ in a..b, ‖amplitude' w‖) +
          (Q0 * Q2 + Q1 ^ 2) * (∫ w : ℝ in a..b, ‖amplitude w‖) := by
      rw [show (fun w ↦ Q0 ^ 2 * ‖amplitude'' w‖ +
          3 * Q0 * Q1 * ‖amplitude' w‖ +
            (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖) =
          (fun w ↦ Q0 ^ 2 * ‖amplitude'' w‖ +
            (3 * Q0 * Q1 * ‖amplitude' w‖ +
              (Q0 * Q2 + Q1 ^ 2) * ‖amplitude w‖)) by
            funext w; ring,
        intervalIntegral.integral_add (hiA2.const_mul _)
          ((hiA1.const_mul _).add (hiA0.const_mul _)),
        intervalIntegral.integral_add (hiA1.const_mul _) (hiA0.const_mul _),
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring
    _ ≤ Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
        (Q0 * Q2 + Q1 ^ 2) * A0 := by
      gcongr <;> positivity

end
end MAPMRTNonstationaryPhaseTwoIBP
