import MRTNonstationaryPhaseTwoIBPEndpoints

/-! # Quantitative two-IBP bound with exposed cell endpoints -/

namespace MAPMRTNonstationaryPhaseTwoIBPEndpointBound

open MeasureTheory Set
open MAPMRTNonstationaryPhaseTwoIBPEndpoints

noncomputable section

/-- The interior remainder in the boundary-aware two-IBP identity obeys the
same three amplitude budgets as the zero-boundary version. -/
theorem norm_two_ibp_remainder_le_budgets
    {a b A0 A1 A2 Q0 Q1 Q2 : ℝ}
    {E q qd qdd amplitude amplitude' amplitude'' : ℝ → ℂ}
    (hab : a ≤ b)
    (hECont : ContinuousOn E (Set.Icc a b))
    (hq : ∀ w ∈ Set.Icc a b, HasDerivAt q (qd w) w)
    (hqd : ∀ w ∈ Set.Icc a b, HasDerivAt qd (qdd w) w)
    (ha : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude (amplitude' w) w)
    (ha' : ∀ w ∈ Set.Icc a b, HasDerivAt amplitude' (amplitude'' w) w)
    (hqddCont : ContinuousOn qdd (Set.Icc a b))
    (ha''Cont : ContinuousOn amplitude'' (Set.Icc a b))
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hA2 : (∫ w : ℝ in a..b, ‖amplitude'' w‖) ≤ A2)
    (hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ Q0)
    (hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ Q1)
    (hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤ Q2)
    (hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1)
    (hQ0nonneg : 0 ≤ Q0) (hQ1nonneg : 0 ≤ Q1) (hQ2nonneg : 0 ≤ Q2) :
    ‖∫ w : ℝ in a..b,
      (((amplitude'' w * q w + amplitude' w * qd w) +
            (amplitude' w * qd w + amplitude w * qdd w)) * q w +
        (amplitude' w * q w + amplitude w * qd w) * qd w) * E w‖ ≤
      Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
        (Q0 * Q2 + Q1 ^ 2) * A0 := by
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

/-- Quantitative two-IBP estimate retaining both artificial-cell boundary
values of the amplitude and its derivative. -/
theorem norm_integral_le_two_ibp_endpoint_budgets
    {a b A0 A1 A2 Q0 Q1 Q2 L0 R0 L1 R1 : ℝ}
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
    (hA0 : (∫ w : ℝ in a..b, ‖amplitude w‖) ≤ A0)
    (hA1 : (∫ w : ℝ in a..b, ‖amplitude' w‖) ≤ A1)
    (hA2 : (∫ w : ℝ in a..b, ‖amplitude'' w‖) ≤ A2)
    (hQ0 : ∀ w ∈ Set.Icc a b, ‖q w‖ ≤ Q0)
    (hQ1 : ∀ w ∈ Set.Icc a b, ‖qd w‖ ≤ Q1)
    (hQ2 : ∀ w ∈ Set.Icc a b, ‖qdd w‖ ≤ Q2)
    (hEUnit : ∀ w ∈ Set.Icc a b, ‖E w‖ = 1)
    (hL0 : ‖amplitude a‖ ≤ L0) (hR0 : ‖amplitude b‖ ≤ R0)
    (hL1 : ‖amplitude' a‖ ≤ L1) (hR1 : ‖amplitude' b‖ ≤ R1)
    (hQ0nonneg : 0 ≤ Q0) (hQ1nonneg : 0 ≤ Q1) (hQ2nonneg : 0 ≤ Q2) :
    ‖∫ w : ℝ in a..b, E w * amplitude w‖ ≤
      (L0 + R0) * Q0 +
        ((L1 + R1) * Q0 + (L0 + R0) * Q1) * Q0 +
        (Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
          (Q0 * Q2 + Q1 ^ 2) * A0) := by
  let rem : ℝ → ℂ := fun w ↦
    (((amplitude'' w * q w + amplitude' w * qd w) +
          (amplitude' w * qd w + amplitude w * qdd w)) * q w +
      (amplitude' w * q w + amplitude w * qd w) * qd w) * E w
  have hECont : ContinuousOn E (Set.Icc a b) :=
    fun w hw ↦ (hE w hw).continuousAt.continuousWithinAt
  have hinter : ‖∫ w : ℝ in a..b, rem w‖ ≤
      Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
        (Q0 * Q2 + Q1 ^ 2) * A0 := by
    exact norm_two_ibp_remainder_le_budgets hab hECont hq hqd ha ha'
      hqddCont ha''Cont hA0 hA1 hA2 hQ0 hQ1 hQ2 hEUnit
      hQ0nonneg hQ1nonneg hQ2nonneg
  have hamem : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbmem : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hL0nonneg : 0 ≤ L0 := (norm_nonneg (amplitude a)).trans hL0
  have hR0nonneg : 0 ≤ R0 := (norm_nonneg (amplitude b)).trans hR0
  have hL1nonneg : 0 ≤ L1 := (norm_nonneg (amplitude' a)).trans hL1
  have hR1nonneg : 0 ≤ R1 := (norm_nonneg (amplitude' b)).trans hR1
  have huA : ‖amplitude a * q a * E a‖ ≤ L0 * Q0 := by
    rw [norm_mul, norm_mul, hEUnit a hamem, mul_one]
    exact mul_le_mul hL0 (hQ0 a hamem) (norm_nonneg _) hL0nonneg
  have huB : ‖amplitude b * q b * E b‖ ≤ R0 * Q0 := by
    rw [norm_mul, norm_mul, hEUnit b hbmem, mul_one]
    exact mul_le_mul hR0 (hQ0 b hbmem) (norm_nonneg _) hR0nonneg
  have hvA :
      ‖(amplitude' a * q a + amplitude a * qd a) * q a * E a‖ ≤
        (L1 * Q0 + L0 * Q1) * Q0 := by
    rw [norm_mul, norm_mul, hEUnit a hamem, mul_one]
    have hsum : ‖amplitude' a * q a + amplitude a * qd a‖ ≤
        L1 * Q0 + L0 * Q1 := by
      calc
        _ ≤ ‖amplitude' a * q a‖ + ‖amplitude a * qd a‖ := norm_add_le _ _
        _ = ‖amplitude' a‖ * ‖q a‖ + ‖amplitude a‖ * ‖qd a‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ L1 * Q0 + L0 * Q1 := by
          apply add_le_add
          · exact mul_le_mul hL1 (hQ0 a hamem) (norm_nonneg _) hL1nonneg
          · exact mul_le_mul hL0 (hQ1 a hamem) (norm_nonneg _) hL0nonneg
    exact mul_le_mul hsum (hQ0 a hamem) (norm_nonneg _)
      (add_nonneg (mul_nonneg hL1nonneg hQ0nonneg)
        (mul_nonneg hL0nonneg hQ1nonneg))
  have hvB :
      ‖(amplitude' b * q b + amplitude b * qd b) * q b * E b‖ ≤
        (R1 * Q0 + R0 * Q1) * Q0 := by
    rw [norm_mul, norm_mul, hEUnit b hbmem, mul_one]
    have hsum : ‖amplitude' b * q b + amplitude b * qd b‖ ≤
        R1 * Q0 + R0 * Q1 := by
      calc
        _ ≤ ‖amplitude' b * q b‖ + ‖amplitude b * qd b‖ := norm_add_le _ _
        _ = ‖amplitude' b‖ * ‖q b‖ + ‖amplitude b‖ * ‖qd b‖ := by
          rw [norm_mul, norm_mul]
        _ ≤ R1 * Q0 + R0 * Q1 := by
          apply add_le_add
          · exact mul_le_mul hR1 (hQ0 b hbmem) (norm_nonneg _) hR1nonneg
          · exact mul_le_mul hR0 (hQ1 b hbmem) (norm_nonneg _) hR0nonneg
    exact mul_le_mul hsum (hQ0 b hbmem) (norm_nonneg _)
      (add_nonneg (mul_nonneg hR1nonneg hQ0nonneg)
        (mul_nonneg hR0nonneg hQ1nonneg))
  have hid := two_integration_by_parts_identity_with_boundary hab hE hq hqd
    ha ha' hEdCont hqddCont ha''Cont hinverse
  rw [hid]
  change ‖(amplitude b * q b * E b - amplitude a * q a * E a -
      (amplitude' b * q b + amplitude b * qd b) * q b * E b +
      (amplitude' a * q a + amplitude a * qd a) * q a * E a) +
      ∫ w : ℝ in a..b, rem w‖ ≤ _
  calc
    _ ≤ ‖amplitude b * q b * E b - amplitude a * q a * E a -
          (amplitude' b * q b + amplitude b * qd b) * q b * E b +
          (amplitude' a * q a + amplitude a * qd a) * q a * E a‖ +
        ‖∫ w : ℝ in a..b, rem w‖ := norm_add_le _ _
    _ ≤ (R0 * Q0 + L0 * Q0 +
          (R1 * Q0 + R0 * Q1) * Q0 +
          (L1 * Q0 + L0 * Q1) * Q0) +
        (Q0 ^ 2 * A2 + 3 * Q0 * Q1 * A1 +
          (Q0 * Q2 + Q1 ^ 2) * A0) := by
      apply add_le_add _ hinter
      calc
        _ ≤ ‖amplitude b * q b * E b - amplitude a * q a * E a -
              (amplitude' b * q b + amplitude b * qd b) * q b * E b‖ +
            ‖(amplitude' a * q a + amplitude a * qd a) * q a * E a‖ :=
          norm_add_le _ _
        _ ≤ (‖amplitude b * q b * E b - amplitude a * q a * E a‖ +
              ‖(amplitude' b * q b + amplitude b * qd b) * q b * E b‖) +
            ‖(amplitude' a * q a + amplitude a * qd a) * q a * E a‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ ((‖amplitude b * q b * E b‖ + ‖amplitude a * q a * E a‖) +
              ‖(amplitude' b * q b + amplitude b * qd b) * q b * E b‖) +
            ‖(amplitude' a * q a + amplitude a * qd a) * q a * E a‖ := by
          gcongr
          exact norm_sub_le _ _
        _ ≤ _ := by gcongr
    _ = _ := by ring

end
end MAPMRTNonstationaryPhaseTwoIBPEndpointBound

#print axioms MAPMRTNonstationaryPhaseTwoIBPEndpointBound.norm_two_ibp_remainder_le_budgets
#print axioms MAPMRTNonstationaryPhaseTwoIBPEndpointBound.norm_integral_le_two_ibp_endpoint_budgets
