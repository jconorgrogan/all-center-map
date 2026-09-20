import FordWEnvelopeScalar

noncomputable section
namespace FordWIntegral
open FordWEnvelopeScalar

/-- Exact interval integral of an affine branch. -/
theorem interval_integral_affine {a b c d : ℝ} :
    ∫ z in a..b, (c * z + d) = c * ((b ^ 2 - a ^ 2) / 2) + d * (b - a) := by
  have hid : IntervalIntegrable (id : ℝ → ℝ) MeasureTheory.volume a b :=
    continuousOn_id.intervalIntegrable
  have hc : IntervalIntegrable (fun z : ℝ => c * z) MeasureTheory.volume a b := by
    simpa using hid.const_mul c
  have hd : IntervalIntegrable (fun _ : ℝ => d) MeasureTheory.volume a b :=
    intervalIntegrable_const
  rw [intervalIntegral.integral_add hc hd, intervalIntegral.integral_const_mul,
    integral_id, intervalIntegral.integral_const]
  ring


/-- Exact integral of the literal envelope, assembled from its four branches. -/
theorem envelope_integral_exact :
    ∫ z in (0 : ℝ)..(2500 / 1623), envelope z =
      (529631531821 : ℝ) / 3978922975983 := by
  let p0 : ℝ := 0
  let p1 : ℝ := 1
  let p2 : ℝ := 10000 / 8397
  let p3 : ℝ := 2000 / 1619
  let p4 : ℝ := 2500 / 1623
  have hp01 : p0 ≤ p1 := by norm_num [p0, p1]
  have hp12 : p1 ≤ p2 := by norm_num [p1, p2]
  have hp23 : p2 ≤ p3 := by norm_num [p2, p3]
  have hp34 : p3 ≤ p4 := by norm_num [p3, p4]
  have hcont : Continuous envelope := envelope_lipschitz_one.continuous
  have hi (a b : ℝ) : IntervalIntegrable envelope MeasureTheory.volume a b :=
    hcont.continuousOn.intervalIntegrable
  have hsplit01 := intervalIntegral.integral_add_adjacent_intervals (hi p0 p1) (hi p1 p2)
  have hsplit12 := intervalIntegral.integral_add_adjacent_intervals (hi p0 p2) (hi p2 p3)
  have hsplit23 := intervalIntegral.integral_add_adjacent_intervals (hi p0 p3) (hi p3 p4)
  have h0 : ∫ z in p0..p1, envelope z = ∫ z in p0..p1, mu2 * z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : p0 ≤ z ∧ z ≤ p1 := by simpa [Set.uIcc_of_le hp01] using hz
    simpa [p0, p1] using envelope_first_branch hz'.2
  have h1 : ∫ z in p1..p2, envelope z = ∫ z in p1..p2, 1 - (1 - mu2) * z := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : p1 ≤ z ∧ z ≤ p2 := by simpa [Set.uIcc_of_le hp12] using hz
    exact envelope_second_branch hz'.1 (by simpa [p2] using hz'.2)
  have h2 : ∫ z in p2..p3, envelope z = ∫ z in p2..p3, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : p2 ≤ z ∧ z ≤ p3 := by simpa [Set.uIcc_of_le hp23] using hz
    simpa using envelope_zero_branch (by simpa [p2] using hz'.1) (by simpa [p3] using hz'.2)
  have h3 : ∫ z in p3..p4, envelope z = ∫ z in p3..p4, (1 - mu1) * z - 1 := by
    apply intervalIntegral.integral_congr
    intro z hz
    have hz' : p3 ≤ z ∧ z ≤ p4 := by simpa [Set.uIcc_of_le hp34] using hz
    exact envelope_final_branch (by simpa [p3] using hz'.1) (by simpa [p4] using hz'.2)
  change (∫ z in p0..p4, envelope z) = _
  rw [← hsplit23, ← hsplit12, ← hsplit01, h0, h1, h2, h3]
  rw [intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  have hqint : (∫ z in p1..p2, 1 - (1 - mu2) * z) =
      -(1 - mu2) * ((p2 ^ 2 - p1 ^ 2) / 2) + 1 * (p2 - p1) := by
    convert interval_integral_affine (a := p1) (b := p2)
      (c := -(1 - mu2)) (d := 1) using 1 <;> ring
  have hrint : (∫ z in p3..p4, (1 - mu1) * z - 1) =
      (1 - mu1) * ((p4 ^ 2 - p3 ^ 2) / 2) + (-1) * (p4 - p3) := by
    convert interval_integral_affine (a := p3) (b := p4)
      (c := 1 - mu1) (d := -1) using 1 <;> ring
  rw [hqint, hrint]
  simp only [smul_zero, add_zero]
  norm_num [p0, p1, p2, p3, p4, mu1, mu2]

end FordWIntegral
#print axioms FordWIntegral.envelope_integral_exact
