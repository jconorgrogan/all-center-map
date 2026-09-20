import FordWEnvelopeScalar
import FordWIntegral

noncomputable section
namespace FordWRiemann
open FordWEnvelopeScalar FordWIntegral

/-- A Lipschitz function changes by at most the cell width on one right cell. -/
lemma right_endpoint_gap {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {a b : ℝ} (hab : a ≤ b) :
    f b - f a ≤ b - a := by
  have h := hf.dist_le_mul a b
  rw [Real.dist_eq, Real.dist_eq] at h
  have hsub : f b - f a ≤ |f b - f a| := le_abs_self _
  have habs : |b - a| = b - a := abs_of_nonneg (sub_nonneg.mpr hab)
  have habs2 : |a - b| = b - a := by
    rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  have h' : |f b - f a| ≤ b - a := by
    simpa [abs_sub_comm, habs2] using h
  linarith

/-- Exact nonnegative length of a right cell. -/
lemma right_cell_error {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {a b : ℝ} (hab : a ≤ b) :
    f b - (b - a) ≤ f a := by
  have h := right_endpoint_gap hf hab
  linarith


/-- Integrated error on one right cell. -/
theorem cell_integral_error {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    {a b : ℝ} (hab : a ≤ b) (hfi : IntervalIntegrable f MeasureTheory.volume a b) :
    f b * (b - a) - (∫ t in a..b, f t) ≤ (b - a) ^ 2 / 2 := by
  let g : ℝ → ℝ := fun t => f t + (b - t)
  have hlin : IntervalIntegrable (fun t : ℝ => b - t) MeasureTheory.volume a b := by
    exact (continuousOn_const.sub continuousOn_id).intervalIntegrable
  have hgi : IntervalIntegrable g MeasureTheory.volume a b := by
    simpa [g] using hfi.add hlin
  have hpoint : ∀ t ∈ Set.Icc a b, f b ≤ g t := by
    intro t ht
    dsimp [g]
    have hgap := right_endpoint_gap hf ht.2
    linarith
  have hconst : IntervalIntegrable (fun _ : ℝ => f b) MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hab hconst hgi hpoint
  have hadd := intervalIntegral.integral_add hfi hlin
  have hlinint : (∫ t in a..b, b - t) =
      (-1 : ℝ) * ((b ^ 2 - a ^ 2) / 2) + b * (b - a) := by
    simpa [sub_eq_add_neg, add_comm] using
      (FordWIntegral.interval_integral_affine (a := a) (b := b) (c := -1) (d := b))
  change (∫ u in a..b, f b) ≤ (∫ u in a..b, f u + (b - u)) at hmono
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add hfi hlin,
    hlinint] at hmono
  norm_num [smul_eq_mul] at hmono ⊢
  nlinarith


/-- The literal envelope is nonnegative on the nonnegative half-line. -/
theorem envelope_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ envelope z := by
  unfold envelope
  apply le_min
  · norm_num [mu2]
    positivity
  · exact le_max_left _ _


/-- Any initial interval integral is bounded by the full positive envelope integral. -/
theorem envelope_partial_integral_le {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 2500 / 1623) :
    (∫ z in 0..x, envelope z) ≤ envelopeIntegral := by
  have hcont : Continuous envelope := envelope_lipschitz_one.continuous
  have hi01 : IntervalIntegrable envelope MeasureTheory.volume 0 x :=
    hcont.continuousOn.intervalIntegrable
  have hixd : IntervalIntegrable envelope MeasureTheory.volume x (2500 / 1623) :=
    hcont.continuousOn.intervalIntegrable
  have hadd := intervalIntegral.integral_add_adjacent_intervals hi01 hixd
  have hnonneg : 0 ≤ (∫ z in x..(2500 / 1623), envelope z) :=
    intervalIntegral.integral_nonneg hx1 (fun u hu => envelope_nonneg (le_trans hx0 hu.1))
  rw [FordWIntegral.envelope_integral_exact] at hadd
  norm_num [envelopeIntegral] at ⊢
  linarith

open scoped BigOperators

/-- A finite right-endpoint Riemann bound with the exact accumulated cell error. -/
theorem right_sum_le {f : ℝ → ℝ} (hf : LipschitzWith 1 f)
    (K : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    h * (∑ i ∈ Finset.range K, f (((i + 1 : ℕ) : ℝ) * h)) ≤
      (∫ z in 0..((K : ℝ) * h), f z) + (K : ℝ) * h ^ 2 / 2 := by
  have hcell (i : ℕ) :
      f (((i + 1 : ℕ) : ℝ) * h) * h -
        (∫ z in ((i : ℝ) * h)..(((i + 1 : ℕ) : ℝ) * h), f z) ≤ h ^ 2 / 2 := by
    have hdiff : (((i + 1 : ℕ) : ℝ) * h) - (i : ℝ) * h = h := by
      push_cast
      ring
    have hab : (i : ℝ) * h ≤ ((i + 1 : ℕ) : ℝ) * h := by
      rw [← sub_nonneg, hdiff]
      exact hh
    have hi : IntervalIntegrable f MeasureTheory.volume ((i : ℝ) * h)
        (((i + 1 : ℕ) : ℝ) * h) := hf.continuous.continuousOn.intervalIntegrable
    simpa only [hdiff] using cell_integral_error hf hab hi
  have hsum := Finset.sum_le_sum (s := Finset.range K) (fun i hi => hcell i)
  have ht := intervalIntegral.sum_integral_adjacent_intervals
    (a := fun i : ℕ => (i : ℝ) * h) (n := K)
    (f := f) (μ := MeasureTheory.volume)
    (fun i hi => hf.continuous.continuousOn.intervalIntegrable)
  simp only [Nat.cast_zero, zero_mul] at ht
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ht] at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  nlinarith

def scale (K : ℕ) : ℝ := b * K + 1 / 2

def envelopeSum (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K, scale K * envelope (((i + 1 : ℕ) : ℝ) / scale K)

lemma scale_pos (K : ℕ) : 0 < scale K := by
  unfold scale b
  positivity

/-- The literal finite W-envelope sum, for every natural cutoff. -/
theorem envelope_sum_le (K : ℕ) :
    envelopeSum K ≤ (scale K) ^ 2 * envelopeIntegral + (K : ℝ) / 2 := by
  have hpos := scale_pos K
  have hx0 : 0 ≤ (K : ℝ) / scale K := by positivity
  have hx1 : (K : ℝ) / scale K ≤ 2500 / 1623 := by
    apply (div_le_iff₀ hpos).mpr
    unfold scale b
    nlinarith
  have hint := envelope_partial_integral_le hx0 hx1
  have hr := right_sum_le envelope_lipschitz_one K (h := 1 / scale K) (by positivity)
  simp only [mul_one_div] at hr
  have hbound : (1 / scale K) *
      (∑ i ∈ Finset.range K, envelope (((i + 1 : ℕ) : ℝ) / scale K)) ≤
      envelopeIntegral + (K : ℝ) * (1 / scale K) ^ 2 / 2 := by
    linarith
  unfold envelopeSum
  calc
    _ = scale K * (∑ i ∈ Finset.range K,
        envelope (((i + 1 : ℕ) : ℝ) / scale K)) := by rw [Finset.mul_sum]
    _ = (scale K) ^ 2 * ((1 / scale K) *
        (∑ i ∈ Finset.range K, envelope (((i + 1 : ℕ) : ℝ) / scale K))) := by
      field_simp
    _ ≤ (scale K) ^ 2 *
        (envelopeIntegral + (K : ℝ) * (1 / scale K) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
    _ = (scale K) ^ 2 * envelopeIntegral + (K : ℝ) / 2 := by
      field_simp

def rawSaving (K : ℕ) : ℝ :=
  mu2 * (K : ℝ) * (K + 1) / 2 - envelopeSum K - eps * (mu1 + mu2) * (K : ℝ) ^ 2

/-- Unconditional scalar saving for the literal finite envelope, not a sampled estimate. -/
theorem raw_saving_ge_target {K : ℕ} (hK : 2000 ≤ K) :
    (K : ℝ) ^ 2 / 50 ≤ rawSaving K := by
  apply saving_ge_target_of_riemann (by exact_mod_cast hK)
  have hs := envelope_sum_le K
  unfold rawSaving
  unfold scale at hs
  linarith

end FordWRiemann
#print axioms FordWRiemann.right_endpoint_gap
#print axioms FordWRiemann.cell_integral_error

#print axioms FordWRiemann.right_sum_le
#print axioms FordWRiemann.envelope_sum_le
#print axioms FordWRiemann.raw_saving_ge_target
