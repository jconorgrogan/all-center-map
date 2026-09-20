import FordScaledCanonicalCorrection

open scoped BigOperators
noncomputable section
namespace FordFinitePoleReal

theorem pole_re_nonneg (m : ℕ) {s ρ : ℂ} (h : ρ.re ≤ s.re) :
    0 ≤ ((m : ℂ) / (s - ρ)).re := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.sub_re, Complex.natCast_im, zero_mul,
    zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr h))
    (Complex.normSq_nonneg _)

theorem pole_re_eq (m : ℕ) {s ρ : ℂ} (him : s.im = ρ.im)
    (hre : ρ.re < s.re) :
    ((m : ℂ) / (s - ρ)).re = (m : ℝ) / (s.re - ρ.re) := by
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.sub_re, Complex.natCast_im, zero_mul,
    zero_div, add_zero]
  have hn : Complex.normSq (s - ρ) = (s.re - ρ.re) ^ 2 := by
    rw [Complex.normSq_apply]
    simp [him, pow_two]
  rw [hn]
  have hne : s.re - ρ.re ≠ 0 := sub_ne_zero.mpr (ne_of_gt hre)
  field_simp

theorem selected_pole_le (S : Finset ℂ) (m : ℂ → ℕ) {s ρ : ℂ}
    (hS : ∀ z ∈ S, z.re ≤ s.re) (hρ : ρ ∈ S)
    (hm : 1 ≤ m ρ) (him : s.im = ρ.im) (hre : ρ.re < s.re) :
    1 / (s.re - ρ.re) ≤ (∑ z ∈ S, (m z : ℂ) / (s - z)).re := by
  rw [Complex.re_sum]
  have hsingle := Finset.single_le_sum
    (fun z hz => pole_re_nonneg (m z) (hS z hz)) hρ
  rw [pole_re_eq (m ρ) him hre] at hsingle
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hm)
    (sub_nonneg.mpr hre.le)).trans hsingle

/-- Exact finite pole isolation, with the analytic remainder kept explicit. -/
theorem neg_re_le_sub_selected (S : Finset ℂ) (m : ℂ → ℕ) {s ρ v r : ℂ}
    {E : ℝ} (hS : ∀ z ∈ S, z.re ≤ s.re) (hρ : ρ ∈ S)
    (hm : 1 ≤ m ρ) (him : s.im = ρ.im) (hre : ρ.re < s.re)
    (hid : v = r + ∑ z ∈ S, (m z : ℂ) / (s - z)) (hr : ‖r‖ ≤ E) :
    (-v).re ≤ E - 1 / (s.re - ρ.re) := by
  have hp := selected_pole_le S m hS hρ hm him hre
  have hr' : -r.re ≤ E := by
    have hh := Complex.re_le_norm (-r)
    simpa using hh.trans (by simpa using hr)
  rw [hid, Complex.neg_re, Complex.add_re]
  linarith

theorem neg_re_le (S : Finset ℂ) (m : ℂ → ℕ) {s v r : ℂ}
    {E : ℝ} (hS : ∀ z ∈ S, z.re ≤ s.re)
    (hid : v = r + ∑ z ∈ S, (m z : ℂ) / (s - z)) (hr : ‖r‖ ≤ E) :
    (-v).re ≤ E := by
  have hp : 0 ≤ (∑ z ∈ S, (m z : ℂ) / (s - z)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_nonneg (fun z hz => pole_re_nonneg (m z) (hS z hz))
  have hr' : -r.re ≤ E := by
    have hh := Complex.re_le_norm (-r)
    simpa using hh.trans (by simpa using hr)
  rw [hid, Complex.neg_re, Complex.add_re]
  linarith

end FordFinitePoleReal
#print axioms FordFinitePoleReal.selected_pole_le
#print axioms FordFinitePoleReal.neg_re_le_sub_selected
#print axioms FordFinitePoleReal.neg_re_le
