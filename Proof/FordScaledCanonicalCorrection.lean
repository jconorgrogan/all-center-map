import WideDiskLocalLogDerivative

open scoped BigOperators
noncomputable section

namespace FordScaledCanonicalCorrection

open Complex ComplexConjugate Set Metric Filter Topology
open WideDiskLocalLogDerivative

/-! A radius `3a` canonical numerator has logarithmic derivative bounded by
`1/(2a)` on the concentric radius-`a` disk.  The proof keeps the strict
product and denominator gaps explicit, so no fixed-radius normalization is
hidden in the scaling. -/

theorem shiftedCanonicalNumerator_ne_zero
    {a : ℝ} (ha : 0 < a) {c ρ s : ℂ}
    (hρ : ρ ∈ Metric.ball c (3 * a))
    (hs : s ∈ Metric.ball c a) :
    shiftedCanonicalNumerator c ρ (3 * a) s ≠ 0 := by
  have hρn : ‖ρ - c‖ < 3 * a := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hsn : ‖s - c‖ < a := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hprod : ‖conj (ρ - c) * (s - c)‖ < 3 * a ^ 2 := by
    rw [norm_mul, norm_conj]
    have hρ0 : 0 ≤ ‖ρ - c‖ := norm_nonneg _
    have hs0 : 0 ≤ ‖s - c‖ := norm_nonneg _
    have ha0 : 0 ≤ a := ha.le
    nlinarith
  have hdenLower : 6 * a ^ 2 <
      ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ := by
    have hrev := norm_sub_norm_le
      (((3 * a : ℝ) : ℂ) ^ 2) (conj (ρ - c) * (s - c))
    have hnorm : ‖(((3 * a : ℝ) : ℂ) ^ 2)‖ = 9 * a ^ 2 := by
      rw [show (((3 * a : ℝ) : ℂ) ^ 2) = (((3 * a) ^ 2 : ℝ) : ℂ) by
        push_cast
        rfl]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      ring
    rw [hnorm] at hrev
    have hrev' :
        9 * a ^ 2 - ‖conj (ρ - c) * (s - c)‖ ≤
          ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ := by
      norm_num [shiftedCanonicalNumerator, pow_two] at hrev ⊢
      exact hrev
    nlinarith
  have hnormpos : 0 < ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ :=
    lt_trans (by positivity : (0 : ℝ) < 6 * a ^ 2) hdenLower
  exact norm_pos_iff.mp hnormpos

theorem norm_logDeriv_shiftedCanonicalNumerator_le
    {a : ℝ} (ha : 0 < a) {c ρ s : ℂ}
    (hρ : ρ ∈ Metric.ball c (3 * a))
    (hs : s ∈ Metric.ball c a) :
    ‖logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s‖ ≤ 1 / (2 * a) := by
  have hρn : ‖ρ - c‖ < 3 * a := by
    simpa [Metric.mem_ball, dist_eq_norm] using hρ
  have hsn : ‖s - c‖ < a := by
    simpa [Metric.mem_ball, dist_eq_norm] using hs
  have hprod : ‖conj (ρ - c) * (s - c)‖ < 3 * a ^ 2 := by
    rw [norm_mul, norm_conj]
    have hρ0 : 0 ≤ ‖ρ - c‖ := norm_nonneg _
    have hs0 : 0 ≤ ‖s - c‖ := norm_nonneg _
    have ha0 : 0 ≤ a := ha.le
    nlinarith
  have hdenLower : 6 * a ^ 2 <
      ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ := by
    have hrev := norm_sub_norm_le
      (((3 * a : ℝ) : ℂ) ^ 2) (conj (ρ - c) * (s - c))
    have hnorm : ‖(((3 * a : ℝ) : ℂ) ^ 2)‖ = 9 * a ^ 2 := by
      rw [show (((3 * a : ℝ) : ℂ) ^ 2) = (((3 * a) ^ 2 : ℝ) : ℂ) by
        push_cast
        rfl]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      ring
    rw [hnorm] at hrev
    have hrev' :
        9 * a ^ 2 - ‖conj (ρ - c) * (s - c)‖ ≤
          ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ := by
      norm_num [shiftedCanonicalNumerator, pow_two] at hrev ⊢
      exact hrev
    nlinarith
  have hderiv : deriv (shiftedCanonicalNumerator c ρ (3 * a)) s =
      -conj (ρ - c) := by
    have hlin : HasDerivAt (fun z : ℂ => z - c) 1 s :=
      (hasDerivAt_id s).sub_const c
    have hmul : HasDerivAt
        (fun z : ℂ => conj (ρ - c) * (z - c)) (conj (ρ - c)) s := by
      convert (hasDerivAt_const s (conj (ρ - c))).mul hlin using 1 <;> simp
    have hconst : HasDerivAt (fun _z : ℂ => ((3 * a : ℝ) : ℂ) ^ 2) 0 s :=
      hasDerivAt_const s _
    change deriv
      (fun z : ℂ => ((3 * a : ℝ) : ℂ) ^ 2 -
        conj (ρ - c) * (z - c)) s = _
    simpa only [Pi.sub_apply, zero_sub] using (hconst.sub hmul).deriv
  rw [logDeriv_apply, hderiv, norm_div, norm_neg, norm_conj]
  have hratio : (3 * a) / (6 * a ^ 2) = 1 / (2 * a) := by
    field_simp
    ring
  have hquot : ‖ρ - c‖ / ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ ≤
      (3 * a) / (6 * a ^ 2) := by
    calc
      ‖ρ - c‖ / ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ ≤
          (3 * a) / ‖shiftedCanonicalNumerator c ρ (3 * a) s‖ :=
        div_le_div_of_nonneg_right hρn.le (by positivity)
      _ ≤ (3 * a) / (6 * a ^ 2) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact hdenLower.le
  exact hquot.trans_eq hratio

theorem norm_finiteWeightedCorrection_le
    {a : ℝ} (ha : 0 < a) {c : ℂ} (S : Finset ℂ) (m : ℂ → ℕ)
    {s : ℂ} (hs : s ∈ Metric.ball c a)
    (hS : ∀ ρ ∈ S, ρ ∈ Metric.ball c (3 * a)) :
    ‖∑ ρ ∈ S, (m ρ : ℂ) *
        logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s‖ ≤
      (∑ ρ ∈ S, (m ρ : ℝ)) / (2 * a) := by
  calc
    ‖∑ ρ ∈ S, (m ρ : ℂ) *
        logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s‖ ≤
        ∑ ρ ∈ S, ‖(m ρ : ℂ) *
          logDeriv (shiftedCanonicalNumerator c ρ (3 * a)) s‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ S, (m ρ : ℝ) / (2 * a) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_mul, Complex.norm_natCast]
      have hlocal := norm_logDeriv_shiftedCanonicalNumerator_le ha
        (hS ρ hρ) hs
      exact (mul_le_mul_of_nonneg_left hlocal (Nat.cast_nonneg _)).trans_eq
        (by ring)
    _ = (∑ ρ ∈ S, (m ρ : ℝ)) / (2 * a) := by
      rw [Finset.sum_div]

end FordScaledCanonicalCorrection

#print axioms FordScaledCanonicalCorrection.shiftedCanonicalNumerator_ne_zero
#print axioms FordScaledCanonicalCorrection.norm_logDeriv_shiftedCanonicalNumerator_le
#print axioms FordScaledCanonicalCorrection.norm_finiteWeightedCorrection_le
