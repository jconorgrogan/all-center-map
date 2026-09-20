import JutilaDualTailContour
import Mathlib.Analysis.SumIntegralComparisons

/-!
# The absolute Dirichlet-series tail in Jutila's reflected remainder

This file certifies the elementary sum--integral estimate used after the
`I₂` contour is moved to `Re w=-h/2` in Jutila (1977), Lemma 1, p. 58.
The exponent is kept real: replacing it by an integer loses the conductor
power which Jutila's lower bound on `M` is designed to cancel.
-/

namespace JutilaDualTailPSeries

open Complex Real Set
open scoped BigOperators LSeries.notation
open JutilaCriticalPartialTruncation
open JutilaDualTailContour

noncomputable section

set_option maxHeartbeats 800000

/-- Integral-test estimate for the part strictly after `M`, with an arbitrary
real exponent. -/
theorem finite_real_rpow_tail_after_le
    {M K : ℕ} {a : ℝ} (hM : 1 ≤ M) (ha : 1 < a) :
    (∑ i ∈ Finset.range K,
        ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
      (M : ℝ) ^ (1 - a) / (a - 1) := by
  let f : ℝ → ℝ := fun x => x ^ (-a)
  have hMpos : (0 : ℝ) < M := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  have hanti : AntitoneOn f
      (Set.Icc (M : ℝ) ((M : ℝ) + K)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hMpos.trans_le hx.1) hxy
      (neg_nonpos.mpr (by linarith))
  have hsum := hanti.sum_le_integral
  have hane : -a ≠ -1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc (M : ℝ) ((M : ℝ) + K) := by
    rw [Set.uIcc_of_le (le_add_of_nonneg_right (Nat.cast_nonneg K))]
    intro hz
    exact (not_le_of_gt hMpos) hz.1
  rw [integral_rpow (Or.inr ⟨hane, hzero⟩)] at hsum
  have hdenPos : 0 < a - 1 := by linarith
  have hrewrite : -a + 1 = 1 - a := by ring
  calc
    (∑ i ∈ Finset.range K,
        ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
      (((M : ℝ) + K) ^ (-a + 1) -
          (M : ℝ) ^ (-a + 1)) / (-a + 1) := by
        simpa [f, Nat.cast_add] using hsum
    _ ≤ (M : ℝ) ^ (1 - a) / (a - 1) := by
      rw [hrewrite]
      have hdenNe : a - 1 ≠ 0 := hdenPos.ne'
      have hupperNonneg :
          0 ≤ ((M : ℝ) + K) ^ (-(a - 1)) :=
        Real.rpow_nonneg (by positivity) _
      have heq :
          (((M : ℝ) + K) ^ (-(a - 1)) -
              (M : ℝ) ^ (-(a - 1))) / (-(a - 1)) =
            ((M : ℝ) ^ (-(a - 1)) -
              ((M : ℝ) + K) ^ (-(a - 1))) / (a - 1) := by
        field_simp [hdenNe]
        ring
      rw [show 1 - a = -(a - 1) by ring, heq]
      exact (div_le_div_iff_of_pos_right hdenPos).2
        (sub_le_self _ hupperNonneg)

/-- Infinite `p`-series tail beginning at `M`, retaining the full real
exponent. -/
theorem tsum_real_rpow_nat_add_le
    {M : ℕ} {a : ℝ} (hM : 1 ≤ M) (ha : 1 < a) :
    (∑' i : ℕ, ((M + i : ℕ) : ℝ) ^ (-a)) ≤
      (M : ℝ) ^ (-a) + (M : ℝ) ^ (1 - a) / (a - 1) := by
  have hsbase : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs : Summable (fun i : ℕ => ((M + i : ℕ) : ℝ) ^ (-a)) := by
    rw [show (fun i : ℕ => ((M + i : ℕ) : ℝ) ^ (-a)) =
        fun i : ℕ => ((i + M : ℕ) : ℝ) ^ (-a) by
      funext i
      rw [Nat.add_comm]]
    exact (summable_nat_add_iff M).2 hsbase
  have htail : (∑' i : ℕ,
      ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
        (M : ℝ) ^ (1 - a) / (a - 1) := by
    apply Real.tsum_le_of_sum_le
    · intro i
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · intro u
      obtain ⟨K, huK⟩ := Finset.exists_nat_subset_range u
      calc
        (∑ i ∈ u, ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-a)) ≤
            ∑ i ∈ Finset.range K,
              ((M + (i + 1 : ℕ) : ℕ) : ℝ) ^ (-a) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg huK
          intro i hi hnot
          exact Real.rpow_nonneg (Nat.cast_nonneg _) _
        _ ≤ (M : ℝ) ^ (1 - a) / (a - 1) :=
          finite_real_rpow_tail_after_le hM ha
  have hsplit := hs.sum_add_tsum_nat_add 1
  rw [Finset.sum_range_one] at hsplit
  rw [← hsplit]
  simpa [Nat.add_zero, Nat.add_assoc] using
    add_le_add_left htail ((M : ℝ) ^ (-a))

/-- The L-series split at `M` is valid at every point traversed by the
remainder contour, not just on the initial reflected line. -/
theorem dualTail_eq_shifted_tsum_of_re_neg
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hz : z.re < 0) (M : ℕ) :
    dualTail chi z M =
      ∑' n : ℕ,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M) := by
  have hsum : LSeriesSummable (fun n : ℕ => chi⁻¹ n) (1 - z) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      exact chi⁻¹.norm_le_one (n : ZMod q)
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  unfold LSeriesSummable at hsum
  unfold dualTail dualPartialSum LSeries
  have hsplit := hsum.sum_add_tsum_nat_add M
  calc
    (∑' n : ℕ, LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n) -
        ∑ n ∈ Finset.range M,
          LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n =
      ((∑ n ∈ Finset.range M,
          LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n) +
        ∑' n : ℕ,
          LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M)) -
        ∑ n ∈ Finset.range M,
          LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n := by
      rw [hsplit]
    _ = ∑' n : ℕ,
          LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M) := by ring

/-- Pointwise absolute majorant for one dual coefficient. -/
theorem norm_dual_term_le_rpow
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {z : ℂ} {n : ℕ} (hn : 0 < n) :
    ‖LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n‖ ≤
      (n : ℝ) ^ (z.re - 1) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [LSeries.term_of_ne_zero hn0, norm_div,
    Complex.norm_natCast_cpow_of_pos hn]
  calc
    ‖chi⁻¹ (n : ZMod q)‖ / (n : ℝ) ^ (1 - z).re ≤
        1 / (n : ℝ) ^ (1 - z).re :=
      div_le_div_of_nonneg_right (chi⁻¹.norm_le_one (n : ZMod q))
        (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (z.re - 1) := by
      rw [one_div, ← Real.rpow_neg hnR.le]
      congr 2
      simp only [Complex.sub_re, Complex.one_re]
      ring

/-- The literal reflected dual L-series remainder has the full real-power
tail needed in Jutila's `I₂` estimate. -/
theorem norm_dualTail_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {z : ℂ} (hz : z.re < 0) {M : ℕ} (hM : 1 ≤ M) :
    ‖dualTail chi z M‖ ≤
      (M : ℝ) ^ (z.re - 1) +
        (M : ℝ) ^ z.re / (-z.re) := by
  rw [dualTail_eq_shifted_tsum_of_re_neg chi hz M]
  have hseries : LSeriesSummable (fun n : ℕ => chi⁻¹ n) (1 - z) := by
    apply LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    · intro n hn
      exact chi⁻¹.norm_le_one (n : ZMod q)
    · simp only [Complex.sub_re, Complex.one_re]
      linarith
  unfold LSeriesSummable at hseries
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) n‖) :=
    hseries.norm
  have hnormShift : Summable (fun n : ℕ =>
      ‖LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M)‖) :=
    (summable_nat_add_iff M).2 hnorm
  have hmodel : Summable (fun n : ℕ =>
      ((M + n : ℕ) : ℝ) ^ (z.re - 1)) := by
    have hsbase : Summable (fun n : ℕ => (n : ℝ) ^ (z.re - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    rw [show (fun n : ℕ => ((M + n : ℕ) : ℝ) ^ (z.re - 1)) =
        fun n : ℕ => ((n + M : ℕ) : ℝ) ^ (z.re - 1) by
      funext n
      rw [Nat.add_comm]]
    exact (summable_nat_add_iff M).2 hsbase
  have hpoint : ∀ n : ℕ,
      ‖LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M)‖ ≤
        ((M + n : ℕ) : ℝ) ^ (z.re - 1) := by
    intro n
    have hpos : 0 < n + M := by omega
    simpa [Nat.add_comm] using norm_dual_term_le_rpow chi (z := z) hpos
  calc
    ‖∑' n : ℕ,
        LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M)‖ ≤
        ∑' n : ℕ,
          ‖LSeries.term (fun m : ℕ => chi⁻¹ m) (1 - z) (n + M)‖ :=
      norm_tsum_le_tsum_norm hnormShift
    _ ≤ ∑' n : ℕ, ((M + n : ℕ) : ℝ) ^ (z.re - 1) :=
      hnormShift.tsum_le_tsum hpoint hmodel
    _ ≤ (M : ℝ) ^ (z.re - 1) +
        (M : ℝ) ^ z.re / (-z.re) := by
      have h := tsum_real_rpow_nat_add_le hM
        (a := 1 - z.re) (by linarith)
      simpa only [show -(1 - z.re) = z.re - 1 by ring,
        show 1 - (1 - z.re) = z.re by ring,
        show (1 - z.re) - 1 = -z.re by ring] using h

end

end JutilaDualTailPSeries

#print axioms JutilaDualTailPSeries.finite_real_rpow_tail_after_le
#print axioms JutilaDualTailPSeries.tsum_real_rpow_nat_add_le
#print axioms JutilaDualTailPSeries.dualTail_eq_shifted_tsum_of_re_neg
#print axioms JutilaDualTailPSeries.norm_dual_term_le_rpow
#print axioms JutilaDualTailPSeries.norm_dualTail_le
