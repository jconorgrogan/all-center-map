import NearOneThreeLines
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Explicit bound for the right-edge p-series

This is the narrow integral-test estimate needed when the absolutely
convergent boundary is placed at `Re s = 1+r` with `r = 1 / log x₀`.
-/

namespace MAPRightEdgePSeriesExplicitBound

open Set LSeries
open MAPZeroFreeSiegelSpine

noncomputable section

private theorem rightEdgeTerm_eq_rpow {r : ℝ} (n : ℕ) :
    ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) (((1 + r : ℝ) : ℂ)) n‖ =
      if n = 0 then 0 else (n : ℝ) ^ (-(1 + r)) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · rfl
  · rw [show ((((1 + r : ℝ) : ℂ)).re) = 1 + r by simp]
    simp only [norm_one, one_div]
    rw [← Real.rpow_neg (Nat.cast_nonneg n)]

private theorem finite_rightEdge_sum_le {r : ℝ} (hr : 0 < r) (s : Finset ℕ) :
    ∑ n ∈ s,
        ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) (((1 + r : ℝ) : ℂ)) n‖ ≤
      1 + 1 / r := by
  let g : ℕ → ℝ := fun n =>
    ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) (((1 + r : ℝ) : ℂ)) n‖
  obtain ⟨N, hsN⟩ := Finset.exists_nat_subset_range s
  have hsLarge : s ⊆ Finset.range (2 + N) := by
    exact hsN.trans (Finset.range_mono (by omega))
  have hsumSubset : ∑ n ∈ s, g n ≤ ∑ n ∈ Finset.range (2 + N), g n := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsLarge
      (fun i _ _ => norm_nonneg _)
  let f : ℝ → ℝ := fun x => x ^ (-(1 + r))
  have ha : -(1 + r) ≤ 0 := by linarith
  have hfanti : AntitoneOn f (Set.Icc (1 : ℝ) (1 + N)) := by
    exact (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos ha).mono
      (by intro x hx; exact lt_of_lt_of_le zero_lt_one hx.1)
  have htail := hfanti.sum_le_integral (a := N)
  have hterm (i : ℕ) : g (2 + i) = f (1 + (i + 1 : ℕ)) := by
    rw [show 2 + i = 1 + (i + 1) by omega]
    rw [show g (1 + (i + 1)) =
        (if 1 + (i + 1) = 0 then 0 else
          ((1 + (i + 1) : ℕ) : ℝ) ^ (-(1 + r))) by
      exact rightEdgeTerm_eq_rpow (r := r) (1 + (i + 1))]
    rw [if_neg (by omega)]
    dsimp only [f]
    congr 1
    norm_num
  have hhead : ∑ n ∈ Finset.range 2, g n = 1 := by
    norm_num [g, LSeries.norm_term_eq, Finset.sum_range_succ, Real.one_rpow]
  have hfull : ∑ n ∈ Finset.range (2 + N), g n =
      1 + ∑ i ∈ Finset.range N, f (1 + (i + 1 : ℕ)) := by
    rw [Finset.sum_range_add, hhead]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    exact hterm i
  have hint : (∫ x in (1 : ℝ)..1 + N, f x) ≤ 1 / r := by
    rw [show (∫ x in (1 : ℝ)..1 + N, f x) =
        (((1 + N : ℝ) ^ (-r) - (1 : ℝ) ^ (-r)) / (-r)) by
      dsimp [f]
      rw [integral_rpow]
      · congr 3 <;> ring
      · right
        constructor
        · linarith
        · simp]
    rw [Real.one_rpow]
    have hb0 : 0 ≤ (1 + (N : ℝ)) ^ (-r) := Real.rpow_nonneg (by positivity) _
    have hr0 : 0 ≤ r := hr.le
    have hneg : -r < 0 := neg_neg_of_pos hr
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hinvneg : (-r)⁻¹ = -(r⁻¹) := by rw [inv_neg]
    rw [hinvneg]
    nlinarith [inv_nonneg.mpr hr0]
  have hlarge : ∑ n ∈ Finset.range (2 + N), g n ≤ 1 + 1 / r := by
    rw [hfull]
    simpa only [add_comm] using add_le_add_left (htail.trans hint) 1
  exact hsumSubset.trans hlarge

/-- Explicit integral-test bound on the conductor-free right boundary. -/
theorem rightEdgePSeries_le_one_add_inv {r : ℝ} (hr : 0 < r) :
    rightEdgePSeries r ≤ 1 + 1 / r := by
  unfold rightEdgePSeries
  have hs : Summable (fun n : ℕ =>
      ‖LSeries.term (fun _n : ℕ => (1 : ℂ)) (((1 + r : ℝ) : ℂ)) n‖) := by
    exact (LSeriesSummable_of_bounded_of_one_lt_re
      (f := fun _n : ℕ => (1 : ℂ)) (m := 1)
      (fun _n _hn => by simp) (by simp; linarith)).norm
  exact hs.tsum_le_of_sum_le (finite_rightEdge_sum_le hr)

end
end MAPRightEdgePSeriesExplicitBound

#print axioms MAPRightEdgePSeriesExplicitBound.rightEdgePSeries_le_one_add_inv
