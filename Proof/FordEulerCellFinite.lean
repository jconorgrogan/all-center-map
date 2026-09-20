import Mathlib

open scoped BigOperators
noncomputable section
namespace FordEulerCellFinite

/-- Exact telescoping of Euler cells, before any infinite limit is taken. -/
theorem sum_cells (a : ℝ) (s : ℂ) (K : ℕ) :
    (∑ n ∈ Finset.range K,
      (((a + n : ℝ) : ℂ) ^ (-s) -
        (((a + n + 1 : ℝ) : ℂ) ^ (1 - s) -
          ((a + n : ℝ) : ℂ) ^ (1 - s)) / (1 - s))) =
    (∑ n ∈ Finset.range K, ((a + n : ℝ) : ℂ) ^ (-s)) -
      (((a + K : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring

end FordEulerCellFinite
#print axioms FordEulerCellFinite.sum_cells
