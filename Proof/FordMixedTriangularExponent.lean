import FordP18FixedTargetInjection
import Mathlib.Algebra.BigOperators.Intervals

open scoped BigOperators
namespace MAPFordMixedTriangularExponent

theorem sum_truncated_descending (q n : ℕ) (hqn : q ≤ n) :
    (Finset.range n).sum (fun i => q - 1 - i) = q * (q - 1) / 2 := by
  have htruncate : (Finset.range q).sum (fun i => q - 1 - i) =
      (Finset.range n).sum (fun i => q - 1 - i) := by
    apply Finset.sum_subset (Finset.range_mono hqn)
    intro i hi hiq
    have : q ≤ i := by simpa only [Finset.mem_range, not_lt] using hiq
    omega
  rw [← htruncate]
  exact (Finset.sum_range_reflect (fun i : ℕ => i) q).trans (Finset.sum_range_id q)

theorem mixed_exponent_eq_triangular {d r n : ℕ} (hr : r ≤ d + n) :
    Finset.univ.sum (fun (i : Fin n) => r - min (d + i.val + 1) r) =
      (r-d) * (r-d-1) / 2 := by
  have hterm : ∀ i : ℕ, r - min (d+i+1) r = (r-d)-1-i := by
    intro i
    omega
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range]
  exact sum_truncated_descending (r-d) n (by omega)

end MAPFordMixedTriangularExponent

#print axioms MAPFordMixedTriangularExponent.mixed_exponent_eq_triangular
