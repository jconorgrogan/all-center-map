import Mathlib

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteCorrelationDiagonal

/-- Literal forward correlation of a finite sequence, with the empty range
covering all separations at least `N`. -/
def correlation (N h : ℕ) (f : ℕ → ℂ) : ℂ :=
  ∑ n ∈ Finset.range (N - h), f (n + h) * conj (f n)

lemma correlation_zero_eq (N : ℕ) (f : ℕ → ℂ) :
    correlation N 0 f = ∑ n ∈ Finset.range N, f n * conj (f n) := by
  simp [correlation]

/-- Every literal correlation is bounded by its number of available pairs. -/
theorem correlation_norm_le {N h : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.range N, ‖f n‖ ≤ 1) :
    ‖correlation N h f‖ ≤ (N - h : ℕ) := by
  unfold correlation
  calc
    _ ≤ ∑ n ∈ Finset.range (N - h), ‖f (n + h) * conj (f n)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range (N - h), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, Complex.norm_conj]
      have hnN : n + h < N := by
        have hn' := Finset.mem_range.mp hn
        omega
      exact mul_le_one₀ (hf (n + h) (Finset.mem_range.mpr hnN)) (norm_nonneg _) (hf n (Finset.mem_range.mpr (by omega)))
    _ = (N - h : ℕ) := by simp

/-- Diagonal correlation is bounded by `N`, including the `N=0` case. -/
theorem diagonal_norm_le {N : ℕ} (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.range N, ‖f n‖ ≤ 1) :
    ‖correlation N 0 f‖ ≤ (N : ℝ) := by
  simpa using (correlation_norm_le (N := N) (h := 0) f hf)

end FordDiscreteCorrelationDiagonal

#print axioms FordDiscreteCorrelationDiagonal.correlation_norm_le
#print axioms FordDiscreteCorrelationDiagonal.diagonal_norm_le
