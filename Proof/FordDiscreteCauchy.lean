import GuthMaynardJIterationDeterministic

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteCauchy

/-- Finite complex Cauchy--Schwarz on a natural range. -/
theorem norm_sum_range_sq_le_card_mul_sum_norm_sq
    (L : ℕ) (F : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range L, F r‖ ^ 2 ≤
      (L : ℝ) * ∑ r ∈ Finset.range L, ‖F r‖ ^ 2 := by
  simpa using
    (GuthMaynardJIteration.norm_finset_sum_sq_le_card_mul_sum_norm_sq
      (s := Finset.range L) F)

/-- Exact finite expansion of a complex norm square into its full ordered
correlation sum. Splitting the ordered sum into diagonal and upper/lower
triangles is then a purely finite `Finset` rearrangement. -/
theorem norm_sum_range_sq_eq_real_double_correlation
    (L : ℕ) (F : ℕ → ℂ) :
    ‖∑ r ∈ Finset.range L, F r‖ ^ 2 =
      Complex.re (∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L,
        F r * star (F s)) := by
  have hcomplex :
      (((‖∑ r ∈ Finset.range L, F r‖ ^ 2 : ℝ) : ℂ)) =
        ∑ r ∈ Finset.range L, ∑ s ∈ Finset.range L,
          F r * star (F s) := by
    rw [Complex.sq_norm, ← Complex.mul_conj]
    change (∑ r ∈ Finset.range L, F r) *
        star (∑ r ∈ Finset.range L, F r) = _
    rw [star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
  have hreal := congrArg Complex.re hcomplex
  simpa only [Complex.ofReal_re] using hreal

end FordDiscreteCauchy

#print axioms FordDiscreteCauchy.norm_sum_range_sq_le_card_mul_sum_norm_sq
#print axioms FordDiscreteCauchy.norm_sum_range_sq_eq_real_double_correlation
