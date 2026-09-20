import FordLemma33Dichotomy

open scoped BigOperators
namespace FordUniformFiberSum

/-- Sum an actual finite family of nonnegative counts using a uniform squared
bound. Empty index types are allowed. -/
theorem sum_sq_le_uniform {I : Type*} [Fintype I]
    (c : I → ℝ) {V : ℝ} (hV : 0 ≤ V)
    (hc : ∀ i, 0 ≤ c i) (hbound : ∀ i, c i ^ 2 ≤ V) :
    (∑ i, c i) ^ 2 ≤ (Fintype.card I : ℝ) ^ 2 * V := by
  classical
  have hs := Real.sq_sqrt hV
  have hn := Real.sqrt_nonneg V
  have hpoint : ∀ i, c i ≤ Real.sqrt V := by
    intro i
    have hi := hbound i
    nlinarith [hc i]
  have hsum : (∑ i, c i) ≤ (Fintype.card I : ℝ) * Real.sqrt V := by
    calc
      (∑ i, c i) ≤ ∑ _i : I, Real.sqrt V :=
        Finset.sum_le_sum (fun i _ => hpoint i)
      _ = _ := by simp
  calc
    (∑ i, c i) ^ 2 ≤ ((Fintype.card I : ℝ) * Real.sqrt V) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg (fun i _ => hc i)) hsum 2
    _ = (Fintype.card I : ℝ) ^ 2 * V := by rw [mul_pow, hs]

end FordUniformFiberSum

#print axioms FordUniformFiberSum.sum_sq_le_uniform
