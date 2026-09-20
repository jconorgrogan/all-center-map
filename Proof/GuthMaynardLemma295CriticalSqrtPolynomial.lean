import GuthMaynardLemma295CriticalTailPointwise

namespace GuthMaynardLemma295CriticalSqrtPolynomial

open Complex GuthMaynardLemma295DualTail GuthMaynardJutilaReflection2941

noncomputable section

private theorem inv_sqrt_succ_le (n : ℕ) :
    1 / Real.sqrt (n + 1 : ℝ) ≤
      2 * (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 < Real.sqrt (n + 1 : ℝ) := Real.sqrt_pos.2 (by positivity)
  have ha := Real.sq_sqrt hn
  have hb := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n + 1)
  have hab := Real.sqrt_le_sqrt (show (n : ℝ) ≤ n + 1 by linarith)
  have hs := sq_nonneg (Real.sqrt (n + 1 : ℝ) - Real.sqrt (n : ℝ))
  apply (div_le_iff₀ hp).2
  nlinarith

private theorem sum_inv_sqrt_le (K : ℕ) :
    (∑ n ∈ Finset.range K, 1 / Real.sqrt (n + 1 : ℝ)) ≤ 2 * Real.sqrt K := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have h := inv_sqrt_succ_le K
    push_cast
    linarith

 theorem norm_lemma295ReflectedPolynomial_nat_le_sqrt
    (K : ℕ) (tau : ℝ) :
    ‖lemma295ReflectedPolynomial K tau‖ ≤ 2 * Real.sqrt K := by
  have heq := sourceDualPartialNat_critical_eq_reflectedPolynomial_neg K (-tau)
  have heq' : lemma295ReflectedPolynomial K tau =
      sourceDualPartialNat K (((1 / 2 : ℝ) : ℂ) - (-tau) * I) := by
    simpa using heq.symm
  rw [heq']
  unfold sourceDualPartialNat
  calc
    ‖∑ n ∈ Finset.range K,
        1 / ((n + 1 : ℕ) : ℂ) ^ (1 - (((1 / 2 : ℝ) : ℂ) - (-tau) * I))‖
        ≤ ∑ n ∈ Finset.range K,
          ‖1 / ((n + 1 : ℕ) : ℂ) ^ (1 - (((1 / 2 : ℝ) : ℂ) - (-tau) * I))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.range K, 1 / Real.sqrt (n + 1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos (by omega)]
      simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re,
        Complex.neg_re, Complex.I_re, Complex.I_im]
      norm_num
      rw [Real.sqrt_eq_rpow]
    _ ≤ 2 * Real.sqrt K := sum_inv_sqrt_le K

end
end GuthMaynardLemma295CriticalSqrtPolynomial

#print axioms GuthMaynardLemma295CriticalSqrtPolynomial.norm_lemma295ReflectedPolynomial_nat_le_sqrt
