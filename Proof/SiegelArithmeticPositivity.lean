import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Arithmetic positivity at the start of Koukoulopoulos Theorem 12.8

Mathlib already proves nonnegativity of `zetaMul chi = 1 * chi` for quadratic
characters.  The first source step not present there is the stronger square
coefficient bound `(1 * chi)(n^2) >= 1` for positive `n`.
-/

open ComplexOrder

namespace DirichletCharacter

noncomputable section

/-- Every even prime-power coefficient of `1 * chi` is at least one for a
quadratic character. -/
theorem one_le_zetaMul_prime_pow_two_mul
    {N : ℕ} {chi : DirichletCharacter ℂ N} (hchi : chi ^ 2 = 1)
    {p : ℕ} (hp : p.Prime) (k : ℕ) :
    1 ≤ zetaMul chi (p ^ (2 * k)) := by
  simp only [zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk, Nat.sum_divisors_prime_pow hp,
    pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hchi p with h | h | h
  · simp [h]
  · simp [h]
    positivity
  · simp [h, neg_one_geom_sum]

/-- Koukoulopoulos, proof of Theorem 12.8: `(1 * chi)(n^2) >= 1` for every
positive integer `n`. -/
theorem one_le_zetaMul_sq
    {N : ℕ} [NeZero N] {chi : DirichletCharacter ℂ N}
    (hchi : chi ^ 2 = 1) {n : ℕ} (hn : n ≠ 0) :
    1 ≤ zetaMul chi (n ^ 2) := by
  rw [chi.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hn)]
  refine Finset.one_le_prod (fun p hp => ?_)
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  simpa [Nat.factorization_pow, mul_comm] using
    one_le_zetaMul_prime_pow_two_mul hchi hpPrime (n.factorization p)

end
end DirichletCharacter

#print axioms DirichletCharacter.one_le_zetaMul_prime_pow_two_mul
#print axioms DirichletCharacter.one_le_zetaMul_sq
