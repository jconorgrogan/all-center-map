import JutilaP53DivisorKernelAbsoluteMass
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # Signed residue mass of the actual p.53 divisor kernel -/
namespace MAPJutilaP53SignedDivisorMass

open scoped BigOperators
open ArithmeticFunction
open MAPJutilaPseudocharacterAlgebra MAPJutilaP53Lemma2Bridge
open MAPJutilaP53DivisorKernelMultiplicative MAPJutilaP53DivisorKernelAbsoluteMass

noncomputable section

def p53PairDivisorKernelAtOne (r r' : ℕ) : ArithmeticFunction ℂ where
  toFun d := p53PairDivisorKernel r r' d / (d : ℂ)
  map_zero' := by simp

theorem p53PairDivisorKernelAtOne_multiplicative (r r' : ℕ) :
    (p53PairDivisorKernelAtOne r r').IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [p53PairDivisorKernelAtOne,
      (p53PairDivisorKernel_multiplicative r r').map_one]
  · intro m n hm hn hcop
    change p53PairDivisorKernel r r' (m*n) / ((m*n : ℕ) : ℂ) = _
    rw [(p53PairDivisorKernel_multiplicative r r').map_mul_of_coprime hcop,
      Nat.cast_mul]
    exact mul_div_mul_comm _ _ _ _

/-- Retaining the sign before the divisor sum recovers the exact Euler
product at one, including its off-diagonal cancellation. -/
theorem sum_p53PairDivisorKernel_div_eq_lemmaThreeEulerAtOne
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    (∑ d ∈ (r.lcm r').divisors, p53PairDivisorKernel r r' d / (d : ℂ)) =
      (lemmaThreeEulerAtOne r.primeFactors r'.primeFactors : ℂ) := by
  have heuler := (p53PairDivisorKernelAtOne_multiplicative r r').prodPrimeFactors_one_add_of_squarefree
    (squarefree_lcm hr hr')
  change ∑ d ∈ (r.lcm r').divisors, p53PairDivisorKernelAtOne r r' d = _
  rw [← heuler, primeFactors_lcm (Squarefree.ne_zero hr) (Squarefree.ne_zero hr'),
    primeFactors_union_decomposition,
    Finset.prod_union (disjoint_exclusive_inter r.primeFactors r'.primeFactors)]
  unfold lemmaThreeEulerAtOne
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro p hpEx
    have hpU : p ∈ r.primeFactors ∪ r'.primeFactors := by
      rw [primeFactors_union_decomposition]
      exact Finset.mem_union_left _ hpEx
    have hp : p.Prime := (Finset.mem_union.mp hpU).elim
      Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
    have hx : (p ∣ r ∧ ¬ p ∣ r') ∨ (p ∣ r' ∧ ¬ p ∣ r) := by
      simpa [exclusivePrimes, Nat.mem_primeFactors, hp,
        Squarefree.ne_zero hr, Squarefree.ne_zero hr'] using hpEx
    change 1 + p53PairDivisorKernel r r' p / (p : ℂ) = _
    rw [p53PairDivisorKernel_prime_local hr hr' hp]
    rcases hx with hx | hx <;> simp [hx.1, hx.2]
  · apply Finset.prod_congr rfl
    intro p hpI
    have hpR := (Finset.mem_inter.mp hpI).1
    have hpR' := (Finset.mem_inter.mp hpI).2
    change 1 + p53PairDivisorKernel r r' p / (p : ℂ) = _
    rw [p53PairDivisorKernel_prime_local hr hr' (Nat.prime_of_mem_primeFactors hpR)]
    simp [Nat.dvd_of_mem_primeFactors hpR, Nat.dvd_of_mem_primeFactors hpR']

/-- The actual divisor kernel has signed residue mass `phi(r)` on the
pseudocharacter diagonal and zero off it. -/
theorem sum_p53PairDivisorKernel_div_eq_diagonal
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    (∑ d ∈ (r.lcm r').divisors, p53PairDivisorKernel r r' d / (d : ℂ)) =
      if r = r' then (Nat.totient r : ℂ) else 0 := by
  rw [sum_p53PairDivisorKernel_div_eq_lemmaThreeEulerAtOne hr hr',
    lemmaThreeEulerAtOne_primeFactors (Squarefree.ne_zero hr) (Squarefree.ne_zero hr') hr hr']
  split_ifs <;> norm_cast

/-- The surviving normalized diagonal costs only one harmonic sum. -/
theorem sum_totient_div_sq_le_harmonic
    {S : Finset ℕ} {R : ℕ} (hS : S ⊆ Finset.Icc 1 R) :
    (∑ r ∈ S, (Nat.totient r : ℝ) / (r : ℝ)^2) ≤ (harmonic R : ℝ) := by
  calc
    _ ≤ ∑ r ∈ S, (r : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro r hr
      have hrpos : 0 < r := (Finset.mem_Icc.mp (hS hr)).1
      have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hrpos
      have hphi : (Nat.totient r : ℝ) ≤ (r : ℝ) := by
        exact_mod_cast Nat.totient_le r
      calc
        (Nat.totient r : ℝ) / (r : ℝ)^2 ≤ (r : ℝ) / (r : ℝ)^2 :=
          div_le_div_of_nonneg_right hphi (sq_nonneg _)
        _ = (r : ℝ)⁻¹ := by field_simp
    _ ≤ ∑ r ∈ Finset.Icc 1 R, (r : ℝ)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg hS (fun r hrI hrS => by positivity)
    _ = (harmonic R : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl

end
end MAPJutilaP53SignedDivisorMass

#print axioms MAPJutilaP53SignedDivisorMass.sum_p53PairDivisorKernel_div_eq_diagonal

#print axioms MAPJutilaP53SignedDivisorMass.sum_totient_div_sq_le_harmonic
