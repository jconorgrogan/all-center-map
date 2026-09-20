import Mathlib

/-!
# Algebraic leaves behind Jutila's pseudocharacter Lemmas 2 and 3

This staging file records the exact Mobius-inversion mechanism in Lemma 2 and
the local-factor diagonal collapse in Lemma 3 of Jutila (1977), pp. 48--49.
It contains no asymptotic estimate and no assertion about Dirichlet zeros.
-/

namespace MAPJutilaPseudocharacterAlgebra

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius
open ArithmeticFunction

noncomputable section

/-! ## Lemma 2 as exact divisor inversion -/

/-- For an arithmetic function `F`, the coefficient family of the Euler
quotient `F/zeta` is its Mobius convolution. -/
def divisorKernel (F : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  (μ : ArithmeticFunction ℂ) * F

/-- Exact coefficient statement of Jutila's Lemma 2:
`F(n) = sum_{d|n} h(d)`.  In the source, `F(n)=f_r(n)f_{r'}(n)` and the
finite Euler product printed before Lemma 2 specifies `h`. -/
theorem sum_divisorKernel (F : ArithmeticFunction ℂ) (n : ℕ) :
    ∑ d ∈ n.divisors, divisorKernel F d = F n := by
  rw [← coe_zeta_mul_apply]
  unfold divisorKernel
  rw [← mul_assoc, coe_zeta_mul_coe_moebius, one_mul]

/-- Uniqueness of the coefficient family in Lemma 2. -/
theorem divisorKernel_unique
    (F h : ArithmeticFunction ℂ)
    (hdiv : ∀ n : ℕ, ∑ d ∈ n.divisors, h d = F n) :
    h = divisorKernel F := by
  have hzeta : (ζ : ArithmeticFunction ℂ) * h = F := by
    ext n
    rw [coe_zeta_mul_apply]
    exact hdiv n
  calc
    h = (1 : ArithmeticFunction ℂ) * h := by simp
    _ = ((μ : ArithmeticFunction ℂ) * ζ) * h := by
      rw [coe_moebius_mul_coe_zeta]
    _ = (μ : ArithmeticFunction ℂ) * ((ζ : ArithmeticFunction ℂ) * h) := by
      rw [mul_assoc]
    _ = divisorKernel F := by rw [hzeta]; rfl

/-! ## The source local factors for `f(n)=mu(n) phi(n)` -/

/-- Primes which divide exactly one of `r,r'`, expressed at the finite-set
level used by the Euler product in Jutila's Lemma 2. -/
def exclusivePrimes (A B : Finset ℕ) : Finset ℕ :=
  (A \ B) ∪ (B \ A)

/-- The Euler product at `s=1` from Jutila's Lemma 3.  For
`f(p)=mu(p)phi(p)=1-p`, an exclusive prime has coefficient `-p`, while a
common prime has coefficient `p(p-2)`. -/
def lemmaThreeEulerAtOne (A B : Finset ℕ) : ℚ :=
  (∏ p ∈ exclusivePrimes A B,
      (1 + (-(p : ℚ)) / (p : ℚ))) *
    ∏ p ∈ A ∩ B,
      (1 + ((p : ℚ) * ((p : ℚ) - 2)) / (p : ℚ))

theorem exclusivePrimes_eq_empty_iff (A B : Finset ℕ) :
    exclusivePrimes A B = ∅ ↔ A = B := by
  classical
  constructor
  · intro h
    apply Finset.Subset.antisymm
    · intro p hpA
      by_contra hpB
      have hp : p ∈ exclusivePrimes A B := by
        simp [exclusivePrimes, hpA, hpB]
      rw [h] at hp
      simpa using hp
    · intro p hpB
      by_contra hpA
      have hp : p ∈ exclusivePrimes A B := by
        simp [exclusivePrimes, hpA, hpB]
      rw [h] at hp
      simpa using hp
  · rintro rfl
    change (A \ A) ∪ (A \ A) = ∅
    simp

theorem lemmaThreeEulerAtOne_eq_zero_of_ne
    (A B : Finset ℕ) (hAB : A ≠ B)
    (hpos : ∀ p ∈ exclusivePrimes A B, 0 < p) :
    lemmaThreeEulerAtOne A B = 0 := by
  classical
  have hne : exclusivePrimes A B ≠ ∅ :=
    fun h => hAB ((exclusivePrimes_eq_empty_iff A B).mp h)
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hpos p hp).ne'
  unfold lemmaThreeEulerAtOne
  have hfactor : (1 + (-(p : ℚ)) / (p : ℚ)) = 0 := by
    field_simp
    norm_num
  have hprod : (∏ a ∈ exclusivePrimes A B,
      (1 + (-(a : ℚ)) / (a : ℚ))) = 0 := by
    apply Finset.prod_eq_zero hp
    exact hfactor
  simp [hprod]

theorem lemmaThreeEulerAtOne_self
    (A : Finset ℕ) (hpos : ∀ p ∈ A, 0 < p) :
    lemmaThreeEulerAtOne A A = ∏ p ∈ A, ((p : ℚ) - 1) := by
  classical
  unfold lemmaThreeEulerAtOne
  rw [show exclusivePrimes A A = ∅ by simp [exclusivePrimes]]
  simp only [Finset.prod_empty, Finset.inter_self, one_mul]
  apply Finset.prod_congr rfl
  intro p hp
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hpos p hp).ne'
  field_simp
  ring

theorem prod_prime_sub_one_eq_totient
    {r : ℕ} (hr0 : r ≠ 0) (hr : Squarefree r) :
    (∏ p ∈ r.primeFactors, ((p : ℚ) - 1)) = (r.totient : ℚ) := by
  have hprod : ∏ p ∈ r.primeFactors, p = r :=
    Nat.prod_primeFactors_of_squarefree hr
  rw [Nat.totient_eq_div_primeFactors_mul, hprod,
    Nat.div_self (Nat.pos_of_ne_zero hr0), one_mul]
  rw [Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro p hp
  rw [Nat.cast_sub]
  · norm_num
  · exact (Nat.prime_of_mem_primeFactors hp).one_le

/-- Exact diagonal statement of Jutila's Lemma 3, at the Euler-product level:
the value at `s=1` is `phi(r)` on the diagonal and zero off it. -/
theorem lemmaThreeEulerAtOne_primeFactors
    {r r' : ℕ} (hr0 : r ≠ 0) (hr0' : r' ≠ 0)
    (hr : Squarefree r) (hr' : Squarefree r') :
    lemmaThreeEulerAtOne r.primeFactors r'.primeFactors =
      if r = r' then (r.totient : ℚ) else 0 := by
  classical
  by_cases hrr : r = r'
  · subst r'
    rw [if_pos rfl, lemmaThreeEulerAtOne_self]
    · exact prod_prime_sub_one_eq_totient hr0 hr
    · intro p hp
      exact Nat.pos_of_mem_primeFactors hp
  · rw [if_neg hrr]
    apply lemmaThreeEulerAtOne_eq_zero_of_ne
    · intro hsets
      apply hrr
      calc
        r = ∏ p ∈ r.primeFactors, p :=
          (Nat.prod_primeFactors_of_squarefree hr).symm
        _ = ∏ p ∈ r'.primeFactors, p := by rw [hsets]
        _ = r' := Nat.prod_primeFactors_of_squarefree hr'
    · intro p hp
      rw [exclusivePrimes, Finset.mem_union, Finset.mem_sdiff,
        Finset.mem_sdiff] at hp
      rcases hp with hp | hp
      · exact Nat.pos_of_mem_primeFactors hp.1
      · exact Nat.pos_of_mem_primeFactors hp.1

end

end MAPJutilaPseudocharacterAlgebra

#print axioms MAPJutilaPseudocharacterAlgebra.sum_divisorKernel
#print axioms MAPJutilaPseudocharacterAlgebra.divisorKernel_unique
#print axioms MAPJutilaPseudocharacterAlgebra.lemmaThreeEulerAtOne_primeFactors
