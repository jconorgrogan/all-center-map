import JutilaP53Lemma2Bridge

/-!
# Multiplicativity of Jutila's p.53 divisor kernel

The contour argument on journal page 53 uses the fact that the correction
coefficient `h(d;r,r')` is a finite Euler coefficient.  Before computing its
prime factors one must first justify its multiplicativity.  This file closes
that algebraic step for the *actual* p.53 coefficient already used by the
right-line factorization.

No support, Euler-factor, or analytic estimate is assumed here.  Those are
separate consequences of the prime-power computation.
-/

namespace MAPJutilaP53DivisorKernelMultiplicative

open scoped ArithmeticFunction.Moebius
open ArithmeticFunction
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53Lemma2Bridge
open MAPJutilaPseudocharacterAlgebra

noncomputable section

/-- The arithmetic function `μ(n)φ(n)` underlying every pseudocharacter. -/
private def p53SelbergArithmetic : ArithmeticFunction ℂ where
  toFun n := (ArithmeticFunction.moebius n : ℂ) * (Nat.totient n : ℂ)
  map_zero' := by simp

private theorem p53SelbergArithmetic_multiplicative :
    p53SelbergArithmetic.IsMultiplicative := by
  constructor
  · simp [p53SelbergArithmetic]
  · intro m n hcop
    simp [p53SelbergArithmetic,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hcop]
    ring

/-- One unnormalised Selberg pseudocharacter, represented as an arithmetic
function.  The value at zero is the obligatory arithmetic-function value and
does not occur in the positive-index Dirichlet series. -/
def p53SinglePseudoArithmetic (r : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else jutilaP53SelbergPseudoAt r n
  map_zero' := by simp

@[simp] theorem p53SinglePseudoArithmetic_apply_of_pos
    (r : ℕ) {n : ℕ} (hn : 0 < n) :
    p53SinglePseudoArithmetic r n = jutilaP53SelbergPseudoAt r n := by
  simp [p53SinglePseudoArithmetic, hn.ne']

/-- Taking `gcd(r,·)` preserves multiplicativity.  The source uses this
implicitly when it passes from Lemma 2 to an Euler product. -/
theorem p53SinglePseudoArithmetic_multiplicative (r : ℕ) :
    (p53SinglePseudoArithmetic r).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [p53SinglePseudoArithmetic, jutilaP53SelbergPseudoAt]
  · intro m n hm hn hcop
    have hmn : m * n ≠ 0 := mul_ne_zero hm hn
    have hgcd : r.gcd (m * n) = r.gcd m * r.gcd n := hcop.gcd_mul r
    have hcopGcd : (r.gcd m).Coprime (r.gcd n) :=
      Nat.Coprime.of_dvd (Nat.gcd_dvd_right r m)
        (Nat.gcd_dvd_right r n) hcop
    change (if m * n = 0 then 0 else jutilaP53SelbergPseudoAt r (m * n)) =
      (if m = 0 then 0 else jutilaP53SelbergPseudoAt r m) *
        (if n = 0 then 0 else jutilaP53SelbergPseudoAt r n)
    rw [if_neg hmn, if_neg hm, if_neg hn]
    unfold jutilaP53SelbergPseudoAt
    rw [hgcd]
    exact p53SelbergArithmetic_multiplicative.map_mul_of_coprime hcopGcd

/-- The pair pseudocharacter in the p.53 kernel is the pointwise product of
the two single pseudocharacters. -/
theorem p53PairPseudoArithmetic_eq_pmul (r r' : ℕ) :
    p53PairPseudoArithmetic r r' =
      (p53SinglePseudoArithmetic r).pmul
        (p53SinglePseudoArithmetic r') := by
  ext n
  rw [ArithmeticFunction.pmul_apply]
  by_cases hn : n = 0
  · subst n
    simp [p53PairPseudoArithmetic, p53SinglePseudoArithmetic]
  · simp [p53PairPseudoArithmetic, p53SinglePseudoArithmetic, hn]

theorem p53PairPseudoArithmetic_multiplicative (r r' : ℕ) :
    (p53PairPseudoArithmetic r r').IsMultiplicative := by
  rw [p53PairPseudoArithmetic_eq_pmul]
  exact (p53SinglePseudoArithmetic_multiplicative r).pmul
    (p53SinglePseudoArithmetic_multiplicative r')

/-- Jutila's correction coefficient `h(d;r,r') = μ * (f_r f_r')` is
multiplicative.  This is the last structural input needed before the local
prime-power calculation and the finite-support Euler continuation. -/
theorem p53PairDivisorKernel_multiplicative (r r' : ℕ) :
    (p53PairDivisorKernel r r').IsMultiplicative := by
  unfold p53PairDivisorKernel MAPJutilaPseudocharacterAlgebra.divisorKernel
  exact ArithmeticFunction.isMultiplicative_moebius.intCast.mul
    (p53PairPseudoArithmetic_multiplicative r r')

/-! ## The exact prime-power input -/

/-- For squarefree `r`, its gcd with a positive prime power is either `p`
or `1`, according as `p ∣ r` or not. -/
theorem gcd_squarefree_prime_pow
    {r p k : ℕ} (hr : Squarefree r) (hp : p.Prime) (hk : 0 < k) :
    r.gcd (p ^ k) = if p ∣ r then p else 1 := by
  by_cases hpr : p ∣ r
  · rw [if_pos hpr]
    have hfactor : r / p * p = r := Nat.div_mul_cancel hpr
    have hcop : (r / p).Coprime p := by
      apply Nat.coprime_of_squarefree_mul
      simpa only [hfactor] using hr
    have hcopPow : (r / p).Coprime (p ^ k) :=
      hcop.pow_right k
    calc
      r.gcd (p ^ k) = ((r / p) * p).gcd (p ^ k) := by rw [hfactor]
      _ = p := Nat.gcd_mul_of_coprime_of_dvd hcopPow
        (dvd_pow_self p hk.ne')
  · rw [if_neg hpr]
    have hcop : r.Coprime p :=
      ((hp.coprime_iff_not_dvd).mpr hpr).symm
    exact (hcop.pow_right k).gcd_eq_one

theorem p53SinglePseudoArithmetic_prime_pow
    {r p k : ℕ} (hr : Squarefree r) (hp : p.Prime) (hk : 0 < k) :
    p53SinglePseudoArithmetic r (p ^ k) =
      if p ∣ r then (1 - (p : ℂ)) else 1 := by
  have hpk : 0 < p ^ k := pow_pos hp.pos k
  change (if p ^ k = 0 then 0 else
    jutilaP53SelbergPseudoAt r (p ^ k)) = _
  rw [if_neg hpk.ne', jutilaP53SelbergPseudoAt,
    gcd_squarefree_prime_pow hr hp hk]
  by_cases hpr : p ∣ r
  · simp only [if_pos hpr, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime hp]
    rw [Nat.cast_sub hp.one_le]
    push_cast
    ring
  · simp [hpr]

/-- Local value of the unnormalised pair pseudocharacter. -/
theorem p53PairPseudoArithmetic_prime_pow
    {r r' p k : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hp : p.Prime) (hk : 0 < k) :
    p53PairPseudoArithmetic r r' (p ^ k) =
      (if p ∣ r then (1 - (p : ℂ)) else 1) *
        (if p ∣ r' then (1 - (p : ℂ)) else 1) := by
  rw [p53PairPseudoArithmetic_eq_pmul]
  simp only [ArithmeticFunction.pmul_apply,
    p53SinglePseudoArithmetic_prime_pow hr hp hk,
    p53SinglePseudoArithmetic_prime_pow hr' hp hk]

/-- The prime coefficient of the correction kernel is the local pair factor
minus one. -/
theorem p53PairDivisorKernel_prime
    {r r' p : ℕ} (hp : p.Prime) :
    p53PairDivisorKernel r r' p =
      p53PairPseudoArithmetic r r' p - 1 := by
  unfold p53PairDivisorKernel MAPJutilaPseudocharacterAlgebra.divisorKernel
  rw [ArithmeticFunction.mul_apply]
  have hsum := Nat.sum_divisorsAntidiagonal
    (fun a b =>
      ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) a) *
        p53PairPseudoArithmetic r r' b) (n := p)
  rw [hsum, hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact fun h => hp.ne_one h.symm
  rw [Finset.sum_insert hnot, Finset.sum_singleton,
    Nat.div_one, Nat.div_self hp.pos]
  simp only [ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_neg, Int.cast_one]
  have hFone : p53PairPseudoArithmetic r r' 1 = 1 :=
    (p53PairPseudoArithmetic_multiplicative r r').map_one
  rw [hFone]
  simp
  ring

theorem p53PairDivisorKernel_prime_local
    {r r' p : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hp : p.Prime) :
    p53PairDivisorKernel r r' p =
      (if p ∣ r then
        if p ∣ r' then (p : ℂ) * ((p : ℂ) - 2) else -(p : ℂ)
      else
        if p ∣ r' then -(p : ℂ) else 0) := by
  have hpair := p53PairPseudoArithmetic_prime_pow hr hr' hp
    (by norm_num : 0 < 1)
  simp only [pow_one] at hpair
  rw [p53PairDivisorKernel_prime hp, hpair]
  by_cases hpr : p ∣ r <;> by_cases hpr' : p ∣ r' <;>
    simp [hpr, hpr'] <;> ring

/-- Every prime-square and higher coefficient of the correction kernel
vanishes.  This is the squarefree-support half of the finite Euler product. -/
theorem p53PairDivisorKernel_prime_pow_succ_succ
    {r r' p k : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hp : p.Prime) :
    p53PairDivisorKernel r r' (p ^ (k + 2)) = 0 := by
  have hbig := sum_p53PairDivisorKernel r r'
    (n := p ^ (k + 2)) (pow_pos hp.pos _)
  have hsmall := sum_p53PairDivisorKernel r r'
    (n := p ^ (k + 1)) (pow_pos hp.pos _)
  simp only [Nat.sum_divisors_prime_pow hp] at hbig hsmall
  rw [Finset.sum_range_succ] at hbig hsmall
  have hF : p53PairPseudoArithmetic r r' (p ^ (k + 2)) =
      p53PairPseudoArithmetic r r' (p ^ (k + 1)) := by
    rw [p53PairPseudoArithmetic_prime_pow hr hr' hp (by omega : 0 < k + 2),
      p53PairPseudoArithmetic_prime_pow hr hr' hp (by omega : 0 < k + 1)]
  have hJ :
      jutilaP53SelbergPseudoAt r (p ^ (k + 2)) *
          jutilaP53SelbergPseudoAt r' (p ^ (k + 2)) =
        jutilaP53SelbergPseudoAt r (p ^ (k + 1)) *
          jutilaP53SelbergPseudoAt r' (p ^ (k + 1)) := by
    simpa [p53PairPseudoArithmetic, hp.ne_zero] using hF
  rw [Finset.sum_range_succ] at hbig
  rw [hsmall, ← hJ] at hbig
  have hbig' :
      jutilaP53SelbergPseudoAt r (p ^ (k + 2)) *
          jutilaP53SelbergPseudoAt r' (p ^ (k + 2)) +
          p53PairDivisorKernel r r' (p ^ (k + 2)) =
        jutilaP53SelbergPseudoAt r (p ^ (k + 2)) *
          jutilaP53SelbergPseudoAt r' (p ^ (k + 2)) + 0 := by
    simpa only [add_zero] using hbig
  exact add_left_cancel hbig'

/-- The actual correction coefficient is supported on squarefree indices.
This follows from multiplicativity and the prime-square calculation, rather
than being imported from the separately defined model Euler product. -/
theorem p53PairDivisorKernel_eq_zero_of_not_squarefree
    {r r' n : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hn0 : n ≠ 0) (hn : ¬ Squarefree n) :
    p53PairDivisorKernel r r' n = 0 := by
  rw [(p53PairDivisorKernel_multiplicative r r').multiplicative_factorization
    (p53PairDivisorKernel r r') hn0]
  have hex : ∃ p : ℕ, 1 < n.factorization p := by
    rw [Nat.squarefree_iff_factorization_le_one hn0] at hn
    push Not at hn
    exact hn
  obtain ⟨p, hpTwo⟩ := hex
  have hpPos : 0 < n.factorization p := zero_lt_one.trans hpTwo
  have hpPrime : p.Prime := by
    by_contra hp
    rw [Nat.factorization_eq_zero_of_not_prime n hp] at hpPos
    omega
  have hpMem : p ∈ n.factorization.support := by
    rw [Finsupp.mem_support_iff]
    omega
  apply Finset.prod_eq_zero hpMem
  have htwo : 2 ≤ n.factorization p := by omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le htwo
  have hk' : n.factorization p = k + 2 := by omega
  rw [hk']
  exact p53PairDivisorKernel_prime_pow_succ_succ hr hr' hpPrime

/-- A squarefree index containing a prime outside `lcm(r,r')` also has zero
coefficient.  Together with the preceding theorem, this proves that the
actual correction kernel is supported on divisors of `lcm(r,r')`. -/
theorem p53PairDivisorKernel_eq_zero_of_not_dvd_lcm
    {r r' n : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hn0 : n ≠ 0) (hn : Squarefree n) (hnd : ¬ n ∣ r.lcm r') :
    p53PairDivisorKernel r r' n = 0 := by
  have hnotSubset : ¬ n.primeFactors ⊆ (r.lcm r').primeFactors := by
    intro hsub
    have hpDvd : (∏ p ∈ n.primeFactors, p) ∣
        ∏ p ∈ (r.lcm r').primeFactors, p :=
      Finset.prod_dvd_prod_of_subset n.primeFactors
        (r.lcm r').primeFactors (fun p : ℕ => p) hsub
    have hprodN : ∏ p ∈ n.primeFactors, p = n :=
      Nat.prod_primeFactors_of_squarefree hn
    apply hnd
    rw [← hprodN]
    exact hpDvd.trans (Nat.prod_primeFactors_dvd (r.lcm r'))
  obtain ⟨p, hpn, hplcm⟩ := Finset.not_subset.mp hnotSubset
  have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hpn).1
  have hpNotDvd : ¬ p ∣ r.lcm r' := by
    intro hd
    exact hplcm (Nat.mem_primeFactors.mpr ⟨hpPrime, hd, by
      exact Nat.lcm_ne_zero (Squarefree.ne_zero hr) (Squarefree.ne_zero hr')⟩)
  have hpr : ¬ p ∣ r := fun hd =>
    hpNotDvd (hd.trans (Nat.dvd_lcm_left r r'))
  have hpr' : ¬ p ∣ r' := fun hd =>
    hpNotDvd (hd.trans (Nat.dvd_lcm_right r r'))
  rw [(p53PairDivisorKernel_multiplicative r r').multiplicative_factorization
    (p53PairDivisorKernel r r') hn0]
  have hpMem : p ∈ n.factorization.support := hpn
  apply Finset.prod_eq_zero hpMem
  rw [Nat.factorization_eq_one_of_squarefree hn hpPrime
    (Nat.mem_primeFactors.mp hpn).2.1]
  have hz : p53PairDivisorKernel r r' p = 0 := by
    rw [p53PairDivisorKernel_prime_local hr hr' hpPrime]
    simp [hpr, hpr']
  simpa only [pow_one] using hz

/-- Complete support theorem in the form used by the p.53 outer `d`-sum. -/
theorem p53PairDivisorKernel_eq_zero_of_not_dvd_lcm'
    {r r' n : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hn0 : n ≠ 0) (hnd : ¬ n ∣ r.lcm r') :
    p53PairDivisorKernel r r' n = 0 := by
  by_cases hn : Squarefree n
  · exact p53PairDivisorKernel_eq_zero_of_not_dvd_lcm hr hr' hn0 hn hnd
  · exact p53PairDivisorKernel_eq_zero_of_not_squarefree hr hr' hn0 hn

/-- The infinite notation for the correction series is literally a finite
sum over the divisors of `lcm(r,r')`. -/
theorem tsum_p53PairDivisorKernel_eq_sum_divisors
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ∑' d : ℕ, p53PairDivisorKernel r r' d =
      ∑ d ∈ (r.lcm r').divisors, p53PairDivisorKernel r r' d := by
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    exact ArithmeticFunction.map_zero
  · apply p53PairDivisorKernel_eq_zero_of_not_dvd_lcm' hr hr' hd0
    intro hdiv
    exact hd (Nat.mem_divisors.mpr ⟨hdiv,
      Nat.lcm_ne_zero (Squarefree.ne_zero hr) (Squarefree.ne_zero hr')⟩)


end

end MAPJutilaP53DivisorKernelMultiplicative

#print axioms MAPJutilaP53DivisorKernelMultiplicative.p53SinglePseudoArithmetic_multiplicative
#print axioms MAPJutilaP53DivisorKernelMultiplicative.p53PairPseudoArithmetic_multiplicative
#print axioms MAPJutilaP53DivisorKernelMultiplicative.p53PairDivisorKernel_multiplicative
#print axioms MAPJutilaP53DivisorKernelMultiplicative.p53PairDivisorKernel_prime_pow_succ_succ
#print axioms MAPJutilaP53DivisorKernelMultiplicative.p53PairDivisorKernel_eq_zero_of_not_dvd_lcm'
#print axioms MAPJutilaP53DivisorKernelMultiplicative.tsum_p53PairDivisorKernel_eq_sum_divisors
