import JutilaMEntire

/-!
# Coefficient algebra behind Jutila Lemma 1

This file formalizes the arithmetic relation singled out in the published
proof of (2.2).  For squarefree `r`, writing `t = r/(r,d)`, the source uses

`f_r(n d) = f_r(d) f_t(n)`.

Here `f(n)=mu(n) phi(n)` and `f_r(n)=f((r,n))`.  The result below proves the
literal identity, including the exact gcd factorization on which it rests.
-/

namespace MAPJutilaLemma1CoefficientAlgebra

open ArithmeticFunction
open MAPJutilaPseudocharacterMExact
open MAPJutilaMEntire

noncomputable section

/-- The complex arithmetic function `mu(n) phi(n)` used in the source. -/
def selbergPseudoArithmetic : ArithmeticFunction ℂ where
  toFun := selbergPseudoCoeff
  map_zero' := by simp [selbergPseudoCoeff]

@[simp] theorem selbergPseudoArithmetic_apply (n : ℕ) :
    selbergPseudoArithmetic n = selbergPseudoCoeff n := rfl

theorem selbergPseudoArithmetic_multiplicative :
    selbergPseudoArithmetic.IsMultiplicative := by
  constructor
  · simp [selbergPseudoArithmetic, selbergPseudoCoeff]
  · intro m n hcop
    simp only [selbergPseudoArithmetic_apply, selbergPseudoCoeff]
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hcop]
    push_cast
    ring

/-- Exact gcd splitting in the sentence following Jutila (2.3). -/
theorem gcd_squarefree_mul_split
    {r d n : ℕ} (hr : Squarefree r) (hd : d ≠ 0) :
    r.gcd (n * d) = r.gcd d * (r / r.gcd d).gcd n := by
  let a := r.gcd d
  let b := r / a
  have haDvdR : a ∣ r := by
    dsimp [a]
    exact Nat.gcd_dvd_left r d
  have haDvdD : a ∣ d := by
    dsimp [a]
    exact Nat.gcd_dvd_right r d
  have hrFactor : b * a = r := by
    dsimp [b]
    exact Nat.div_mul_cancel haDvdR
  have hbCoprimeD : b.Coprime d := by
    dsimp [b, a]
    exact Nat.coprime_div_gcd_of_squarefree hr hd
  have hbCoprimeA : b.Coprime a := by
    apply Nat.coprime_of_squarefree_mul
    simpa only [hrFactor] using hr
  have hbGcd : b.gcd (n * d) = b.gcd n := by
    exact hbCoprimeD.symm.gcd_mul_right_cancel_right n
  have haGcd : (n * d).gcd a = a := by
    rw [Nat.gcd_eq_right_iff_dvd]
    exact dvd_mul_of_dvd_right haDvdD n
  calc
    r.gcd (n * d) = (n * d).gcd (b * a) := by
      rw [hrFactor, Nat.gcd_comm]
    _ = (n * d).gcd b * (n * d).gcd a :=
      hbCoprimeA.gcd_mul (n * d)
    _ = b.gcd n * a := by
      rw [haGcd, Nat.gcd_comm (n * d) b, hbGcd]
    _ = a * b.gcd n := by ring
    _ = r.gcd d * (r / r.gcd d).gcd n := by rfl

/-- The two gcd factors above are coprime, so a multiplicative `f` splits. -/
theorem gcd_factors_coprime
    {r d n : ℕ} (hr : Squarefree r) (hd : d ≠ 0) :
    (r.gcd d).Coprime ((r / r.gcd d).gcd n) := by
  have hbase : (r / r.gcd d).Coprime (r.gcd d) := by
    have hfactor : (r / r.gcd d) * r.gcd d = r :=
      Nat.div_mul_cancel (Nat.gcd_dvd_left r d)
    apply Nat.coprime_of_squarefree_mul
    simpa only [hfactor] using hr
  exact Nat.Coprime.of_dvd_right
    (Nat.gcd_dvd_left (r / r.gcd d) n) hbase.symm

/-- Literal relation `f_r(nd)=f_r(d)f_t(n)` from Jutila's proof of (2.2). -/
theorem selbergPseudoAt_mul_split
    {r d n : ℕ} (hr : Squarefree r) (hd : d ≠ 0) :
    selbergPseudoAt r (n * d) =
      selbergPseudoAt r d * selbergPseudoAt (r / r.gcd d) n := by
  unfold selbergPseudoAt
  rw [gcd_squarefree_mul_split hr hd]
  exact selbergPseudoArithmetic_multiplicative.map_mul_of_coprime
    (gcd_factors_coprime hr hd)

/-! ## The finite Euler factor in (2.1) -/

/-- The local correction coefficients are the Dirichlet convolution
`mu * f`; at a prime this is exactly `f(p)-1`. -/
def selbergPseudoDifference : ArithmeticFunction ℂ :=
  (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
    selbergPseudoArithmetic

theorem selbergPseudoDifference_multiplicative :
    selbergPseudoDifference.IsMultiplicative := by
  exact isMultiplicative_moebius.intCast.mul
    selbergPseudoArithmetic_multiplicative

theorem selbergPseudoDifference_apply_prime
    {p : ℕ} (hp : p.Prime) :
    selbergPseudoDifference p = selbergPseudoCoeff p - 1 := by
  unfold selbergPseudoDifference
  rw [ArithmeticFunction.mul_apply]
  have hsum := Nat.sum_divisorsAntidiagonal
    (fun a b => (ArithmeticFunction.moebius : ArithmeticFunction ℂ) a *
      selbergPseudoArithmetic b) (n := p)
  rw [hsum, hp.divisors]
  have hnot : 1 ∉ ({p} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    exact fun h => hp.ne_one h.symm
  rw [Finset.sum_insert hnot,
    Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos]
  simp [selbergPseudoArithmetic, selbergPseudoCoeff,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- The completely multiplicative Dirichlet weight times the correction
coefficient, regarded as one arithmetic function. -/
def weightedSelbergPseudoDifference {q : ℕ}
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 0) :
    ArithmeticFunction ℂ where
  toFun n := selbergPseudoDifference n * dirichletSummandHom chi hs n
  map_zero' := by simp [selbergPseudoDifference]

@[simp] theorem weightedSelbergPseudoDifference_apply
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 0)
    (n : ℕ) :
    weightedSelbergPseudoDifference chi hs n =
      selbergPseudoDifference n * chi n * jutilaNatPower n s := by
  simp [weightedSelbergPseudoDifference, dirichletSummandHom,
    jutilaNatPower]
  ring

theorem weightedSelbergPseudoDifference_multiplicative
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 0) :
    (weightedSelbergPseudoDifference chi hs).IsMultiplicative := by
  constructor
  · simp [weightedSelbergPseudoDifference,
      selbergPseudoDifference_multiplicative]
  · intro m n hcop
    change selbergPseudoDifference (m * n) *
        dirichletSummandHom chi hs (m * n) =
      (selbergPseudoDifference m * dirichletSummandHom chi hs m) *
        (selbergPseudoDifference n * dirichletSummandHom chi hs n)
    rw [selbergPseudoDifference_multiplicative.map_mul_of_coprime hcop]
    rw [map_mul]
    ring

/-- Exact finite Euler expansion of the product in (2.1). -/
theorem jutilaLocalEulerProductComplex_eq_divisorSum
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t : ℕ} (ht : Squarefree t) {s : ℂ} (hs : s ≠ 0) :
    (∏ p ∈ t.primeFactors,
        (1 + (selbergPseudoCoeff p - 1) * chi p *
          jutilaNatPower p s)) =
      ∑ k ∈ t.divisors,
        selbergPseudoDifference k * chi k * jutilaNatPower k s := by
  have hsum :
      (∑ k ∈ t.divisors,
        selbergPseudoDifference k * chi k * jutilaNatPower k s) =
      ∑ k ∈ t.divisors, weightedSelbergPseudoDifference chi hs k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [weightedSelbergPseudoDifference_apply]
  rw [hsum]
  have hprod :=
    IsMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (weightedSelbergPseudoDifference_multiplicative chi hs) ht
  rw [← hprod]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [weightedSelbergPseudoDifference_apply,
    selbergPseudoDifference_apply_prime hpPrime]

end

end MAPJutilaLemma1CoefficientAlgebra

#print axioms MAPJutilaLemma1CoefficientAlgebra.gcd_squarefree_mul_split
#print axioms MAPJutilaLemma1CoefficientAlgebra.selbergPseudoAt_mul_split
#print axioms MAPJutilaLemma1CoefficientAlgebra.jutilaLocalEulerProductComplex_eq_divisorSum
