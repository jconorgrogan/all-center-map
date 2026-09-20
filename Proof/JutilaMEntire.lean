import JutilaPseudocharacterMExact

/-!
# Entire finite continuation of Jutila's `M(s,chi,psi_r)`

The sieve coefficients have finite support.  Consequently the expression in
Jutila (2.1) is an entire finite sum in `s`.  This module defines the literal
complex-variable expression, proves entireness, and identifies its value on
the imaginary axis with the already bounded finite mollifier.
-/

namespace MAPJutilaMEntire

open scoped BigOperators
open Complex
open MAPJutilaPseudocharacterMExact

noncomputable section

def jutilaNatPower (n : ℕ) (s : ℂ) : ℂ :=
  (n : ℂ) ^ (-s)

def jutilaLocalEulerFactorComplex {q : ℕ}
    (chi : DirichletCharacter ℂ q) (p : ℕ) (s : ℂ) : ℂ :=
  1 + (selbergPseudoCoeff p - 1) * chi p * jutilaNatPower p s

def jutilaLocalEulerProductComplex {q : ℕ}
    (chi : DirichletCharacter ℂ q) (r d : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (r / r.gcd d).primeFactors,
    jutilaLocalEulerFactorComplex chi p s

def jutilaMTermComplex {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (r d : ℕ) (s : ℂ) : ℂ :=
  xi d * chi d * selbergPseudoAt r d * jutilaNatPower d s *
    jutilaLocalEulerProductComplex chi r d s

def jutilaMFiniteComplex {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D : Finset ℕ) (r : ℕ) (s : ℂ) : ℂ :=
  ∑ d ∈ D, jutilaMTermComplex chi xi r d s

def jutilaMWeightedSumComplex {q : ℕ}
    (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (s : ℂ) : ℂ :=
  ∑ r ∈ S,
    ((r : ℂ)⁻¹ * jutilaMFiniteComplex chi xi D r s)

theorem jutilaNatPower_mul_I_eq_imaginaryNatPower (n : ℕ) (t : ℝ) :
    jutilaNatPower n ((t : ℂ) * I) = imaginaryNatPower n t := by
  rfl

theorem jutilaLocalEulerProductComplex_mul_I_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (r d : ℕ) (t : ℝ) :
    jutilaLocalEulerProductComplex chi r d ((t : ℂ) * I) =
      jutilaLocalEulerProduct chi r d t := by
  unfold jutilaLocalEulerProductComplex jutilaLocalEulerProduct
    jutilaLocalEulerFactorComplex jutilaLocalEulerFactor
  rfl

theorem jutilaMFiniteComplex_mul_I_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D : Finset ℕ) (r : ℕ) (t : ℝ) :
    jutilaMFiniteComplex chi xi D r ((t : ℂ) * I) =
      jutilaMFinite chi xi D r t := by
  unfold jutilaMFiniteComplex jutilaMFinite
  apply Finset.sum_congr rfl
  intro d hd
  unfold jutilaMTermComplex jutilaMTerm
  rw [jutilaNatPower_mul_I_eq_imaginaryNatPower,
    jutilaLocalEulerProductComplex_mul_I_eq]

private theorem differentiable_jutilaNatPower
    {n : ℕ} (hn : 0 < n) :
    Differentiable ℂ (jutilaNatPower n) := by
  unfold jutilaNatPower
  exact differentiable_neg.const_cpow
    (.inl (by exact_mod_cast hn.ne' : (n : ℂ) ≠ 0))

private theorem differentiable_jutilaLocalEulerFactorComplex
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) :
    Differentiable ℂ (jutilaLocalEulerFactorComplex chi p) := by
  unfold jutilaLocalEulerFactorComplex
  exact (differentiable_const (c := (1 : ℂ))).add
    ((differentiable_const
      (c := (selbergPseudoCoeff p - 1) * chi p)).mul
        (differentiable_jutilaNatPower hp.pos))

private theorem differentiable_jutilaLocalEulerProductComplex
    {q : ℕ} (chi : DirichletCharacter ℂ q) (r d : ℕ) :
    Differentiable ℂ (jutilaLocalEulerProductComplex chi r d) := by
  unfold jutilaLocalEulerProductComplex
  apply Differentiable.fun_finsetProd
  intro p hp
  exact differentiable_jutilaLocalEulerFactorComplex chi
    (Nat.prime_of_mem_primeFactors hp)

private theorem differentiable_jutilaMTermComplex
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (r : ℕ) {d : ℕ} (hd : 0 < d) :
    Differentiable ℂ (jutilaMTermComplex chi xi r d) := by
  unfold jutilaMTermComplex
  have hconst : Differentiable ℂ
      (fun _s : ℂ => xi d * chi d * selbergPseudoAt r d) :=
    by fun_prop
  exact (hconst.mul (differentiable_jutilaNatPower hd)).mul
    (differentiable_jutilaLocalEulerProductComplex chi r d)

theorem differentiable_jutilaMFiniteComplex
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d) (r : ℕ) :
    Differentiable ℂ (jutilaMFiniteComplex chi xi D r) := by
  unfold jutilaMFiniteComplex
  have heq : (fun s : ℂ =>
      ∑ d ∈ D, jutilaMTermComplex chi xi r d s) =
      ∑ d ∈ D, fun s : ℂ => jutilaMTermComplex chi xi r d s := by
    funext s
    simp
  rw [heq]
  apply Differentiable.sum
  intro d hd
  exact differentiable_jutilaMTermComplex chi xi r (hDpos d hd)

theorem differentiable_jutilaMWeightedSumComplex
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    {D : Finset ℕ} (hDpos : ∀ d ∈ D, 0 < d) (S : Finset ℕ) :
    Differentiable ℂ (jutilaMWeightedSumComplex chi xi D S) := by
  unfold jutilaMWeightedSumComplex
  have heq : (fun s : ℂ => ∑ r ∈ S,
      (r : ℂ)⁻¹ * jutilaMFiniteComplex chi xi D r s) =
      ∑ r ∈ S, fun s : ℂ =>
        (r : ℂ)⁻¹ * jutilaMFiniteComplex chi xi D r s := by
    funext s
    simp
  rw [heq]
  apply Differentiable.sum
  intro r hr
  exact ((differentiable_const (c := (r : ℂ)⁻¹)).mul
    (differentiable_jutilaMFiniteComplex chi xi hDpos r))

end

end MAPJutilaMEntire

#print axioms MAPJutilaMEntire.differentiable_jutilaMFiniteComplex
#print axioms MAPJutilaMEntire.differentiable_jutilaMWeightedSumComplex
