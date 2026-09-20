import JutilaP53PairRExpansion
import JutilaPseudocharacterAlgebra

/-!
# Jutila Lemma 2 inserted into the p.53 pair component

This file performs the exact divisor inversion used on p.52.  The zero value
is isolated only to satisfy Mathlib's `ArithmeticFunction` convention;
Dirichlet-series indices are positive, so the resulting identity is literal
on every term used by p.53.
-/

namespace MAPJutilaP53Lemma2Bridge

open scoped BigOperators
open MAPJutilaPseudocharacterAlgebra
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterSquareExpansion
open MAPJutilaP53PairRExpansion

noncomputable section

def p53PairPseudoArithmetic (r r' : ℕ) : ArithmeticFunction ℂ where
  toFun n := if n = 0 then 0 else
    jutilaP53SelbergPseudoAt r n * jutilaP53SelbergPseudoAt r' n
  map_zero' := by simp

def p53PairDivisorKernel (r r' : ℕ) : ArithmeticFunction ℂ :=
  divisorKernel (p53PairPseudoArithmetic r r')

/-- Exact source identity `psi_r(n) psi_r'(n) = sum_{d|n} h(d;r,r')`. -/
theorem sum_p53PairDivisorKernel
    (r r' : ℕ) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, p53PairDivisorKernel r r' d =
      jutilaP53SelbergPseudoAt r n * jutilaP53SelbergPseudoAt r' n := by
  rw [show p53PairDivisorKernel r r' =
      divisorKernel (p53PairPseudoArithmetic r r') by rfl]
  rw [sum_divisorKernel]
  simp [p53PairPseudoArithmetic, Nat.ne_of_gt hn]

/-- The normalizing factor `(rr')^-1` in Jutila's displayed `B(s,chi)` is
recovered exactly from the two normalized pseudocharacters. -/
theorem normalized_pair_eq_divisorSum
    {r r' n : ℕ} (hr : 0 < r) (hr' : 0 < r') (hn : 0 < n) :
    normalizedP53PseudoAt r n * normalizedP53PseudoAt r' n =
      ((r * r' : ℕ) : ℂ)⁻¹ *
        ∑ d ∈ n.divisors, p53PairDivisorKernel r r' d := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hr'C : (r' : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr')
  rw [sum_p53PairDivisorKernel r r' hn]
  unfold normalizedP53PseudoAt
  push_cast
  field_simp

/-- Lemma 2 substituted into one literal p.53 Dirichlet-series term. -/
theorem pairRTerm_eq_divisorExpanded
    {q : ℕ} {M N : ℝ} {s : ℂ} {chi : DirichletCharacter ℂ q}
    {r r' n : ℕ} (hr : 0 < r) (hr' : 0 < r') (hn : 0 < n) :
    jutilaP53PairRTerm M N s chi r r' n =
      ((r * r' : ℕ) : ℂ)⁻¹ *
        (∑ d ∈ n.divisors, p53PairDivisorKernel r r' d) *
        ((n : ℝ)⁻¹ : ℂ) *
        ((Real.exp (-((n : ℝ) / N)) -
          Real.exp (-((n : ℝ) / M))) : ℂ) *
        chi n * (n : ℂ) ^ (-s) := by
  unfold jutilaP53PairRTerm
  calc
    ((n : ℝ)⁻¹ : ℂ) * normalizedP53PseudoAt r n *
          normalizedP53PseudoAt r' n *
          ((Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M))) : ℂ) *
          chi n * (n : ℂ) ^ (-s) =
        (normalizedP53PseudoAt r n * normalizedP53PseudoAt r' n) *
          ((n : ℝ)⁻¹ : ℂ) *
          ((Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M))) : ℂ) *
          chi n * (n : ℂ) ^ (-s) := by ring
    _ = _ := by rw [normalized_pair_eq_divisorSum hr hr' hn]

end

end MAPJutilaP53Lemma2Bridge

#print axioms MAPJutilaP53Lemma2Bridge.sum_p53PairDivisorKernel
#print axioms MAPJutilaP53Lemma2Bridge.normalized_pair_eq_divisorSum
#print axioms MAPJutilaP53Lemma2Bridge.pairRTerm_eq_divisorExpanded
