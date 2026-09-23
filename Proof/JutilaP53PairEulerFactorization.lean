import JutilaP53PairRightLine

/-!
# L-function factorization of one p.53 pseudocharacter pair

Lemma 2 says that the product of the two pseudocharacters is the divisor
sum of `h(d;r,r')`.  Character multiplicativity therefore factors its
Dirichlet series into one Dirichlet L-function and the twisted `h` series.
This file proves that identity, including all absolute-convergence claims
on `Re s > 1`.
-/

namespace MAPJutilaP53PairEulerFactorization

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
  LSeries.notation
open ArithmeticFunction
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PseudocharacterSquareExpansion
open MAPJutilaP53Lemma2Bridge
open MAPJutilaP53PairRightLine

noncomputable section

def p53TwistedDivisorKernel {q : ℕ}
    (chi : DirichletCharacter ℂ q) (r r' n : ℕ) : ℂ :=
  chi n * p53PairDivisorKernel r r' n

theorem norm_p53PairPseudoArithmetic_le
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') (n : ℕ) :
    ‖p53PairPseudoArithmetic r r' n‖ ≤ (r * r' : ℕ) := by
  by_cases hn0 : n = 0
  · subst n
    change ‖(0 : ℂ)‖ ≤ (r * r' : ℕ)
    simp only [norm_zero]
    positivity
  have ha := norm_jutilaP53SelbergPseudoAt_le r n
  have hb := norm_jutilaP53SelbergPseudoAt_le r' n
  have hphiA : (Nat.totient (r.gcd n) : ℝ) ≤ r := by
    exact_mod_cast (Nat.totient_le _).trans
      (Nat.gcd_le_left n hr)
  have hphiB : (Nat.totient (r'.gcd n) : ℝ) ≤ r' := by
    exact_mod_cast (Nat.totient_le _).trans
      (Nat.gcd_le_left n hr')
  change ‖if n = 0 then 0 else
      jutilaP53SelbergPseudoAt r n *
        jutilaP53SelbergPseudoAt r' n‖ ≤ _
  rw [if_neg hn0, norm_mul]
  calc
    ‖jutilaP53SelbergPseudoAt r n‖ *
        ‖jutilaP53SelbergPseudoAt r' n‖ ≤
      (Nat.totient (r.gcd n) : ℝ) *
        (Nat.totient (r'.gcd n) : ℝ) :=
      mul_le_mul ha hb (norm_nonneg _)
        (Nat.cast_nonneg _)
    _ ≤ (r : ℝ) * (r' : ℝ) :=
      mul_le_mul hphiA hphiB (Nat.cast_nonneg _) (by positivity)
    _ = (r * r' : ℕ) := by push_cast; ring

theorem LSeriesSummable_p53PairPseudoArithmetic
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (p53PairPseudoArithmetic r r') s :=
  LSeriesSummable_of_bounded_of_one_lt_re
    (m := (r * r' : ℕ))
    (fun n _ => norm_p53PairPseudoArithmetic_le hr hr' n) hs

theorem LSeriesSummable_p53PairDivisorKernel
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (p53PairDivisorKernel r r') s := by
  have hmu : LSeriesSummable
      ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) : ℕ → ℂ) s :=
    LSeriesSummable_of_bounded_of_one_lt_re
      (m := 1) (fun n _ => by
        norm_num
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := n)) hs
  have hF := LSeriesSummable_p53PairPseudoArithmetic hr hr' hs
  have hconv := hmu.convolution hF
  simpa [p53PairDivisorKernel, MAPJutilaPseudocharacterAlgebra.divisorKernel,
    ArithmeticFunction.coe_mul] using hconv

theorem LSeriesSummable_p53TwistedDivisorKernel
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (p53TwistedDivisorKernel chi r r') s := by
  simpa [p53TwistedDivisorKernel, Pi.mul_def] using!
    DirichletCharacter.LSeriesSummable_mul chi
      (LSeriesSummable_p53PairDivisorKernel hr hr' hs)

theorem character_convolution_twistedKernel_eq_pair
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' n : ℕ} (hr : 0 < r) (hr' : 0 < r') (hn : 0 < n) :
    (((chi ·) : ℕ → ℂ) ⍟ p53TwistedDivisorKernel chi r r') n =
      ((r * r' : ℕ) : ℂ) * p53PairCoefficient chi r r' n := by
  have hdist :
      (((chi ·) : ℕ → ℂ) ⍟
          (((chi ·) : ℕ → ℂ) *
            (p53PairDivisorKernel r r' : ℕ → ℂ))) =
        ((chi ·) : ℕ → ℂ) *
          ((1 : ℕ → ℂ) ⍟
            (p53PairDivisorKernel r r' : ℕ → ℂ)) := by
    simpa only [Pi.mul_apply, mul_one] using
      DirichletCharacter.mul_convolution_distrib chi
        (1 : ℕ → ℂ) (p53PairDivisorKernel r r' : ℕ → ℂ)
  rw [show p53TwistedDivisorKernel chi r r' =
      (((chi ·) : ℕ → ℂ) *
        (p53PairDivisorKernel r r' : ℕ → ℂ)) by
    funext k
    simp [p53TwistedDivisorKernel]]
  rw [hdist]
  simp only [Pi.mul_apply]
  rw [LSeries.convolution_def]
  change chi n *
      (∑ p ∈ n.divisorsAntidiagonal,
        (1 : ℂ) * p53PairDivisorKernel r r' p.2) = _
  rw [Nat.sum_divisorsAntidiagonal'
    (fun _a b => (1 : ℂ) * p53PairDivisorKernel r r' b)]
  simp only [one_mul]
  rw [sum_p53PairDivisorKernel r r' hn]
  have hnorm := normalized_pair_eq_divisorSum hr hr' hn
  rw [sum_p53PairDivisorKernel r r' hn] at hnorm
  unfold p53PairCoefficient
  have hrr : (((r * r' : ℕ) : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero hr.ne' hr'.ne')
  field_simp [hrr] at hnorm ⊢
  rw [← hnorm]

/-- Exact source factorization on the absolute-convergence half-plane. -/
theorem LSeries_p53PairCoefficient_factorization
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r')
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (p53PairCoefficient chi r r') s =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        LSeries ((chi ·) : ℕ → ℂ) s *
        LSeries (p53TwistedDivisorKernel chi r r') s := by
  have hchi := DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hH := LSeriesSummable_p53TwistedDivisorKernel chi hr hr' hs
  have hconv := LSeries_convolution' hchi hH
  have hcoeff :
      LSeries (p53PairCoefficient chi r r') s =
        (((r * r' : ℕ) : ℂ)⁻¹) *
          LSeries ((((chi ·) : ℕ → ℂ) ⍟
            p53TwistedDivisorKernel chi r r')) s := by
    unfold LSeries
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp [LSeries.term_zero]
    rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0,
      character_convolution_twistedKernel_eq_pair chi hr hr'
        (Nat.pos_of_ne_zero hn0)]
    have hrr : (((r * r' : ℕ) : ℂ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero hr.ne' hr'.ne')
    field_simp [hrr]
  rw [hcoeff, hconv]
  ring

end

end MAPJutilaP53PairEulerFactorization

#print axioms MAPJutilaP53PairEulerFactorization.LSeries_p53PairCoefficient_factorization
