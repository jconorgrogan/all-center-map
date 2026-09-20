import JutilaLemma6SelectedRightLine
import JutilaLemma6DirectTail

/-!
# Arithmetic coefficient bridge for Jutila Lemma 6

This module identifies the selected coefficient sequence furnished by (2.2)
with the divisor coefficient times the literal primed pseudocharacter sum.
It is the deterministic bridge from the right-line L-series to the direct
series used in (2.11).
-/

namespace MAPJutilaLemma6SieveCoefficientBridge

open scoped BigOperators
open Complex
open MAPJutilaLemma1OuterSum
open MAPJutilaLemma6DirectTail
open MAPJutilaGappedGrahamBypass
open MAPJutilaPseudocharacterMExact

noncomputable section

def jutilaLambdaSupport (z2 : ℝ) : Finset ℕ :=
  Finset.Icc 1 (Nat.floor z2)

def jutilaLambdaComplex (z1 z2 : ℝ) (d : ℕ) : ℂ :=
  (jutilaLambda z1 z2 d : ℂ)

theorem jutilaLambda_eq_zero_of_floor_lt
    {z1 z2 : ℝ} (hz2 : 0 ≤ z2) (hz12 : z1 < z2)
    {d : ℕ} (hd : Nat.floor z2 < d) :
    jutilaLambda z1 z2 d = 0 := by
  have hz2d : z2 < (d : ℝ) := (Nat.floor_lt hz2).mp hd
  have hz1d : ¬ (d : ℝ) < z1 := not_lt.mpr (hz12.trans hz2d).le
  have hdz2 : ¬ (d : ℝ) ≤ z2 := not_le.mpr hz2d
  simp [jutilaLambda, hz1d, hdz2]

/-- The explicit finite support `1 ≤ d ≤ floor z2` realizes the divisor
coefficient in Jutila (2.9), with no implicit infinite-support convention. -/
theorem jutilaOuterDivisorCoeff_lambdaSupport_eq
    {z1 z2 : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    {n : ℕ} (hn : 0 < n) :
    jutilaOuterDivisorCoeff (jutilaLambdaComplex z1 z2)
        (jutilaLambdaSupport z2) n =
      (jutilaDivisorCoefficient z1 z2 n : ℂ) := by
  have hz2 : 0 ≤ z2 := by linarith
  let D := jutilaLambdaSupport z2
  have hset : D.filter (fun d => d ∣ n) =
      n.divisors.filter (fun d => d ≤ Nat.floor z2) := by
    ext d
    simp only [D, jutilaLambdaSupport, Finset.mem_filter,
      Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, hdn⟩
      exact ⟨⟨hdn, hn.ne'⟩, hd2⟩
    · rintro ⟨⟨hdn, hn0⟩, hd2⟩
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
      exact ⟨⟨hdpos, hd2⟩, hdn⟩
  have hfiltered :
      (∑ d ∈ n.divisors.filter (fun d => d ≤ Nat.floor z2),
          (jutilaLambda z1 z2 d : ℂ)) =
        ∑ d ∈ n.divisors, (jutilaLambda z1 z2 d : ℂ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hddiv hdnot
    have hnotle : ¬ d ≤ Nat.floor z2 := by
      intro hle
      exact hdnot (Finset.mem_filter.mpr ⟨hddiv, hle⟩)
    rw [jutilaLambda_eq_zero_of_floor_lt hz2 hz12 (Nat.lt_of_not_ge hnotle)]
    rfl
  unfold jutilaOuterDivisorCoeff
  rw [← Finset.sum_filter]
  change (∑ d ∈ D.filter (fun d => d ∣ n),
      (jutilaLambda z1 z2 d : ℂ)) = _
  rw [hset, hfiltered]
  unfold jutilaDivisorCoefficient
  push_cast
  rfl

theorem jutilaEquation22SelectedCoeff_eq
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) (n : ℕ) :
    jutilaEquation22SelectedCoeff chi xi D S n =
      jutilaOuterDivisorCoeff xi D n * chi n *
        jutilaWeightedPseudocharacter S n := by
  unfold jutilaEquation22SelectedCoeff jutilaEquation22Coeff
    jutilaWeightedPseudocharacter
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    ∑ r ∈ S, (r : ℂ)⁻¹ *
        (jutilaOuterDivisorCoeff xi D n * chi n * selbergPseudoAt r n) =
      ∑ r ∈ S, (jutilaOuterDivisorCoeff xi D n * chi n) *
        ((r : ℂ)⁻¹ * selbergPseudoAt r n) := by
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (jutilaOuterDivisorCoeff xi D n * chi n) *
        ∑ r ∈ S, ((r : ℂ)⁻¹ * selbergPseudoAt r n) := by
      rw [Finset.mul_sum]
    _ = _ := by ring

/-- Once the finite sieve support realizes Jutila's divisor coefficient, an
individual positive-index L-series term is exactly the direct-series term. -/
theorem selected_LSeries_term_eq_directTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q) (xi : ℕ → ℂ)
    (D S : Finset ℕ) {z1 z2 X : ℝ} (rho : ℂ) {n : ℕ}
    (hn : 0 < n)
    (houter : jutilaOuterDivisorCoeff xi D n =
      (jutilaDivisorCoefficient z1 z2 n : ℂ)) :
    LSeries.term (jutilaEquation22SelectedCoeff chi xi D S) rho n *
        (Real.exp (-((n : ℝ) / X)) : ℂ) =
      jutilaLemmaSixDirectTerm chi z1 z2 S rho X n := by
  rw [LSeries.term_of_ne_zero hn.ne']
  rw [jutilaEquation22SelectedCoeff_eq, houter]
  unfold jutilaLemmaSixDirectTerm
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  ring

/-- Premise-free term identification for the literal finite sieve support. -/
theorem selected_lambda_LSeries_term_eq_directTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset ℕ) {z1 z2 X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2)
    (rho : ℂ) {n : ℕ} (hn : 0 < n) :
    LSeries.term
        (jutilaEquation22SelectedCoeff chi
          (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2) S)
        rho n * (Real.exp (-((n : ℝ) / X)) : ℂ) =
      jutilaLemmaSixDirectTerm chi z1 z2 S rho X n := by
  exact selected_LSeries_term_eq_directTerm chi
    (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2) S rho hn
      (jutilaOuterDivisorCoeff_lambdaSupport_eq hz1 hz12 hn)

theorem selected_lambda_smoothedSeries_eq_directSeries
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    (S : Finset ℕ) {z1 z2 X : ℝ}
    (hz1 : 1 < z1) (hz12 : z1 < z2) (rho : ℂ) :
    (∑' n : ℕ,
      LSeries.term
          (jutilaEquation22SelectedCoeff chi
            (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2) S)
          rho n * (Real.exp (-((n : ℝ) / X)) : ℂ)) =
      ∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S rho X n := by
  apply tsum_congr
  intro n
  rcases n with _ | n
  · simp [LSeries.term_zero, jutilaLemmaSixDirectTerm,
      jutilaDivisorCoefficient]
  · exact selected_lambda_LSeries_term_eq_directTerm
      chi S hz1 hz12 rho (Nat.succ_pos n)

/-- Exact source starting-line identity with the literal finite sieve support
and an explicit selected squarefree/coprime `r`-system. -/
theorem jutilaSelectedDirectSeries_eq_gamma_rightLine
    {q R : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) {S : Finset ℕ}
    (hS : S ⊆ Finset.Icc 1 R)
    (hrsq : ∀ r ∈ S, Squarefree r)
    (hrcop : ∀ r ∈ S, r.Coprime q)
    {z1 z2 c X : ℝ} (hz1 : 1 < z1) (hz12 : z1 < z2)
    (hc : 0 < c) (hX : 0 < X)
    (rho : ℂ) (hright : 1 < (rho + (c : ℂ)).re) :
    (∑' n : ℕ, jutilaLemmaSixDirectTerm chi z1 z2 S rho X n) =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ v : ℝ,
          DirichletCharacter.LFunction chi
              (rho + ((c : ℂ) + v * I)) *
            MAPJutilaMEntire.jutilaMWeightedSumComplex chi
              (jutilaLambdaComplex z1 z2) (jutilaLambdaSupport z2) S
              (rho + ((c : ℂ) + v * I)) *
            Complex.Gamma ((c : ℂ) + v * I) *
            (X : ℂ) ^ ((c : ℂ) + v * I)) := by
  have hDpos : ∀ d ∈ jutilaLambdaSupport z2, d ≠ 0 := by
    intro d hd
    have hdI := Finset.mem_Icc.mp hd
    omega
  rw [← selected_lambda_smoothedSeries_eq_directSeries
    chi S hz1 hz12 rho]
  exact MAPJutilaLemma6SelectedRightLine.jutilaSelectedSmoothedSeries_eq_gamma_rightLine
    chi (jutilaLambdaComplex z1 z2) hDpos hS hrsq hrcop hc hX rho hright

end

end MAPJutilaLemma6SieveCoefficientBridge

#print axioms MAPJutilaLemma6SieveCoefficientBridge.jutilaEquation22SelectedCoeff_eq
#print axioms MAPJutilaLemma6SieveCoefficientBridge.selected_LSeries_term_eq_directTerm
#print axioms MAPJutilaLemma6SieveCoefficientBridge.selected_lambda_LSeries_term_eq_directTerm
#print axioms MAPJutilaLemma6SieveCoefficientBridge.jutilaSelectedDirectSeries_eq_gamma_rightLine
