import JutilaP53ShiftedContourBound
import JutilaLemma3AbsoluteMass

/-!
# Absolute Euler mass of the actual Jutila p.53 divisor kernel

This file connects the correction kernel occurring in the shifted contour
identity to the finite Euler product certified in `JutilaLemma3AbsoluteMass`.
-/

namespace MAPJutilaP53DivisorKernelAbsoluteMass

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction
open MAPJutilaPseudocharacterAlgebra
open MAPJutilaP53Lemma2Bridge
open MAPJutilaP53DivisorKernelMultiplicative
open MAPJutilaLemma3AbsoluteMass
open MAPJutilaP53LeftLineEstimate
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53ShiftedContourBound

noncomputable section

/-- The pointwise absolute value of the actual correction coefficient. -/
def p53PairDivisorKernelNorm (r r' : ℕ) : ArithmeticFunction ℝ where
  toFun n := ‖p53PairDivisorKernel r r' n‖
  map_zero' := by simp [p53PairDivisorKernel]

theorem p53PairDivisorKernelNorm_multiplicative (r r' : ℕ) :
    (p53PairDivisorKernelNorm r r').IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  constructor
  · simp [p53PairDivisorKernelNorm,
      (p53PairDivisorKernel_multiplicative r r').map_one]
  · intro m n hm hn hcop
    change ‖p53PairDivisorKernel r r' (m * n)‖ =
      ‖p53PairDivisorKernel r r' m‖ * ‖p53PairDivisorKernel r r' n‖
    rw [(p53PairDivisorKernel_multiplicative r r').map_mul_of_coprime hcop,
      norm_mul]

theorem squarefree_lcm {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    Squarefree (r.lcm r') := by
  have hr0 := Squarefree.ne_zero hr
  have hr0' := Squarefree.ne_zero hr'
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_ne_zero hr0 hr0')]
  rw [Nat.factorization_lcm hr0 hr0']
  intro p
  rw [Finsupp.sup_apply]
  exact max_le
    ((Nat.squarefree_iff_factorization_le_one hr0).mp hr p)
    ((Nat.squarefree_iff_factorization_le_one hr0').mp hr' p)

theorem primeFactors_lcm {r r' : ℕ} (hr0 : r ≠ 0) (hr0' : r' ≠ 0) :
    (r.lcm r').primeFactors = r.primeFactors ∪ r'.primeFactors := by
  ext p
  by_cases hp : p.Prime
  · simp [Nat.mem_primeFactors, hp, hr0, hr0',
      Nat.lcm_ne_zero hr0 hr0', hp.dvd_lcm]
  · simp [Nat.mem_primeFactors, hp]

theorem one_add_norm_kernel_of_exclusive
    {r r' p : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hp : p.Prime)
    (hex : p ∈ exclusivePrimes r.primeFactors r'.primeFactors) :
    1 + ‖p53PairDivisorKernel r r' p‖ = (p + 1 : ℕ) := by
  have hr0 := Squarefree.ne_zero hr
  have hr0' := Squarefree.ne_zero hr'
  have hx : (p ∣ r ∧ ¬ p ∣ r') ∨ (p ∣ r' ∧ ¬ p ∣ r) := by
    simpa [exclusivePrimes, Nat.mem_primeFactors, hp, hr0, hr0'] using hex
  rw [p53PairDivisorKernel_prime_local hr hr' hp]
  rcases hx with hx | hx
  · simp [hx.1, hx.2, add_comm]
  · simp [hx.1, hx.2, add_comm]

theorem one_add_norm_kernel_of_common
    {r r' p : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hp : p.Prime) (hrp : p ∣ r) (hrp' : p ∣ r') :
    1 + ‖p53PairDivisorKernel r r' p‖ =
      (1 + p * (p - 2) : ℕ) := by
  rw [p53PairDivisorKernel_prime_local hr hr' hp]
  simp only [if_pos hrp, if_pos hrp', norm_mul, Complex.norm_natCast]
  rw [show ((p : ℂ) - 2) = ((p - 2 : ℕ) : ℂ) by
    rw [Nat.cast_sub hp.two_le]; norm_num, Complex.norm_natCast]
  norm_num

theorem primeFactors_union_decomposition (A B : Finset ℕ) :
    A ∪ B = exclusivePrimes A B ∪ (A ∩ B) := by
  ext p
  simp [exclusivePrimes]
  tauto

theorem disjoint_exclusive_inter (A B : Finset ℕ) :
    Disjoint (exclusivePrimes A B) (A ∩ B) := by
  apply Finset.disjoint_left.2
  intro p hpEx hpI
  simp [exclusivePrimes] at hpEx hpI
  tauto

/-- Exact absolute Euler mass of the actual p.53 correction kernel. -/
theorem sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ d ∈ (r.lcm r').divisors, ‖p53PairDivisorKernel r r' d‖ =
      (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  have hlcm := squarefree_lcm hr hr'
  have heuler :=
    (p53PairDivisorKernelNorm_multiplicative r r').prodPrimeFactors_one_add_of_squarefree
      hlcm
  change ∑ d ∈ (r.lcm r').divisors,
      p53PairDivisorKernelNorm r r' d = _
  rw [← heuler]
  rw [primeFactors_lcm (Squarefree.ne_zero hr) (Squarefree.ne_zero hr'),
    primeFactors_union_decomposition,
    Finset.prod_union (disjoint_exclusive_inter r.primeFactors r'.primeFactors)]
  unfold lemmaThreeAbsoluteMass
  push_cast
  congr 1
  · apply Finset.prod_congr rfl
    intro p hpEx
    have hpU : p ∈ r.primeFactors ∪ r'.primeFactors := by
      rw [primeFactors_union_decomposition]
      exact Finset.mem_union_left _ hpEx
    rw [Finset.mem_union] at hpU
    have hp : p.Prime := hpU.elim Nat.prime_of_mem_primeFactors
      Nat.prime_of_mem_primeFactors
    simpa [p53PairDivisorKernelNorm, Nat.cast_add, Nat.cast_one] using
      one_add_norm_kernel_of_exclusive hr hr' hp hpEx
  · apply Finset.prod_congr rfl
    intro p hpI
    have hpR : p ∈ r.primeFactors := (Finset.mem_inter.mp hpI).1
    have hpR' : p ∈ r'.primeFactors := (Finset.mem_inter.mp hpI).2
    have hp := Nat.prime_of_mem_primeFactors hpR
    simpa [p53PairDivisorKernelNorm, Nat.cast_add, Nat.cast_mul,
      Nat.cast_sub hp.two_le] using
      one_add_norm_kernel_of_common hr hr' hp
        (Nat.dvd_of_mem_primeFactors hpR)
        (Nat.dvd_of_mem_primeFactors hpR')

/-- Lemma 3, now attached to the actual divisor kernel used on p.53. -/
theorem sum_norm_p53PairDivisorKernel_le_prime_products
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    ∑ d ∈ (r.lcm r').divisors, ‖p53PairDivisorKernel r r' d‖ ≤
      ((∏ p ∈ r.primeFactors, (p + 1)) *
        ∏ p ∈ r'.primeFactors, (p + 1) : ℕ) := by
  rw [sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass hr hr']
  exact_mod_cast lemmaThreeAbsoluteMass_le r.primeFactors r'.primeFactors
    (fun p hp => by
      rw [Finset.mem_union] at hp
      exact hp.elim
        (fun h => (Nat.prime_of_mem_primeFactors h).two_le)
        (fun h => (Nat.prime_of_mem_primeFactors h).two_le))

theorem p53CpowEndpointBound_div_le_rpow_mul
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    {d : ℕ} (hd : 0 < d) {sigma : ℝ} (hsigma : 0 ≤ sigma) :
    p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
        (-(1 / 2)) (-(1 / 2)) ≤
      (d : ℝ) ^ (1 + sigma) *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hpow : (d : ℝ) ^ (1 / 2 : ℝ) ≤ (d : ℝ) ^ (1 + sigma) :=
    Real.rpow_le_rpow_of_exponent_le hdOne (by linarith)
  unfold p53CpowEndpointBound
  simp only [max_self]
  rw [Real.div_rpow hN.le hdR.le, Real.div_rpow hM.le hdR.le,
    Real.rpow_neg hdR.le, div_inv_eq_mul, div_inv_eq_mul]
  nlinarith [Real.rpow_nonneg hN.le (-(1 / 2 : ℝ)),
    Real.rpow_nonneg hM.le (-(1 / 2 : ℝ))]

theorem norm_twisted_kernel_term_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) {r r' d : ℕ}
    (hd : 0 < d) {s : ℂ} :
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ ≤
      ‖p53PairDivisorKernel r r' d‖ / (d : ℝ) ^ (1 + s).re := by
  have hden0 : 0 ≤ (d : ℝ) ^ (1 + s).re := Real.rpow_nonneg (by positivity) _
  rw [LSeries.norm_term_eq, if_neg hd.ne']
  unfold p53TwistedDivisorKernel
  rw [norm_mul]
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (norm_nonneg _)
      (DirichletCharacter.norm_le_one chi d)) hden0

theorem twisted_term_mul_endpoint_le_kernel
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    {r r' d : ℕ} (hd : 0 < d) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ *
        p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
          (-(1 / 2)) (-(1 / 2)) ≤
      ‖p53PairDivisorKernel r r' d‖ *
        p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) := by
  let D : ℝ := (d : ℝ) ^ (1 + s).re
  let E : ℝ := p53CpowEndpointBound (N / (d : ℝ)) (M / (d : ℝ))
    (-(1 / 2)) (-(1 / 2))
  let E0 : ℝ := p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2))
  have hD : 0 < D := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hd) _
  have hE : 0 ≤ E := p53CpowEndpointBound_nonneg
    (div_pos hN (Nat.cast_pos.mpr hd)) (div_pos hM (Nat.cast_pos.mpr hd)) _ _
  have hscale : E ≤ D * E0 := by
    simpa [D, E, E0] using
      p53CpowEndpointBound_div_le_rpow_mul hM hN hd hs
  calc
    _ ≤ (‖p53PairDivisorKernel r r' d‖ / D) * E := by
      apply mul_le_mul_of_nonneg_right _ hE
      simpa [D] using norm_twisted_kernel_term_le chi hd
    _ ≤ ‖p53PairDivisorKernel r r' d‖ * E0 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hD]
      calc
        ‖p53PairDivisorKernel r r' d‖ * E ≤
            ‖p53PairDivisorKernel r r' d‖ * (D * E0) :=
          mul_le_mul_of_nonneg_left hscale (norm_nonneg _)
        _ = (‖p53PairDivisorKernel r r' d‖ * E0) * D := by ring

/-- The abstract shifted-contour divisor mass is bounded by the exact Lemma-3
Euler mass, with no loss in the arithmetic variables. -/
theorem p53ShiftedDivisorMass_le_lemmaThreeAbsoluteMass
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    {s : ℂ} (hs : 0 ≤ s.re)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    p53ShiftedDivisorMass chi s M N r r' ≤
      p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) := by
  unfold p53ShiftedDivisorMass
  calc
    _ ≤ ∑ d ∈ (r.lcm r').divisors,
        ‖p53PairDivisorKernel r r' d‖ *
          p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) := by
      apply Finset.sum_le_sum
      intro d hd
      exact twisted_term_mul_endpoint_le_kernel chi hM hN
        (Nat.pos_of_mem_divisors hd) hs
    _ = p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
        ∑ d ∈ (r.lcm r').divisors,
          ‖p53PairDivisorKernel r r' d‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by
      rw [sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass hr hr']

/-- The fully expanded source bound using the two elementary prime products
from Jutila's Lemma 3. -/
theorem p53ShiftedDivisorMass_le_prime_products
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hN : 0 < N)
    {s : ℂ} (hs : 0 ≤ s.re)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    p53ShiftedDivisorMass chi s M N r r' ≤
      p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
        (((∏ p ∈ r.primeFactors, (p + 1)) *
          ∏ p ∈ r'.primeFactors, (p + 1) : ℕ) : ℝ) := by
  calc
    _ ≤ p53CpowEndpointBound N M (-(1 / 2)) (-(1 / 2)) *
        (lemmaThreeAbsoluteMass r.primeFactors r'.primeFactors : ℝ) :=
      p53ShiftedDivisorMass_le_lemmaThreeAbsoluteMass chi hM hN hs hr hr'
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
        (p53CpowEndpointBound_nonneg hN hM _ _)
      exact_mod_cast lemmaThreeAbsoluteMass_le r.primeFactors r'.primeFactors
        (fun p hp => by
          rw [Finset.mem_union] at hp
          exact hp.elim
            (fun h => (Nat.prime_of_mem_primeFactors h).two_le)
            (fun h => (Nat.prime_of_mem_primeFactors h).two_le))

end

end MAPJutilaP53DivisorKernelAbsoluteMass

#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.p53PairDivisorKernelNorm_multiplicative
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.squarefree_lcm
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.primeFactors_lcm
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.sum_norm_p53PairDivisorKernel_eq_lemmaThreeAbsoluteMass
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.sum_norm_p53PairDivisorKernel_le_prime_products
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.p53CpowEndpointBound_div_le_rpow_mul
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.norm_twisted_kernel_term_le
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.twisted_term_mul_endpoint_le_kernel
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.p53ShiftedDivisorMass_le_lemmaThreeAbsoluteMass
#print axioms MAPJutilaP53DivisorKernelAbsoluteMass.p53ShiftedDivisorMass_le_prime_products
