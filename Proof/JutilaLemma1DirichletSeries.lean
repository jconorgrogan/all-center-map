import JutilaLemma1CoefficientAlgebra
import MollifierCoefficientIdentity

/-!
# Dirichlet-series weld for Jutila Lemma 1

This module turns the certified finite Euler correction into an actual
finite-support `LSeries` and proves its coefficient action.  It is the outer
absolute-convergence layer of Jutila (2.2).
-/

namespace MAPJutilaLemma1DirichletSeries

open scoped BigOperators LSeries.notation ArithmeticFunction.Moebius
open ArithmeticFunction
open MAPJutilaPseudocharacterMExact
open MAPJutilaMEntire
open MAPJutilaLemma1CoefficientAlgebra

noncomputable section

/-- Untwisted finite correction supported on divisors of squarefree `t`. -/
def jutilaCorrectionCoeff (t n : ℕ) : ℂ :=
  if n ∈ t.divisors then selbergPseudoDifference n else 0

def jutilaCorrectionPolynomial {q : ℕ}
    (chi : DirichletCharacter ℂ q) (t : ℕ) (s : ℂ) : ℂ :=
  LSeries (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t) s

theorem jutilaCorrectionCoeff_support
    {t n : ℕ} (hn : jutilaCorrectionCoeff t n ≠ 0) :
    n ∈ t.divisors := by
  by_contra hmem
  exact hn (by simp [jutilaCorrectionCoeff, hmem])

theorem jutilaCorrectionCoeff_LSeriesSummable
    {t : ℕ} {s : ℂ} :
    LSeriesSummable (jutilaCorrectionCoeff t) s := by
  unfold LSeriesSummable
  apply summable_of_hasFiniteSupport
  rw [Function.HasFiniteSupport]
  exact (Finset.finite_toSet t.divisors).subset (by
    intro n hn
    by_contra hmem
    change n ∉ t.divisors at hmem
    have hcoeff : jutilaCorrectionCoeff t n = 0 := by
      simp [jutilaCorrectionCoeff, hmem]
    exact hn (by simp [LSeries.term, hcoeff]))

theorem twisted_jutilaCorrectionCoeff_LSeriesSummable
    {q : ℕ} (chi : DirichletCharacter ℂ q) {t : ℕ} {s : ℂ} :
    LSeriesSummable (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t) s := by
  exact DirichletCharacter.LSeriesSummable_mul chi
    jutilaCorrectionCoeff_LSeriesSummable

/-- A finite-support L-series is the literal divisor polynomial. -/
theorem jutilaCorrectionPolynomial_eq_divisorSum
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t : ℕ} (ht : t ≠ 0) (s : ℂ) :
    jutilaCorrectionPolynomial chi t s =
      ∑ k ∈ t.divisors,
        selbergPseudoDifference k * chi k * jutilaNatPower k s := by
  unfold jutilaCorrectionPolynomial LSeries
  rw [tsum_eq_sum (s := t.divisors)]
  · apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := ne_zero_of_dvd_ne_zero ht
      (Nat.dvd_of_mem_divisors hk)
    rw [LSeries.term_of_ne_zero hk0]
    simp [jutilaCorrectionCoeff, hk, jutilaNatPower]
    rw [Complex.cpow_neg]
    ring
  · intro k hk
    simp [LSeries.term, jutilaCorrectionCoeff, hk]

/-- The finite `LSeries` is exactly the Euler product in (2.1). -/
theorem jutilaCorrectionPolynomial_eq_localEulerProduct
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t : ℕ} (ht : Squarefree t) {s : ℂ} (hs : s ≠ 0) :
    jutilaCorrectionPolynomial chi t s =
      ∏ p ∈ t.primeFactors,
        (1 + (selbergPseudoCoeff p - 1) * chi p *
          jutilaNatPower p s) := by
  rw [jutilaCorrectionPolynomial_eq_divisorSum chi ht.ne_zero]
  exact (jutilaLocalEulerProductComplex_eq_divisorSum chi ht hs).symm

/-- Intersecting the divisor support with a coefficient index gives the
divisors of the gcd. -/
theorem sum_divisors_jutilaCorrectionCoeff
    {t n : ℕ} (ht : t ≠ 0) (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, jutilaCorrectionCoeff t k) =
      ∑ k ∈ (t.gcd n).divisors, selbergPseudoDifference k := by
  have hset : (t.gcd n).divisors = t.divisors ∩ n.divisors := by
    ext k
    simp only [Nat.mem_divisors, Finset.mem_inter]
    constructor
    · rintro ⟨hk, hgcd0⟩
      have hpair := Nat.dvd_gcd_iff.mp hk
      exact ⟨⟨hpair.1, ht⟩, ⟨hpair.2, hn⟩⟩
    · rintro ⟨⟨hkt, ht0⟩, ⟨hkn, hn0⟩⟩
      exact ⟨Nat.dvd_gcd hkt hkn, Nat.gcd_ne_zero_left ht⟩
  rw [hset]
  simp only [jutilaCorrectionCoeff]
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp [Finset.mem_inter, and_comm]

/-- The correction divisor sum reconstructs `f_t(n)=f((t,n))`. -/
theorem sum_divisors_selbergPseudoDifference_eq_selbergPseudoAt
    {t n : ℕ} (ht : t ≠ 0) (hn : n ≠ 0) :
    (∑ k ∈ n.divisors, jutilaCorrectionCoeff t k) =
      selbergPseudoAt t n := by
  rw [sum_divisors_jutilaCorrectionCoeff ht hn]
  have hconv :
      (ArithmeticFunction.zeta : ArithmeticFunction ℂ) *
          selbergPseudoDifference = selbergPseudoArithmetic := by
    unfold selbergPseudoDifference
    rw [← mul_assoc, ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  rw [← ArithmeticFunction.coe_zeta_mul_apply]
  rw [hconv]
  rfl

/-- Untwisted coefficient identity for the finite Euler correction. -/
theorem one_convolution_jutilaCorrectionCoeff
    {t n : ℕ} (ht : t ≠ 0) (hn : n ≠ 0) :
    ((1 : ℕ → ℂ) ⍟ jutilaCorrectionCoeff t) n =
      selbergPseudoAt t n := by
  rw [LSeries.convolution_def]
  change (∑ p ∈ n.divisorsAntidiagonal,
      (1 : ℕ → ℂ) p.1 * jutilaCorrectionCoeff t p.2) = _
  rw [
    Nat.sum_divisorsAntidiagonal'
      (fun a b => (1 : ℕ → ℂ) a * jutilaCorrectionCoeff t b)]
  simp only [Pi.one_apply, one_mul]
  exact sum_divisors_selbergPseudoDifference_eq_selbergPseudoAt ht hn

/-- Character twisting distributes through the correction convolution. -/
theorem character_convolution_jutilaCorrectionCoeff
    {q t n : ℕ} (chi : DirichletCharacter ℂ q) (ht : t ≠ 0)
    (hn : n ≠ 0) :
    (((chi ·) : ℕ → ℂ) ⍟
        (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t)) n =
      (((chi ·) : ℕ → ℂ) * (selbergPseudoAt t)) n := by
  have hdist :
      ((chi ·) : ℕ → ℂ) ⍟
          (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t) =
        ((chi ·) : ℕ → ℂ) *
          ((1 : ℕ → ℂ) ⍟ jutilaCorrectionCoeff t) := by
    simpa only [Pi.mul_apply, mul_one] using
      DirichletCharacter.mul_convolution_distrib chi
        (1 : ℕ → ℂ) (jutilaCorrectionCoeff t)
  rw [hdist]
  simp only [Pi.mul_apply]
  rw [one_convolution_jutilaCorrectionCoeff ht hn]

/-- The Dirichlet L-series times the finite local correction is exactly the
series with coefficients `chi(n) f_t(n)`. -/
theorem LSeries_mul_jutilaCorrectionPolynomial_eq
    {q t : ℕ} (chi : DirichletCharacter ℂ q)
    (ht : t ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries ((chi ·) : ℕ → ℂ) s *
        jutilaCorrectionPolynomial chi t s =
      LSeries (((chi ·) : ℕ → ℂ) * selbergPseudoAt t) s := by
  have hchi : LSeriesSummable ((chi ·) : ℕ → ℂ) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hcorr : LSeriesSummable
      (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t) s :=
    twisted_jutilaCorrectionCoeff_LSeriesSummable chi
  unfold jutilaCorrectionPolynomial
  rw [← LSeries_convolution' hchi hcorr]
  apply LSeries_congr
  intro n hn
  exact character_convolution_jutilaCorrectionCoeff chi ht hn

theorem LSeriesSummable_chi_mul_selbergPseudoAt
    {q t : ℕ} (chi : DirichletCharacter ℂ q)
    (ht : t ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (((chi ·) : ℕ → ℂ) * selbergPseudoAt t) s := by
  have hchi : LSeriesSummable ((chi ·) : ℕ → ℂ) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs
  have hcorr : LSeriesSummable
      (((chi ·) : ℕ → ℂ) * jutilaCorrectionCoeff t) s :=
    twisted_jutilaCorrectionCoeff_LSeriesSummable chi
  have hconv := hchi.convolution hcorr
  exact (LSeriesSummable_congr s (fun {n} hn =>
    character_convolution_jutilaCorrectionCoeff chi ht hn)).mp hconv

/-- Paper-facing inner Euler identity on `Re s > 1`. -/
theorem LFunction_mul_localEulerProduct_eq
    {q t : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (ht : Squarefree t) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction chi s *
        (∏ p ∈ t.primeFactors,
          (1 + (selbergPseudoCoeff p - 1) * chi p *
            jutilaNatPower p s)) =
      LSeries (((chi ·) : ℕ → ℂ) * selbergPseudoAt t) s := by
  have hs0 : s ≠ 0 := by
    intro hzero
    subst s
    norm_num at hs
  rw [← jutilaCorrectionPolynomial_eq_localEulerProduct chi ht
    hs0]
  rw [DirichletCharacter.LFunction_eq_LSeries chi hs]
  exact LSeries_mul_jutilaCorrectionPolynomial_eq chi ht.ne_zero hs

end

end MAPJutilaLemma1DirichletSeries

#print axioms MAPJutilaLemma1DirichletSeries.jutilaCorrectionPolynomial_eq_localEulerProduct
#print axioms MAPJutilaLemma1DirichletSeries.sum_divisors_selbergPseudoDifference_eq_selbergPseudoAt
#print axioms MAPJutilaLemma1DirichletSeries.LFunction_mul_localEulerProduct_eq
