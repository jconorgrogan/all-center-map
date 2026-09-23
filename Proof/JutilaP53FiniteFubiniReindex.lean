import JutilaP53DivisorKernelMultiplicative
import JutilaP53PairEulerFactorization
import JutilaP53InnerMellinRightLine
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# The finite-support Fubini seam on Jutila p.53

This file rewrites one selected pseudocharacter pair as the literal
divisor-kernel antidiagonal which is subsequently reindexed by `n = d*m`.
The first theorem is the exact termwise identity, before any exchange of an
infinite and a finite sum. Keeping this statement separate makes the source
normalization `(r*r')⁻¹`, the twist on the divisor kernel, and both copies of
`1+s` independently visible.
-/

namespace MAPJutilaP53FiniteFubiniReindex

open scoped BigOperators LSeries.notation
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53PairRExpansion
open MAPJutilaP53PairRightLine
open MAPJutilaP53PairEulerFactorization
open MAPJutilaP53InnerMellinRightLine
open MAPJutilaP53DivisorKernelMultiplicative

noncomputable section

set_option maxHeartbeats 1200000

/-- Abstract positive-index reindexing behind the substitution `n=d*m`.
Absolute summability is stated on factor pairs, where it is easiest to prove
from the finite support of the divisor kernel and exponential smoothing. -/
theorem tsum_pnat_antidiagonal_eq_tsum_prod
    (f : ℕ → ℕ → ℂ)
    (hf : Summable (fun p : ℕ+ × ℕ+ => f p.1 p.2)) :
    ∑' n : ℕ+, ∑ p ∈ (n : ℕ).divisorsAntidiagonal, f p.1 p.2 =
      ∑' p : ℕ+ × ℕ+, f p.1 p.2 := by
  let F : ℕ+ × ℕ+ → ℂ := fun p => f p.1 p.2
  have hsigma : Summable (fun x : Σ n : ℕ+,
      (n : ℕ).divisorsAntidiagonal =>
        F (sigmaAntidiagonalEquivProd x)) :=
    (sigmaAntidiagonalEquivProd.summable_iff).2 hf
  calc
    (∑' n : ℕ+, ∑ p ∈ (n : ℕ).divisorsAntidiagonal, f p.1 p.2) =
        ∑' n : ℕ+, ∑' p : (n : ℕ).divisorsAntidiagonal,
          f p.1.1 p.1.2 := by
      apply tsum_congr
      intro n
      exact (Finset.tsum_subtype' (n : ℕ).divisorsAntidiagonal
        (fun p : ℕ × ℕ => f p.1 p.2)).symm
    _ = ∑' x : Σ n : ℕ+, (n : ℕ).divisorsAntidiagonal,
          F (sigmaAntidiagonalEquivProd x) := by
      rw [hsigma.tsum_sigma]
      rfl
    _ = ∑' p : ℕ+ × ℕ+, F p := sigmaAntidiagonalEquivProd.tsum_eq F
    _ = _ := rfl

/-- On `Re s ≥ 0`, the character factor at `1+s` has norm at most one. -/
theorem norm_character_LSeries_term_one_add_le_one
    {q m : ℕ} (chi : DirichletCharacter ℂ q) (hm : 0 < m)
    {s : ℂ} (hs : 0 ≤ s.re) :
    ‖LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m‖ ≤ 1 := by
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexp : 0 ≤ (1 + s).re := by simp; linarith
  have hden : 1 ≤ (m : ℝ) ^ (1 + s).re :=
    Real.one_le_rpow hmOne hexp
  have hdenPos : 0 < (m : ℝ) ^ (1 + s).re :=
    zero_lt_one.trans_le hden
  rw [LSeries.norm_term_eq, if_neg hm.ne', div_le_one hdenPos]
  exact (DirichletCharacter.norm_le_one chi m).trans hden

/-- The two-scale exponential attached to the product `d*m`. -/
def p53ProductTwoScaleWeight (M N : ℝ) (d m : ℕ) : ℂ :=
  ((Real.exp (-(((d * m : ℕ) : ℝ) / N)) -
    Real.exp (-(((d * m : ℕ) : ℝ) / M))) : ℂ)

theorem norm_p53ProductTwoScaleWeight_le_geometric
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    ‖p53ProductTwoScaleWeight M N d m‖ ≤
      (Real.exp (-(1 / N))) ^ m := by
  have hN : 0 < N := hM.trans hMN
  have hdm : (0 : ℝ) < (d * m : ℕ) := by exact_mod_cast mul_pos hd hm
  have hquot : ((d * m : ℕ) : ℝ) / N < ((d * m : ℕ) : ℝ) / M :=
    (div_lt_div_iff_of_pos_left hdm hN hM).2 hMN
  have hdiff0 : 0 ≤ Real.exp (-(((d * m : ℕ) : ℝ) / N)) -
      Real.exp (-(((d * m : ℕ) : ℝ) / M)) :=
    sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
  have hdiff : Real.exp (-(((d * m : ℕ) : ℝ) / N)) -
      Real.exp (-(((d * m : ℕ) : ℝ) / M)) ≤
        Real.exp (-(((d * m : ℕ) : ℝ) / N)) := by
    linarith [Real.exp_nonneg (-(((d * m : ℕ) : ℝ) / M))]
  have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hscale : -(((d * m : ℕ) : ℝ) / N) ≤ -((m : ℝ) / N) := by
    push_cast
    have hmR : (0 : ℝ) ≤ m := by positivity
    have : (m : ℝ) ≤ (d : ℝ) * m := by nlinarith
    have := (div_le_div_iff_of_pos_right hN).2 this
    linarith
  unfold p53ProductTwoScaleWeight
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hdiff0]
  calc
    Real.exp (-(((d * m : ℕ) : ℝ) / N)) -
          Real.exp (-(((d * m : ℕ) : ℝ) / M)) ≤
        Real.exp (-(((d * m : ℕ) : ℝ) / N)) := hdiff
    _ ≤ Real.exp (-((m : ℝ) / N)) := Real.exp_le_exp.mpr hscale
    _ = (Real.exp (-(1 / N))) ^ m := by
      rw [← Real.exp_nat_mul]
      ring

/-- The factor-pair summand after Lemma 2. -/
def p53FactorPairTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (M N : ℝ) (s : ℂ) (r r' d m : ℕ) : ℂ :=
  LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
    LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
    p53ProductTwoScaleWeight M N d m

theorem summable_p53FactorPairTerm_pnat
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    Summable (fun p : ℕ+ × ℕ+ =>
      p53FactorPairTerm chi M N s r r' p.1 p.2) := by
  let a : ℝ := Real.exp (-(1 / N))
  have hN : 0 < N := hM.trans hMN
  have haPos : 0 < a := by dsimp [a]; positivity
  have haLt : a < 1 := by
    dsimp [a]
    have hneg : -(1 / N) < 0 := by
      have : 0 < 1 / N := one_div_pos.mpr hN
      linarith
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  let A : ℕ+ → ℝ := fun d =>
    ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖
  have hAfin : Function.HasFiniteSupport A := by
    change (Function.support A).Finite
    have hpre : ((fun d : ℕ+ => (d : ℕ)) ⁻¹'
        (↑(r.lcm r').divisors : Set ℕ)).Finite :=
      Set.Finite.preimage (Set.injOn_of_injective PNat.coe_injective)
        (Finset.finite_toSet (r.lcm r').divisors)
    apply hpre.subset
    intro d hdA
    by_contra hdiv
    change (d : ℕ) ∉ (r.lcm r').divisors at hdiv
    have hnd : ¬ (d : ℕ) ∣ r.lcm r' := by
      intro hdvd
      exact hdiv (Nat.mem_divisors.mpr ⟨hdvd,
        Nat.lcm_ne_zero (Squarefree.ne_zero hr) (Squarefree.ne_zero hr')⟩)
    have hkernel : p53TwistedDivisorKernel chi r r' d = 0 := by
      unfold p53TwistedDivisorKernel
      rw [p53PairDivisorKernel_eq_zero_of_not_dvd_lcm' hr hr'
        (PNat.ne_zero d) hnd]
      simp
    have hterm :
        LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d = 0 := by
      rw [LSeries.term_of_ne_zero (PNat.ne_zero d), hkernel]
      simp
    have hA0 : A d = 0 := by
      change ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d‖ = 0
      rw [hterm, norm_zero]
    exact hdA hA0
  have hAsum : Summable A := summable_of_hasFiniteSupport hAfin
  have hgeoNat : Summable (fun m : ℕ => a ^ m) :=
    summable_geometric_of_norm_lt_one
      (show ‖a‖ < 1 by simpa [Real.norm_eq_abs, abs_of_pos haPos] using haLt)
  have hgeo : Summable (fun m : ℕ+ => a ^ (m : ℕ)) :=
    (summable_pnat_iff_summable_nat).2 hgeoNat
  have hAnorm : Summable (fun d : ℕ+ => ‖A d‖) := by
    convert hAsum using 1
    funext d
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact norm_nonneg _
  have hgnorm : Summable (fun m : ℕ+ => ‖a ^ (m : ℕ)‖) := by
    simpa only [Real.norm_eq_abs, abs_of_pos (pow_pos haPos _)] using hgeo
  have hprod : Summable (fun p : ℕ+ × ℕ+ => A p.1 * a ^ (p.2 : ℕ)) :=
    summable_mul_of_summable_norm (f := A)
      (g := fun m : ℕ+ => a ^ (m : ℕ)) hAnorm hgnorm
  apply Summable.of_norm_bounded hprod
  intro p
  unfold p53FactorPairTerm
  simp only [norm_mul]
  calc
    ‖LSeries.term (fun x => chi x) (1 + s) (p.2 : ℕ)‖ *
          ‖LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) (p.1 : ℕ)‖ *
          ‖p53ProductTwoScaleWeight M N (p.1 : ℕ) (p.2 : ℕ)‖ ≤
        1 * A p.1 * a ^ (p.2 : ℕ) := by
      gcongr
      · exact norm_character_LSeries_term_one_add_le_one chi p.2.2 hs
      · exact norm_p53ProductTwoScaleWeight_le_geometric hM hMN p.1.2 p.2.2
    _ = A p.1 * a ^ (p.2 : ℕ) := by ring

theorem p53FactorPairTerm_eq_outer_mul_innerTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    (s : ℂ) (r r' : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m) :
    p53FactorPairTerm chi M N s r r' d m =
      LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
        (LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
          ((Real.exp (-((m : ℝ) / (N / (d : ℝ)))) -
            Real.exp (-((m : ℝ) / (M / (d : ℝ))))) : ℂ)) := by
  have hN : 0 < N := hM.trans hMN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hscaleN : (m : ℝ) / (N / (d : ℝ)) = ((d * m : ℕ) : ℝ) / N := by
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hN]
  have hscaleM : (m : ℝ) / (M / (d : ℝ)) = ((d * m : ℕ) : ℝ) / M := by
    push_cast
    field_simp [ne_of_gt hdR, ne_of_gt hM]
  unfold p53FactorPairTerm p53ProductTwoScaleWeight
  rw [hscaleN, hscaleM]
  ring

/-- Exact antidiagonal form of one positive-index p.53 pair term. This is
the finite identity whose summation and reindexing produces the outer
divisor sum and the inner two-scale smoothed L-series. -/
theorem pairRTerm_eq_twistedKernel_antidiagonal
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} {s : ℂ} {r r' n : ℕ}
    (hr : 0 < r) (hr' : 0 < r') (hn : 0 < n) :
    jutilaP53PairRTerm M N s chi r r' n =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        (∑ p ∈ n.divisorsAntidiagonal,
          LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) p.1 *
            LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) p.2) *
        ((Real.exp (-((n : ℝ) / N)) -
          Real.exp (-((n : ℝ) / M))) : ℂ) := by
  have hconv := character_convolution_twistedKernel_eq_pair chi hr hr' hn
  have hrr : (((r * r' : ℕ) : ℂ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero hr.ne' hr'.ne')
  have hterm :
      LSeries.term
          (((chi ·) : ℕ → ℂ) ⍟ p53TwistedDivisorKernel chi r r')
          (1 + s) n =
        (((r * r' : ℕ) : ℂ)) *
          LSeries.term (p53PairCoefficient chi r r') (1 + s) n := by
    rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne', hconv]
    ring
  rw [pairRTerm_eq_LSeries_term_mul_difference chi hn]
  rw [LSeries.term_convolution] at hterm
  calc
    LSeries.term (p53PairCoefficient chi r r') (1 + s) n *
          ((Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M))) : ℂ) =
        (((r * r' : ℕ) : ℂ)⁻¹) *
          ((((r * r' : ℕ) : ℂ)) *
            LSeries.term (p53PairCoefficient chi r r') (1 + s) n) *
          ((Real.exp (-((n : ℝ) / N)) -
            Real.exp (-((n : ℝ) / M))) : ℂ) := by
      field_simp [hrr]
    _ = _ := by rw [← hterm]

/-- The same identity with the antidiagonal coordinates made explicit as
`d*m=n`. This is the precise algebra used by the subsequent sigma/product
equivalence; in particular no coprimality of `d,m` is introduced. -/
theorem pairRTerm_eq_twistedKernel_factorPairs
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} {s : ℂ} {r r' n : ℕ}
    (hr : 0 < r) (hr' : 0 < r') (hn : 0 < n) :
    jutilaP53PairRTerm M N s chi r r' n =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        (∑ p ∈ n.divisorsAntidiagonal,
          LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) p.1 *
            LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) p.2 *
            p53ProductTwoScaleWeight M N p.1 p.2) := by
  rw [pairRTerm_eq_twistedKernel_antidiagonal chi hr hr' hn]
  rw [mul_assoc]
  apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hmul : p.1 * p.2 = n :=
    (Nat.mem_divisorsAntidiagonal.mp hp).1
  rw [p53ProductTwoScaleWeight, hmul]

/-- The outer finite-Euler summand in Jutila's p.53 formula. -/
def p53OuterTwoScaleTerm {q : ℕ} (chi : DirichletCharacter ℂ q)
    (M N : ℝ) (s : ℂ) (r r' d : ℕ) : ℂ :=
  LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
    p53InnerTwoScale chi s (N / (d : ℝ)) (M / (d : ℝ))

theorem p53OuterTwoScaleTerm_eq_zero_of_not_dvd
    {q : ℕ} (chi : DirichletCharacter ℂ q) (M N : ℝ) (s : ℂ)
    {r r' d : ℕ} (hr : Squarefree r) (hr' : Squarefree r')
    (hnd : ¬ d ∣ r.lcm r') :
    p53OuterTwoScaleTerm chi M N s r r' d = 0 := by
  by_cases hd0 : d = 0
  · subst d
    simp [p53OuterTwoScaleTerm, LSeries.term_zero]
  · have hk : p53TwistedDivisorKernel chi r r' d = 0 := by
      unfold p53TwistedDivisorKernel
      rw [p53PairDivisorKernel_eq_zero_of_not_dvd_lcm' hr hr' hd0 hnd]
      simp
    unfold p53OuterTwoScaleTerm
    rw [LSeries.term_of_ne_zero hd0, hk]
    simp

theorem summable_p53OuterTwoScaleTerm
    {q : ℕ} (chi : DirichletCharacter ℂ q) (M N : ℝ) (s : ℂ)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    Summable (p53OuterTwoScaleTerm chi M N s r r') := by
  apply summable_of_hasFiniteSupport
  change (Function.support (p53OuterTwoScaleTerm chi M N s r r')).Finite
  apply (Finset.finite_toSet (r.lcm r').divisors).subset
  intro d hd
  by_contra hmem
  have hnd : ¬ d ∣ r.lcm r' := by
    intro hdvd
    exact hmem (Nat.mem_divisors.mpr ⟨hdvd,
      Nat.lcm_ne_zero (Squarefree.ne_zero hr) (Squarefree.ne_zero hr')⟩)
  exact hd (p53OuterTwoScaleTerm_eq_zero_of_not_dvd chi M N s hr hr' hnd)

theorem tsum_pnat_outer_eq_sum_divisors
    {q : ℕ} (chi : DirichletCharacter ℂ q) (M N : ℝ) (s : ℂ)
    {r r' : ℕ} (hr : Squarefree r) (hr' : Squarefree r') :
    (∑' d : ℕ+, p53OuterTwoScaleTerm chi M N s r r' d) =
      ∑ d ∈ (r.lcm r').divisors,
        p53OuterTwoScaleTerm chi M N s r r' d := by
  have hsum := summable_p53OuterTwoScaleTerm chi M N s hr hr'
  have hzero : p53OuterTwoScaleTerm chi M N s r r' 0 = 0 := by
    simp [p53OuterTwoScaleTerm, LSeries.term_zero]
  have hpnat :
      (∑' d : ℕ+, p53OuterTwoScaleTerm chi M N s r r' d) =
        ∑' d : ℕ, p53OuterTwoScaleTerm chi M N s r r' d := by
    have h := tsum_zero_pnat_eq_tsum_nat hsum
    simpa only [hzero, zero_add] using h
  rw [hpnat]
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    simp [p53OuterTwoScaleTerm, LSeries.term_zero]
  · apply p53OuterTwoScaleTerm_eq_zero_of_not_dvd chi M N s hr hr'
    intro hdiv
    exact hd (Nat.mem_divisors.mpr ⟨hdiv,
      Nat.lcm_ne_zero (Squarefree.ne_zero hr) (Squarefree.ne_zero hr')⟩)

/-- Global positive-index Fubini/reindexing. It is already the exact p.53
formula, except that the finite outer support is still written as a `PNat`
tsum rather than a finite divisor sum. -/
theorem pairRB_eq_twistedKernel_innerTwoScale_pnat
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s chi r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑' d : ℕ+,
          LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
            p53InnerTwoScale chi s (N / (d : ℝ)) (M / (d : ℝ)) := by
  have hrPos : 0 < r := Nat.pos_of_ne_zero (Squarefree.ne_zero hr)
  have hr'Pos : 0 < r' := Nat.pos_of_ne_zero (Squarefree.ne_zero hr')
  have hpair := summable_jutilaP53PairRTerm hM hMN hs chi hrPos hr'Pos
  have hfactor := summable_p53FactorPairTerm_pnat chi hM hMN hs hr hr'
  have hfactorSwap : Summable (fun p : ℕ+ × ℕ+ =>
      p53FactorPairTerm chi M N s r r' p.2 p.1) := by
    simpa only [Function.comp_def, Equiv.prodComm_apply] using!
      (Equiv.prodComm ℕ+ ℕ+).summable_iff.mpr hfactor
  have hzero : jutilaP53PairRTerm M N s chi r r' 0 = 0 := by
    simp [jutilaP53PairRTerm]
  calc
    jutilaP53PairRB M N s chi r r' =
        ∑' n : ℕ, jutilaP53PairRTerm M N s chi r r' n := rfl
    _ = ∑' n : ℕ+, jutilaP53PairRTerm M N s chi r r' n := by
      rw [← tsum_zero_pnat_eq_tsum_nat hpair, hzero, zero_add]
    _ = ∑' n : ℕ+, (((r * r' : ℕ) : ℂ)⁻¹) *
          (∑ p ∈ (n : ℕ).divisorsAntidiagonal,
            p53FactorPairTerm chi M N s r r' p.2 p.1) := by
      apply tsum_congr
      intro n
      have hterm := pairRTerm_eq_twistedKernel_factorPairs (M := M) (N := N)
        (s := s) chi hrPos hr'Pos n.2
      calc
        jutilaP53PairRTerm M N s chi r r' n =
            (((r * r' : ℕ) : ℂ)⁻¹) *
              (∑ p ∈ (n : ℕ).divisorsAntidiagonal,
                LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) p.1 *
                  LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) p.2 *
                  p53ProductTwoScaleWeight M N p.1 p.2) := hterm
        _ = _ := by
          apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
          apply Finset.sum_congr rfl
          intro p hp
          unfold p53FactorPairTerm p53ProductTwoScaleWeight
          rw [mul_comm p.2 p.1]
    _ = (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑' n : ℕ+, ∑ p ∈ (n : ℕ).divisorsAntidiagonal,
            p53FactorPairTerm chi M N s r r' p.2 p.1 := by
      rw [tsum_mul_left]
    _ = (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑' p : ℕ+ × ℕ+,
            p53FactorPairTerm chi M N s r r' p.2 p.1 := by
      rw [tsum_pnat_antidiagonal_eq_tsum_prod
        (fun m d => p53FactorPairTerm chi M N s r r' d m) hfactorSwap]
    _ = (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑' p : ℕ+ × ℕ+,
            p53FactorPairTerm chi M N s r r' p.1 p.2 := by
      congr 1
      exact (Equiv.prodComm ℕ+ ℕ+).tsum_eq
        (fun p : ℕ+ × ℕ+ => p53FactorPairTerm chi M N s r r' p.1 p.2)
    _ = (((r * r' : ℕ) : ℂ)⁻¹) *
          ∑' d : ℕ+, ∑' m : ℕ+,
            p53FactorPairTerm chi M N s r r' d m := by
      rw [hfactor.tsum_prod]
    _ = _ := by
      apply congrArg (((((r * r' : ℕ) : ℂ)⁻¹)) * ·)
      apply tsum_congr
      intro d
      have hN : 0 < N := hM.trans hMN
      have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast d.2
      have hinner := summable_inner_twoScale chi hs
        (div_pos hN hdR) (div_pos hM hdR)
      let innerTerm : ℕ → ℂ := fun m =>
        LSeries.term ((chi ·) : ℕ → ℂ) (1 + s) m *
          ((Real.exp (-((m : ℝ) / (N / (d : ℝ)))) -
            Real.exp (-((m : ℝ) / (M / (d : ℝ))))) : ℂ)
      have hinnerPnat : (∑' m : ℕ+, innerTerm m) =
          p53InnerTwoScale chi s (N / (d : ℝ)) (M / (d : ℝ)) := by
        have h := tsum_zero_pnat_eq_tsum_nat hinner
        change innerTerm 0 + (∑' m : ℕ+, innerTerm m) =
          ∑' m : ℕ, innerTerm m at h
        have hzeroInner : innerTerm 0 = 0 := by
          simp [innerTerm, LSeries.term_zero]
        rw [hzeroInner, zero_add] at h
        exact h
      calc
        (∑' m : ℕ+, p53FactorPairTerm chi M N s r r' d m) =
            ∑' m : ℕ+,
              LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
                innerTerm m := by
          apply tsum_congr
          intro m
          simpa only [innerTerm] using!
            (p53FactorPairTerm_eq_outer_mul_innerTerm (M := M) (N := N)
              chi hM hMN s r r' d.2 m.2)
        _ = LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
              (∑' m : ℕ+, innerTerm m) := by rw [tsum_mul_left]
        _ = _ := by rw [hinnerPnat]


/-- Exact finite-support Fubini and `n=d*m` reindexing used on Jutila p.53. -/
theorem pairRB_eq_divisorKernel_innerTwoScale
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {s : ℂ} (hs : 0 ≤ s.re) {r r' : ℕ}
    (hr : Squarefree r) (hr' : Squarefree r') :
    jutilaP53PairRB M N s chi r r' =
      (((r * r' : ℕ) : ℂ)⁻¹) *
        ∑ d ∈ (r.lcm r').divisors,
          LSeries.term (p53TwistedDivisorKernel chi r r') (1 + s) d *
            p53InnerTwoScale chi s (N / (d : ℝ)) (M / (d : ℝ)) := by
  rw [pairRB_eq_twistedKernel_innerTwoScale_pnat chi hM hMN hs hr hr']
  change (((r * r' : ℕ) : ℂ)⁻¹) *
      (∑' d : ℕ+, p53OuterTwoScaleTerm chi M N s r r' d) = _
  rw [tsum_pnat_outer_eq_sum_divisors chi M N s hr hr']
  rfl




end

end MAPJutilaP53FiniteFubiniReindex

#print axioms MAPJutilaP53FiniteFubiniReindex.pairRTerm_eq_twistedKernel_antidiagonal
#print axioms MAPJutilaP53FiniteFubiniReindex.pairRTerm_eq_twistedKernel_factorPairs
#print axioms MAPJutilaP53FiniteFubiniReindex.pairRB_eq_divisorKernel_innerTwoScale
