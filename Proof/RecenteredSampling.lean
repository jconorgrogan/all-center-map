import FiniteHilbertInequality
import DiscreteMeanValueSourceLeaf
import FixedCharacterPoweredBridge
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Recentered continuum-to-separated sampling

-/

namespace RecenteredSampling

open scoped BigOperators ComplexConjugate RealInnerProductSpace
open MeasureTheory CGLProofDAG

noncomputable section

/-! ## A literal one-dimensional local Sobolev estimate -/

/-- Point evaluation at the left endpoint of a unit interval is controlled by
the `L²` energy of a continuously differentiable Hilbert-space-valued function
and its derivative.  The constants are literal: `2` on the function energy and
`1` on the derivative energy. -/
theorem norm_sq_le_unit_interval_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f f' : ℝ → E} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (a : ℝ) :
    ‖f a‖ ^ 2 ≤
      2 * (∫ x in a..a + 1, ‖f x‖ ^ 2) +
        ∫ x in a..a + 1, ‖f' x‖ ^ 2 := by
  let g : ℝ → ℝ := fun x => ‖f x‖ ^ 2
  let g' : ℝ → ℝ := fun x => 2 * inner ℝ (f x) (f' x)
  let energy : ℝ → ℝ := fun x => ‖f x‖ ^ 2 + ‖f' x‖ ^ 2
  have hfcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hgderiv : ∀ x, HasDerivAt g (g' x) x := by
    intro x
    simpa [g, g'] using (hf x).norm_sq
  have hg'int : IntervalIntegrable g' volume a (a + 1) := by
    apply Continuous.intervalIntegrable
    exact (hfcont.inner hf').const_mul 2
  have hgint : IntervalIntegrable g volume a (a + 1) := by
    simpa [g] using (hfcont.norm.pow 2).intervalIntegrable a (a + 1)
  have hf'int : IntervalIntegrable (fun x => ‖f' x‖ ^ 2) volume a (a + 1) := by
    exact (hf'.norm.pow 2).intervalIntegrable a (a + 1)
  have henergyInt : IntervalIntegrable energy volume a (a + 1) := by
    exact hgint.add hf'int
  have hpoint : ∀ y ∈ Set.Icc a (a + 1), g a ≤ g y + ∫ x in a..a + 1, energy x := by
    intro y hy
    have hay : a ≤ y := hy.1
    have hya1 : y ≤ a + 1 := hy.2
    have hg'int_ay : IntervalIntegrable g' volume a y := by
      apply Continuous.intervalIntegrable
      exact (hfcont.inner hf').const_mul 2
    have hftc : (∫ x in a..y, g' x) = g y - g a := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hgderiv x) hg'int_ay
    have hneg_le : ∀ x, -g' x ≤ energy x := by
      intro x
      have hinner := abs_real_inner_le_norm (f x) (f' x)
      have hneg : -inner ℝ (f x) (f' x) ≤ ‖f x‖ * ‖f' x‖ :=
        by linarith [(abs_le.mp hinner).1]
      dsimp [g', energy]
      nlinarith [sq_nonneg (‖f x‖ - ‖f' x‖)]
    have hnegInt : IntervalIntegrable (fun x => -g' x) volume a y :=
      hg'int_ay.neg
    have henergyInt_ay : IntervalIntegrable energy volume a y := by
      apply Continuous.intervalIntegrable
      exact (hfcont.norm.pow 2).add (hf'.norm.pow 2)
    have hmono :
        (∫ x in a..y, -g' x) ≤ ∫ x in a..y, energy x := by
      exact intervalIntegral.integral_mono_on hay hnegInt henergyInt_ay
        (fun x _ => hneg_le x)
    have henonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc a (a + 1))] energy := by
      filter_upwards with x
      simp only [energy]
      positivity
    have henlarge :
        (∫ x in a..y, energy x) ≤ ∫ x in a..a + 1, energy x := by
      exact intervalIntegral.integral_mono_interval le_rfl hay hya1
        henonneg henergyInt
    have hident : g a = g y + ∫ x in a..y, -g' x := by
      rw [intervalIntegral.integral_neg, hftc]
      ring
    rw [hident]
    linarith
  have hconstInt : IntervalIntegrable (fun _x : ℝ => g a) volume a (a + 1) :=
    intervalIntegrable_const
  have hrightInt : IntervalIntegrable
      (fun y => g y + ∫ x in a..a + 1, energy x) volume a (a + 1) :=
    hgint.add intervalIntegrable_const
  have hintegrated := intervalIntegral.integral_mono_on
    (by linarith : a ≤ a + 1) hconstInt hrightInt hpoint
  rw [intervalIntegral.integral_add hgint intervalIntegrable_const] at hintegrated
  simp only [intervalIntegral.integral_const] at hintegrated
  norm_num at hintegrated
  have henergyEq :
      (∫ x in a..a + 1, energy x) =
        (∫ x in a..a + 1, g x) +
          ∫ x in a..a + 1, ‖f' x‖ ^ 2 := by
    exact intervalIntegral.integral_add hgint hf'int
  rw [henergyEq] at hintegrated
  dsimp [g] at hintegrated ⊢
  calc
    ‖f a‖ ^ 2 ≤
        (∫ x in a..a + 1, ‖f x‖ ^ 2) +
          ((∫ x in a..a + 1, ‖f x‖ ^ 2) +
            ∫ x in a..a + 1, ‖f' x‖ ^ 2) := hintegrated
    _ = 2 * (∫ x in a..a + 1, ‖f x‖ ^ 2) +
          ∫ x in a..a + 1, ‖f' x‖ ^ 2 := by ring

/-! ## Packing one-separated right unit intervals -/

/-- The half-open right unit intervals based at a one-separated finite set are
literally pairwise disjoint.  Choosing `Ioc` handles the equality-gap endpoint
without an almost-everywhere exception. -/
theorem pairwiseDisjoint_Ioc_unit {W : Finset ℝ}
    (hsep : OneSeparated W) :
    Set.Pairwise (↑W : Set ℝ)
      (fun t u : ℝ => Disjoint (Set.Ioc t (t + 1)) (Set.Ioc u (u + 1))) := by
  intro t ht u hu htu
  rw [Set.disjoint_left]
  intro x hxt hxu
  rcases lt_or_gt_of_ne htu with htu' | hut'
  · have hgap := hsep t ht u hu htu
    rw [abs_of_nonpos (sub_nonpos.mpr htu'.le)] at hgap
    linarith [hxt.2, hxu.1]
  · have hgap := hsep u hu t ht htu.symm
    rw [abs_of_nonpos (sub_nonpos.mpr hut'.le)] at hgap
    linarith [hxu.2, hxt.1]

/-- The union of the packed right unit intervals stays in the single collar
`(0,T+1]` when the sample ordinates lie in `[0,T]`. -/
theorem iUnion_Ioc_unit_subset
    {T : ℝ} {W : Finset ℝ}
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (⋃ t ∈ W, Set.Ioc t (t + 1)) ⊆ Set.Ioc 0 (T + 1) := by
  intro x hx
  simp only [Set.mem_iUnion, Finset.mem_coe] at hx
  rcases hx with ⟨t, ht, hxt⟩
  exact ⟨lt_of_le_of_lt (hheight t ht).1 hxt.1,
    by linarith [(hheight t ht).2, hxt.2]⟩

/-- A nonnegative continuous density integrates over all packed unit intervals
to at most its integral over the one-unit global right collar. -/
theorem sum_unit_interval_integral_le_collar
    {T : ℝ} {W : Finset ℝ} {g : ℝ → ℝ}
    (hT : 0 ≤ T) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (∑ t ∈ W, ∫ x in t..t + 1, g x) ≤
      ∫ x in (0 : ℝ)..T + 1, g x := by
  have hpair := pairwiseDisjoint_Ioc_unit hsep
  have hlocal : ∀ t ∈ W, IntegrableOn g (Set.Ioc t (t + 1)) volume := by
    intro t ht
    exact (hg.intervalIntegrable t (t + 1)).1
  have hunion := integral_biUnion_finset W
    (fun _t _ht => measurableSet_Ioc) hpair hlocal
  have hglobalInt : IntegrableOn g (Set.Ioc 0 (T + 1)) volume :=
    (hg.intervalIntegrable 0 (T + 1)).1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 (T + 1))] g := by
    filter_upwards with x
    exact hg0 x
  have hmono :
      (∫ x in ⋃ t ∈ W, Set.Ioc t (t + 1), g x) ≤
        ∫ x in Set.Ioc 0 (T + 1), g x := by
    exact setIntegral_mono_set hglobalInt hnonneg
      (iUnion_Ioc_unit_subset hheight).eventuallyLE
  rw [hunion] at hmono
  calc
    (∑ t ∈ W, ∫ x in t..t + 1, g x) =
        ∑ t ∈ W, ∫ x in Set.Ioc t (t + 1), g x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact intervalIntegral.integral_of_le (by linarith)
    _ ≤ ∫ x in Set.Ioc 0 (T + 1), g x := hmono
    _ = ∫ x in (0 : ℝ)..T + 1, g x :=
      (intervalIntegral.integral_of_le (by linarith)).symm

/-- Global one-separated Sobolev sampling on the right collar, with no
cardinality loss and the literal local constants `2` and `1`. -/
theorem sum_norm_sq_le_collar_energy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℝ} {W : Finset ℝ} {f f' : ℝ → E}
    (hT : 0 ≤ T) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (∑ t ∈ W, ‖f t‖ ^ 2) ≤
      2 * (∫ x in (0 : ℝ)..T + 1, ‖f x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1, ‖f' x‖ ^ 2 := by
  have hfcont : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  calc
    (∑ t ∈ W, ‖f t‖ ^ 2) ≤
        ∑ t ∈ W,
          (2 * (∫ x in t..t + 1, ‖f x‖ ^ 2) +
            ∫ x in t..t + 1, ‖f' x‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact norm_sq_le_unit_interval_energy hf hf' t
    _ = 2 * (∑ t ∈ W, ∫ x in t..t + 1, ‖f x‖ ^ 2) +
          ∑ t ∈ W, ∫ x in t..t + 1, ‖f' x‖ ^ 2 := by
      rw [Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
    _ ≤ 2 * (∫ x in (0 : ℝ)..T + 1, ‖f x‖ ^ 2) +
          ∫ x in (0 : ℝ)..T + 1, ‖f' x‖ ^ 2 := by
      gcongr
      · exact sum_unit_interval_integral_le_collar hT (hfcont.norm.pow 2)
          (fun _ => sq_nonneg _) hsep hheight
      · exact sum_unit_interval_integral_le_collar hT (hf'.norm.pow 2)
          (fun _ => sq_nonneg _) hsep hheight

/-! ## Exact recentering of the dyadic Dirichlet polynomial -/

open MontgomeryVaughanFiniteReduction

/-- The shifted logarithmic frequency after removal of the common `log N`
carrier. -/
def shiftedLogFrequency (N n : ℕ) : ℝ := Real.log n - Real.log N

def shiftedPhase (N n : ℕ) (t : ℝ) : ℂ :=
  Complex.exp ((((t * shiftedLogFrequency N n : ℝ) : ℂ)) * Complex.I)

def recenteredPolynomial (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicSupport N, b n * shiftedPhase N n t

def recenteredDerivative (b : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ dyadicSupport N,
    b n * ((shiftedLogFrequency N n : ℝ) : ℂ) * Complex.I * shiftedPhase N n t

theorem hasDerivAt_shiftedPhase (N n : ℕ) (t : ℝ) :
    HasDerivAt (shiftedPhase N n)
      (shiftedPhase N n t *
        (((shiftedLogFrequency N n : ℝ) : ℂ) * Complex.I)) t := by
  unfold shiftedPhase
  have hcomplex : HasDerivAt
      (fun s : ℝ => ((s * shiftedLogFrequency N n : ℝ) : ℂ))
      (shiftedLogFrequency N n : ℂ) t := by
    convert (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const
      (shiftedLogFrequency N n : ℂ) using 1
    · funext s
      simp only [Complex.ofRealCLM_apply]
      push_cast
      ring
    · simp
  exact (hcomplex.mul_const Complex.I).cexp

theorem hasDerivAt_recenteredPolynomial
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (recenteredPolynomial b N)
      (recenteredDerivative b N t) t := by
  unfold recenteredPolynomial recenteredDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  convert (hasDerivAt_shiftedPhase N n t).const_mul (b n) using 1 <;> ring

/-- Recentring is exactly multiplication by the unit-modulus carrier
`exp(-it log N)`. -/
theorem recenteredPolynomial_eq_carrier_mul
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    recenteredPolynomial b N t =
      Complex.exp (-(((t * Real.log N : ℝ) : ℂ) * Complex.I)) *
        dirichletPolynomial b N t := by
  rw [MontgomeryVaughanFiniteReduction.dirichletPolynomial_eq]
  unfold recenteredPolynomial dyadicSupport
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hphase :
      shiftedPhase N n t =
        Complex.exp (-(((t * Real.log N : ℝ) : ℂ) * Complex.I)) * phase n t := by
    unfold shiftedPhase shiftedLogFrequency phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

theorem norm_recenteredPolynomial
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    ‖recenteredPolynomial b N t‖ = ‖dirichletPolynomial b N t‖ := by
  rw [recenteredPolynomial_eq_carrier_mul, norm_mul]
  have hcarrier :
      ‖Complex.exp (-(((t * Real.log N : ℝ) : ℂ) * Complex.I))‖ = 1 := by
    convert Complex.norm_exp_ofReal_mul_I (-(t * Real.log N)) using 1 <;>
      push_cast <;> ring
  rw [hcarrier, one_mul]

def derivativeCoefficient (b : ℕ → ℂ) (N n : ℕ) : ℂ :=
  b n * ((shiftedLogFrequency N n : ℝ) : ℂ) * Complex.I

theorem recenteredDerivative_eq_recenteredPolynomial
    (b : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    recenteredDerivative b N t = recenteredPolynomial (derivativeCoefficient b N) N t := by
  unfold recenteredDerivative recenteredPolynomial derivativeCoefficient
  rfl

/-- On the exact dyadic support `(N,2N]`, recentering places every frequency
in `[0,1]`.  The upper bound uses the literal estimate `log 2 ≤ 1`. -/
theorem shiftedLogFrequency_mem_Icc
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ dyadicSupport N) :
    shiftedLogFrequency N n ∈ Set.Icc (0 : ℝ) 1 := by
  have hNposNat : 0 < N := by omega
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnposNat : 0 < n := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hnposNat
  have hNle : (N : ℝ) ≤ n := by exact_mod_cast hnBounds.1.le
  have hnle : (n : ℝ) ≤ (2 : ℝ) * N := by
    norm_num
    exact_mod_cast hnBounds.2
  have hlogLower : Real.log (N : ℝ) ≤ Real.log (n : ℝ) :=
    Real.strictMonoOn_log.monotoneOn hNpos hnpos hNle
  have h2Npos : (0 : ℝ) < 2 * N := mul_pos (by norm_num) hNpos
  have hlogUpper : Real.log (n : ℝ) ≤ Real.log ((2 : ℝ) * N) :=
    Real.strictMonoOn_log.monotoneOn hnpos h2Npos hnle
  have hlogMul : Real.log ((2 : ℝ) * N) = Real.log 2 + Real.log (N : ℝ) := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;>
      norm_num
  unfold shiftedLogFrequency
  constructor <;> linarith

theorem abs_shiftedLogFrequency_le_one
    {N n : ℕ} (hN : 1 ≤ N) (hn : n ∈ dyadicSupport N) :
    |shiftedLogFrequency N n| ≤ 1 := by
  have h := shiftedLogFrequency_mem_Icc hN hn
  rw [abs_of_nonneg h.1]
  exact h.2

/-- The derivative coefficients have no larger dyadic `ℓ²` energy than the
original coefficients.  This is the formal payoff of recentering. -/
theorem coefficientEnergy_derivativeCoefficient_le
    (b : ℕ → ℂ) (N : ℕ) (hN : 1 ≤ N) :
    coefficientEnergy (derivativeCoefficient b N) N ≤
      coefficientEnergy b N := by
  unfold coefficientEnergy
  apply Finset.sum_le_sum
  intro n hn
  rw [derivativeCoefficient, norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one]
  have hfreq := abs_shiftedLogFrequency_le_one hN hn
  have hfreq0 : 0 ≤ |shiftedLogFrequency N n| := abs_nonneg _
  have hsq : |shiftedLogFrequency N n| ^ 2 ≤ (1 : ℝ) := by
    nlinarith
  calc
    (‖b n‖ * |shiftedLogFrequency N n|) ^ 2 =
        ‖b n‖ ^ 2 * |shiftedLogFrequency N n| ^ 2 := by ring
    _ ≤ ‖b n‖ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
    _ = ‖b n‖ ^ 2 := by ring

/-! ## Continuous mean square from the finite Hilbert leaf -/

/-- The exact finite Hilbert leaf already isolated in
`MontgomeryVaughanFiniteReduction` gives the real continuous mean square with
the literal collar length and off-diagonal constant. -/
theorem continuous_meanSquare_le_of_hilbert
    (hHilbert : FiniteLogHilbertInequality)
    (b : ℕ → ℂ) (N : ℕ) (S : ℝ) (hN : 1 ≤ N) (hS : 0 ≤ S) :
    (∫ t in (0 : ℝ)..S, ‖dirichletPolynomial b N t‖ ^ 2) ≤
      (S + 2 * Classical.choose hHilbert * N) * coefficientEnergy b N := by
  let D : ℝ → ℂ := fun t => dirichletPolynomial b N t
  have hDcont : Continuous D := by
    unfold D CGLProofDAG.dirichletPolynomial
    fun_prop
  have hprodInt : IntervalIntegrable (fun t => D t * star (D t)) volume 0 S := by
    apply Continuous.intervalIntegrable
    exact hDcont.mul (hDcont.star)
  have hreComm := RCLike.reCLM.intervalIntegral_comp_comm hprodInt
  have hreal :
      (∫ t in (0 : ℝ)..S, ‖D t‖ ^ 2) =
        (∫ t in (0 : ℝ)..S, D t * star (D t)).re := by
    calc
      (∫ t in (0 : ℝ)..S, ‖D t‖ ^ 2) =
          ∫ t in (0 : ℝ)..S, (D t * star (D t)).re := by
        apply intervalIntegral.integral_congr
        intro t ht
        change ‖D t‖ ^ 2 = (D t * (starRingEnd ℂ) (D t)).re
        rw [Complex.mul_conj, ← Complex.sq_norm]
        change ‖D t‖ ^ 2 = ‖D t‖ ^ 2
        rfl
      _ = (∫ t in (0 : ℝ)..S, D t * star (D t)).re := hreComm
  have hoff := norm_integratedOffDiagonal_le_of_hilbert
    hHilbert b N S hN
  have hexpand := integral_square_eq_diagonal_add_offDiagonal b N S
  have henergy0 : 0 ≤ coefficientEnergy b N := by
    unfold coefficientEnergy
    positivity
  change (∫ t in (0 : ℝ)..S, ‖D t‖ ^ 2) ≤ _
  rw [hreal]
  have hexpandD :
      (∫ t in (0 : ℝ)..S, D t * star (D t)) =
        (S : ℂ) * coefficientEnergy b N + integratedOffDiagonal b N S := by
    simpa [D] using hexpand
  rw [hexpandD]
  calc
    ((S : ℂ) * coefficientEnergy b N + integratedOffDiagonal b N S).re ≤
        ‖(S : ℂ) * coefficientEnergy b N + integratedOffDiagonal b N S‖ :=
      Complex.re_le_norm _
    _ ≤ ‖(S : ℂ) * coefficientEnergy b N‖ +
        ‖integratedOffDiagonal b N S‖ := norm_add_le _ _
    _ ≤ S * coefficientEnergy b N +
        2 * Classical.choose hHilbert * N * coefficientEnergy b N := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg henergy0]
      exact add_le_add le_rfl hoff
    _ = (S + 2 * Classical.choose hHilbert * N) * coefficientEnergy b N := by
      ring

/-! ## Recentered continuum-to-discrete mean square -/

/-- The complete sampling adapter.  The only premise is the finite logarithmic
Hilbert inequality; recentering, Sobolev sampling, the right collar, and the
derivative coefficient estimate are all internal. -/
theorem discrete_meanSquare_raw_of_hilbert
    (hHilbert : FiniteLogHilbertInequality)
    (T : ℝ) (N : ℕ) (b : ℕ → ℂ) (W : Finset ℝ)
    (hT : 0 ≤ T) (hN : 1 ≤ N)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2) ≤
      3 * (T + 1 + 2 * Classical.choose hHilbert * N) *
        coefficientEnergy b N := by
  have hderivCont : Continuous (recenteredDerivative b N) := by
    unfold recenteredDerivative shiftedPhase shiftedLogFrequency
    fun_prop
  have hsamp := sum_norm_sq_le_collar_energy
    (T := T) (W := W)
    (f := recenteredPolynomial b N)
    (f' := recenteredDerivative b N)
    hT (hasDerivAt_recenteredPolynomial b N) hderivCont hsep hheight
  have hsamp' :
      (∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2) ≤
        2 * (∫ x in (0 : ℝ)..T + 1,
          ‖dirichletPolynomial b N x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1, ‖recenteredDerivative b N x‖ ^ 2 := by
    simpa only [norm_recenteredPolynomial] using hsamp
  let A : ℝ := T + 1 + 2 * Classical.choose hHilbert * N
  have hS : 0 ≤ T + 1 := by linarith
  have hbase :
      (∫ x in (0 : ℝ)..T + 1,
        ‖dirichletPolynomial b N x‖ ^ 2) ≤
        A * coefficientEnergy b N := by
    simpa [A] using continuous_meanSquare_le_of_hilbert
      hHilbert b N (T + 1) hN hS
  have hderivIntegralEq :
      (∫ x in (0 : ℝ)..T + 1, ‖recenteredDerivative b N x‖ ^ 2) =
        ∫ x in (0 : ℝ)..T + 1,
          ‖dirichletPolynomial (derivativeCoefficient b N) N x‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    change ‖recenteredDerivative b N x‖ ^ 2 =
      ‖dirichletPolynomial (derivativeCoefficient b N) N x‖ ^ 2
    rw [recenteredDerivative_eq_recenteredPolynomial,
      norm_recenteredPolynomial]
  have hCpos : 0 < Classical.choose hHilbert :=
    (Classical.choose_spec hHilbert).1
  have hA0 : 0 ≤ A := by
    unfold A
    positivity
  have hderiv :
      (∫ x in (0 : ℝ)..T + 1, ‖recenteredDerivative b N x‖ ^ 2) ≤
        A * coefficientEnergy b N := by
    rw [hderivIntegralEq]
    calc
      (∫ x in (0 : ℝ)..T + 1,
          ‖dirichletPolynomial (derivativeCoefficient b N) N x‖ ^ 2) ≤
          A * coefficientEnergy (derivativeCoefficient b N) N := by
        simpa [A] using continuous_meanSquare_le_of_hilbert
          hHilbert (derivativeCoefficient b N) N (T + 1) hN hS
      _ ≤ A * coefficientEnergy b N :=
        mul_le_mul_of_nonneg_left
          (coefficientEnergy_derivativeCoefficient_le b N hN) hA0
  calc
    (∑ t ∈ W, ‖dirichletPolynomial b N t‖ ^ 2) ≤
        2 * (∫ x in (0 : ℝ)..T + 1,
          ‖dirichletPolynomial b N x‖ ^ 2) +
        ∫ x in (0 : ℝ)..T + 1, ‖recenteredDerivative b N x‖ ^ 2 := hsamp'
    _ ≤ 2 * (A * coefficientEnergy b N) +
        A * coefficientEnergy b N := by gcongr
    _ = 3 * (T + 1 + 2 * Classical.choose hHilbert * N) *
        coefficientEnergy b N := by unfold A; ring

/-- Inhabitation of the exact epsilon-form discrete mean-square contract.  The
`T^η` factor is harmless here because `T ≥ 2`; the literal constant produced by
the recentered collar proof is `6 * (1 + C_H)`. -/
theorem discreteDirichletMeanSquare_of_hilbert
    (hHilbert : FiniteLogHilbertInequality) :
    DiscreteMeanValueSourceLeaf.DiscreteDirichletMeanSquare := by
  intro η hη
  let C : ℝ := 6 * (1 + Classical.choose hHilbert)
  have hCH : 0 < Classical.choose hHilbert :=
    (Classical.choose_spec hHilbert).1
  have hC : 0 < C := by
    unfold C
    positivity
  refine ⟨C, 2, hC, by norm_num, ?_⟩
  intro T N b W hT hN hsep hheight
  have hT0 : 0 ≤ T := by linarith
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hpow : 1 ≤ Real.rpow T η :=
    Real.one_le_rpow (by linarith) hη.le
  have hpre :
      3 * (T + 1 + 2 * Classical.choose hHilbert * N) ≤
        C * Real.rpow T η * ((N : ℝ) + T) := by
    have hfirst :
        3 * (T + 1 + 2 * Classical.choose hHilbert * N) ≤
          C * ((N : ℝ) + T) := by
      unfold C
      nlinarith [mul_nonneg hCH.le hT0]
    have hfac0 : 0 ≤ C * ((N : ℝ) + T) :=
      mul_nonneg hC.le (add_nonneg hN0 hT0)
    calc
      3 * (T + 1 + 2 * Classical.choose hHilbert * N) ≤
          C * ((N : ℝ) + T) := hfirst
      _ ≤ (C * ((N : ℝ) + T)) * Real.rpow T η :=
        le_mul_of_one_le_right hfac0 hpow
      _ = C * Real.rpow T η * ((N : ℝ) + T) := by ring
  have hraw := discrete_meanSquare_raw_of_hilbert
    hHilbert T N b W hT0 hN hsep hheight
  have henergy0 : 0 ≤ coefficientEnergy b N := by
    unfold coefficientEnergy
    positivity
  have hfinal := hraw.trans (mul_le_mul_of_nonneg_right hpre henergy0)
  simpa [MontgomeryVaughanFiniteReduction.coefficientEnergy,
    DiscreteMeanValueSourceLeaf.coefficientEnergy,
    MontgomeryVaughanFiniteReduction.dyadicSupport] using hfinal

/-- Exact large-value proposition formerly left uninhabited: after this
adapter, the sole remaining premise is the finite logarithmic Hilbert theorem. -/
theorem discreteDirichletMeanValue_of_hilbert
    (hHilbert : FiniteLogHilbertInequality) :
    FixedCharacterPoweredBridge.DiscreteDirichletMeanValue := by
  exact DiscreteMeanValueSourceLeaf.discreteLargeValue_of_meanSquare
    (discreteDirichletMeanSquare_of_hilbert hHilbert)

/-- The discrete Dirichlet large-value input is inhabited unconditionally by
the finite sawtooth/Parseval Hilbert inequality and the recentered sampling
adapter. -/
theorem discreteDirichletMeanValue :
    FixedCharacterPoweredBridge.DiscreteDirichletMeanValue :=
  discreteDirichletMeanValue_of_hilbert
    MontgomeryVaughanFiniteReduction.finiteLogHilbertInequality_via_integerHilbert

end
end RecenteredSampling

#print axioms RecenteredSampling.norm_sq_le_unit_interval_energy
#print axioms RecenteredSampling.pairwiseDisjoint_Ioc_unit
#print axioms RecenteredSampling.sum_unit_interval_integral_le_collar
#print axioms RecenteredSampling.sum_norm_sq_le_collar_energy
#print axioms RecenteredSampling.hasDerivAt_recenteredPolynomial
#print axioms RecenteredSampling.norm_recenteredPolynomial
#print axioms RecenteredSampling.coefficientEnergy_derivativeCoefficient_le
#print axioms RecenteredSampling.continuous_meanSquare_le_of_hilbert
#print axioms RecenteredSampling.discrete_meanSquare_raw_of_hilbert
#print axioms RecenteredSampling.discreteDirichletMeanSquare_of_hilbert
#print axioms RecenteredSampling.discreteDirichletMeanValue_of_hilbert
#print axioms RecenteredSampling.discreteDirichletMeanValue
