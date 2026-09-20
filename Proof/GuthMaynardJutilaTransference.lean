import GuthMaynardHeathBrownMajorant
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The deterministic Heath--Brown--Jutila transference lemma

This is the finite argument in Lemma 29.7 of the cached third volume.  The
natural-number supports retain the source endpoint conventions
`M < n ≤ M'`, `J ≤ p ≤ J'`, and `JM < l ≤ J'M'`.  The proof is the literal
Parseval/product-collection argument, followed by the already-certified
finite Gram majorant.
-/

namespace GuthMaynardJutilaTransference

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open MeasureTheory intervalIntegral AddCircle Complex

noncomputable section

/-! ## Literal finite supports -/

def natRealIoc (M M' : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil M' + 1)).filter
    (fun n => M < (n : ℝ) ∧ (n : ℝ) ≤ M')

@[simp]
theorem mem_natRealIoc_iff {M M' : ℝ} (_hM' : 0 ≤ M') {n : ℕ} :
    n ∈ natRealIoc M M' ↔ M < (n : ℝ) ∧ (n : ℝ) ≤ M' := by
  constructor
  · exact fun hn => (Finset.mem_filter.mp hn).2
  · intro hn
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn⟩
    have hnceilR : (n : ℝ) ≤ (Nat.ceil M' : ℝ) :=
      hn.2.trans (Nat.le_ceil M')
    have hnceil : n ≤ Nat.ceil M' := by exact_mod_cast hnceilR
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnceil)

def primeRealIcc (J J' : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil J' + 1)).filter
    (fun p => J ≤ (p : ℝ) ∧ (p : ℝ) ≤ J' ∧ Nat.Prime p)

@[simp]
theorem mem_primeRealIcc_iff {J J' : ℝ} (_hJ' : 0 ≤ J') {p : ℕ} :
    p ∈ primeRealIcc J J' ↔
      J ≤ (p : ℝ) ∧ (p : ℝ) ≤ J' ∧ Nat.Prime p := by
  constructor
  · exact fun hp => (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, hp⟩
    have hpceilR : (p : ℝ) ≤ (Nat.ceil J' : ℝ) :=
      hp.2.1.trans (Nat.le_ceil J')
    have hpceil : p ≤ Nat.ceil J' := by exact_mod_cast hpceilR
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hpceil)

def productRealIoc (J J' M M' : ℝ) : Finset ℕ :=
  natRealIoc (J * M) (J' * M')

theorem product_mem_productRealIoc
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hM : 0 ≤ M)
    (hJ' : J ≤ J') (hM' : M < M')
    {p n : ℕ} (hp : p ∈ primeRealIcc J J')
    (hn : n ∈ natRealIoc M M') :
    p * n ∈ productRealIoc J J' M M' := by
  have hJ'0 : 0 ≤ J' := le_trans (by linarith) hJ'
  have hM'0 : 0 ≤ M' := hM.trans hM'.le
  rw [productRealIoc, mem_natRealIoc_iff (mul_nonneg hJ'0 hM'0)]
  rw [mem_primeRealIcc_iff hJ'0] at hp
  rw [mem_natRealIoc_iff hM'0] at hn
  push_cast
  constructor
  · nlinarith
  · exact mul_le_mul hp.2.1 hn.2 (Nat.cast_nonneg n) hJ'0

/-! ## The exact weights and quadratic forms -/

def negativeDirichletPhase (n : ℕ) (g : ℝ) : ℂ :=
  dirichletPhase n (-g)

def sigmaCoefficient (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * (Real.rpow (n : ℝ) (-σ) : ℂ)

def sourceQuadratic (a : ℕ → ℂ) (M M' σ : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (natRealIoc M M') G
    (sigmaCoefficient a σ) negativeDirichletPhase

def primeReciprocalSum (J J' σ : ℝ) : ℝ :=
  ∑ p ∈ primeRealIcc J J', Real.rpow (p : ℝ) (-2 * σ)

/-- The source coefficient `A(l)=sum_{pn=l}|a_n|`, with both factor ranges
spelled out rather than hidden in a divisor convention. -/
def collectedAbsoluteCoefficient
    (a : ℕ → ℂ) (J J' M M' : ℝ) (l : ℕ) : ℝ :=
  ∑ q ∈ (primeRealIcc J J').product (natRealIoc M M') with
    q.1 * q.2 = l, ‖a q.2‖

def targetQuadratic
    (a : ℕ → ℂ) (J J' M M' σ : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (productRealIoc J J' M M') G
    (fun l => ((collectedAbsoluteCoefficient a J J' M M' l *
      Real.rpow (l : ℝ) (-σ) : ℝ) : ℂ)) negativeDirichletPhase

/-! ## Parseval on `[0,1]` -/

def natTrigPoly (s : Finset ℕ) (c : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ s, c n * @fourier (1 : ℝ) (n : ℤ) (α : AddCircle (1 : ℝ))

private theorem fourierCoeffOn_zero (k : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (0 : ℝ → ℂ) k = 0 := by
  unfold fourierCoeffOn fourierCoeff
  apply integral_eq_zero_of_ae
  filter_upwards with t
  simp [AddCircle.liftIoc]

private theorem fourierCoeffOn_const_nonzero
    (c : ℂ) (k : ℤ) (hk : k ≠ 0) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1)
      (fun _ : ℝ => c) k = 0 := by
  rw [fourierCoeffOn_of_hasDerivAt (by norm_num) hk
    (f' := fun _ : ℝ => (0 : ℂ))]
  · rw [show (fun _ : ℝ => (0 : ℂ)) = 0 by rfl,
      fourierCoeffOn_zero]
    simp
  · intro x hx
    simpa using (hasDerivAt_const x c)
  · exact intervalIntegrable_const

private theorem intervalIntegral_fourier (k : ℤ) :
    (∫ α in (0 : ℝ)..1,
      @fourier (1 : ℝ) k (α : AddCircle (1 : ℝ))) =
        if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst k
    simp
  · have hcoeff := fourierCoeffOn_const_nonzero
      (1 : ℂ) (-k) (neg_ne_zero.mpr hk)
    rw [fourierCoeffOn_eq_integral] at hcoeff
    norm_num [smul_eq_mul] at hcoeff
    rw [if_neg hk]
    convert hcoeff using 1
    apply intervalIntegral.integral_congr
    intro α hα
    dsimp only
    rw [fourier_coe_apply]
    norm_num

theorem parseval_natTrigPoly (s : Finset ℕ) (c : ℕ → ℂ) :
    (∫ α in (0 : ℝ)..1, ‖natTrigPoly s c α‖ ^ 2) =
      ∑ n ∈ s, ‖c n‖ ^ 2 := by
  have hcomplex :
      (∫ α in (0 : ℝ)..1,
        natTrigPoly s c α * star (natTrigPoly s c α)) =
          (∑ n ∈ s, ‖c n‖ ^ 2 : ℝ) := by
    have hexpand (α : ℝ) :
        natTrigPoly s c α * star (natTrigPoly s c α) =
          ∑ n ∈ s, ∑ m ∈ s,
            (c n * star (c m)) *
              @fourier (1 : ℝ) ((n : ℤ) - (m : ℤ))
                (α : AddCircle (1 : ℝ)) := by
      unfold natTrigPoly
      rw [star_sum]
      simp_rw [star_mul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hstar :
          star (@fourier (1 : ℝ) (m : ℤ) (α : AddCircle (1 : ℝ))) =
            @fourier (1 : ℝ) (-(m : ℤ)) (α : AddCircle (1 : ℝ)) := by
        change conj (@fourier (1 : ℝ) (m : ℤ)
          (α : AddCircle (1 : ℝ))) = _
        exact fourier_neg.symm
      rw [hstar]
      calc
        _ = (c n * star (c m)) *
            (@fourier (1 : ℝ) (n : ℤ) (α : AddCircle (1 : ℝ)) *
              @fourier (1 : ℝ) (-(m : ℤ))
                (α : AddCircle (1 : ℝ))) := by ring
        _ = _ := by rw [← fourier_add]; congr 2
    rw [intervalIntegral.integral_congr (fun α hα => hexpand α)]
    rw [intervalIntegral.integral_finsetSum]
    · push_cast
      apply Finset.sum_congr rfl
      intro n hn
      rw [intervalIntegral.integral_finsetSum]
      · simp_rw [intervalIntegral.integral_const_mul,
          intervalIntegral_fourier]
        simp [sub_eq_zero, hn, Complex.mul_conj, ← Complex.sq_norm]
      · intro m hm
        apply Continuous.intervalIntegrable
        fun_prop
    · intro n hn
      apply Continuous.intervalIntegrable
      fun_prop
  have hpoint :
      (fun α : ℝ => natTrigPoly s c α * star (natTrigPoly s c α)) =
        fun α : ℝ => ((‖natTrigPoly s c α‖ ^ 2 : ℝ) : ℂ) := by
    funext α
    change natTrigPoly s c α * conj (natTrigPoly s c α) = _
    rw [Complex.mul_conj, ← Complex.sq_norm]
  rw [hpoint, intervalIntegral.integral_ofReal] at hcomplex
  exact Complex.ofReal_injective hcomplex

def primeFourierPolynomial
    (J J' σ g₁ g₂ α : ℝ) : ℂ :=
  natTrigPoly (primeRealIcc J J')
    (fun p => (Real.rpow (p : ℝ) (-σ) : ℂ) *
      negativeDirichletPhase p g₁ * star (negativeDirichletPhase p g₂)) α

theorem prime_parseval
    {J J' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (σ g₁ g₂ : ℝ) :
    (∫ α in (0 : ℝ)..1, ‖primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2) =
      primeReciprocalSum J J' σ := by
  unfold primeFourierPolynomial
  rw [parseval_natTrigPoly]
  unfold primeReciprocalSum
  apply Finset.sum_congr rfl
  intro p hp
  have hJ'0 : 0 ≤ J' := le_trans (by linarith) hJ'
  have hp' := (mem_primeRealIcc_iff hJ'0).mp hp
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [norm_mul, norm_mul, norm_star]
  have hphase (g : ℝ) : ‖negativeDirichletPhase p g‖ = 1 := by
    unfold negativeDirichletPhase dirichletPhase
    simpa using
      Complex.norm_exp_ofReal_mul_I (-g * Real.log (p : ℝ))
  rw [hphase, hphase]
  simp only [mul_one, Complex.norm_real, Real.norm_eq_abs]
  have habs : |Real.rpow (p : ℝ) (-σ)| = Real.rpow (p : ℝ) (-σ) :=
    abs_of_nonneg (Real.rpow_nonneg hp0 _)
  rw [habs]
  rw [show -2 * σ = (-σ) * (2 : ℕ) by ring]
  exact (Real.rpow_mul_natCast hp0 (-σ) 2).symm

/-! ## Exact product collection and coefficient majorization -/

def collectedFourierCoefficient
    (a : ℕ → ℂ) (J J' M M' α : ℝ) (l : ℕ) : ℂ :=
  ∑ q ∈ (primeRealIcc J J').product (natRealIoc M M') with
    q.1 * q.2 = l,
      a q.2 * @fourier (1 : ℝ) (q.1 : ℤ) (α : AddCircle (1 : ℝ))

theorem collectedFourierCoefficient_norm_le
    (a : ℕ → ℂ) (J J' M M' α : ℝ) (l : ℕ) :
    ‖collectedFourierCoefficient a J J' M M' α l‖ ≤
      collectedAbsoluteCoefficient a J J' M M' l := by
  unfold collectedFourierCoefficient collectedAbsoluteCoefficient
  calc
    ‖∑ q ∈ (primeRealIcc J J').product (natRealIoc M M') with
        q.1 * q.2 = l,
          a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
            (α : AddCircle (1 : ℝ))‖ ≤
      ∑ q ∈ (primeRealIcc J J').product (natRealIoc M M') with
        q.1 * q.2 = l,
          ‖a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
            (α : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]

theorem sigmaCoefficient_norm_le_collected
    (a : ℕ → ℂ) (J J' M M' σ α : ℝ) (l : ℕ) :
    ‖collectedFourierCoefficient a J J' M M' α l *
        (Real.rpow (l : ℝ) (-σ) : ℂ)‖ ≤
      collectedAbsoluteCoefficient a J J' M M' l *
        Real.rpow (l : ℝ) (-σ) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have habs : |Real.rpow (l : ℝ) (-σ)| = Real.rpow (l : ℝ) (-σ) :=
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg l) _)
  rw [habs]
  exact mul_le_mul_of_nonneg_right
    (collectedFourierCoefficient_norm_le a J J' M M' α l)
    (Real.rpow_nonneg (Nat.cast_nonneg l) _)

theorem negativeDirichletPhase_mul
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (g : ℝ) :
    negativeDirichletPhase (n * p) g =
      negativeDirichletPhase n g * negativeDirichletPhase p g := by
  unfold negativeDirichletPhase dirichletPhase
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Nat.cast_mul, Real.log_mul hnR hpR, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem weighted_monomial_mul
    {n p : ℕ} (hn : 0 < n) (hp : 0 < p) (σ g₁ g₂ : ℝ) :
    (sigmaCoefficient (fun _ => (1 : ℂ)) σ n *
        negativeDirichletPhase n g₁ * star (negativeDirichletPhase n g₂)) *
      ((Real.rpow (p : ℝ) (-σ) : ℂ) *
        negativeDirichletPhase p g₁ * star (negativeDirichletPhase p g₂)) =
      (Real.rpow (n * p : ℕ) (-σ) : ℂ) *
        negativeDirichletPhase (n * p) g₁ *
          star (negativeDirichletPhase (n * p) g₂) := by
  unfold sigmaCoefficient
  simp only [one_mul]
  rw [Nat.cast_mul]
  have hrpow := Real.mul_rpow
    (z := -σ) (Nat.cast_nonneg n) (Nat.cast_nonneg p)
  have hrpowC :
      (Real.rpow ((n : ℝ) * (p : ℝ)) (-σ) : ℂ) =
        (Real.rpow (n : ℝ) (-σ) : ℂ) *
          (Real.rpow (p : ℝ) (-σ) : ℂ) := by
    exact_mod_cast hrpow
  rw [hrpowC, negativeDirichletPhase_mul hn hp,
    negativeDirichletPhase_mul hn hp, star_mul]
  ring

def sourcePolynomial
    (a : ℕ → ℂ) (M M' σ g₁ g₂ : ℝ) : ℂ :=
  gramPolynomial (natRealIoc M M') (sigmaCoefficient a σ)
    negativeDirichletPhase g₁ g₂

def pairSummand (a : ℕ → ℂ) (σ g₁ g₂ α : ℝ)
    (q : ℕ × ℕ) : ℂ :=
  (a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
      (α : AddCircle (1 : ℝ))) *
    (Real.rpow (q.1 * q.2 : ℕ) (-σ) : ℂ) *
      negativeDirichletPhase (q.1 * q.2) g₁ *
        star (negativeDirichletPhase (q.1 * q.2) g₂)

theorem source_mul_prime_eq_pairSum
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ g₁ g₂ α : ℝ) :
    sourcePolynomial a M M' σ g₁ g₂ *
        primeFourierPolynomial J J' σ g₁ g₂ α =
      ∑ q ∈ (primeRealIcc J J').product (natRealIoc M M'),
        pairSummand a σ g₁ g₂ α q := by
  unfold sourcePolynomial primeFourierPolynomial gramPolynomial natTrigPoly
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  change _ = ∑ q ∈ primeRealIcc J J' ×ˢ natRealIoc M M',
    pairSummand a σ g₁ g₂ α q
  rw [Finset.sum_product (primeRealIcc J J') (natRealIoc M M')
    (pairSummand a σ g₁ g₂ α)]
  apply Finset.sum_congr rfl
  intro p hpMem
  apply Finset.sum_congr rfl
  intro n hnMem
  let q : ℕ × ℕ := (p, n)
  have hq' : q.1 ∈ primeRealIcc J J' ∧ q.2 ∈ natRealIoc M M' :=
    ⟨hpMem, hnMem⟩
  have hJ'0 : 0 ≤ J' := le_trans (by linarith) hJ'
  have hM'0 : 0 ≤ M' := hM.trans hM'.le
  have hpRange := (mem_primeRealIcc_iff hJ'0).mp hq'.1
  have hnRange := (mem_natRealIoc_iff hM'0).mp hq'.2
  have hp : 0 < q.1 := hpRange.2.2.pos
  have hn : 0 < q.2 := by
    exact_mod_cast (lt_of_le_of_lt hM hnRange.1)
  have hmono := weighted_monomial_mul hn hp σ g₁ g₂
  unfold pairSummand
  unfold sigmaCoefficient at hmono
  simp only [one_mul] at hmono
  calc
    (sigmaCoefficient a σ q.2 * negativeDirichletPhase q.2 g₁ *
          star (negativeDirichletPhase q.2 g₂)) *
        ((Real.rpow (q.1 : ℝ) (-σ) : ℂ) *
            negativeDirichletPhase q.1 g₁ *
              star (negativeDirichletPhase q.1 g₂) *
          @fourier (1 : ℝ) (q.1 : ℤ) (α : AddCircle (1 : ℝ))) =
      a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
          (α : AddCircle (1 : ℝ)) *
        ((Real.rpow (q.2 : ℝ) (-σ) : ℂ) *
            negativeDirichletPhase q.2 g₁ *
              star (negativeDirichletPhase q.2 g₂) *
          ((Real.rpow (q.1 : ℝ) (-σ) : ℂ) *
            negativeDirichletPhase q.1 g₁ *
              star (negativeDirichletPhase q.1 g₂))) := by
        unfold sigmaCoefficient
        ring
    _ = a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
          (α : AddCircle (1 : ℝ)) *
        ((Real.rpow (q.2 * q.1 : ℕ) (-σ) : ℂ) *
          negativeDirichletPhase (q.2 * q.1) g₁ *
            star (negativeDirichletPhase (q.2 * q.1) g₂)) := by
        rw [hmono]
    _ = _ := by
      rw [Nat.mul_comm q.2 q.1]
      dsimp [q]
      ring

theorem pairSum_eq_collectedPolynomial
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ g₁ g₂ α : ℝ) :
    (∑ q ∈ (primeRealIcc J J').product (natRealIoc M M'),
        pairSummand a σ g₁ g₂ α q) =
      gramPolynomial (productRealIoc J J' M M')
        (fun l => collectedFourierCoefficient a J J' M M' α l *
          (Real.rpow (l : ℝ) (-σ) : ℂ))
        negativeDirichletPhase g₁ g₂ := by
  let pairs := (primeRealIcc J J').product (natRealIoc M M')
  let prodMap : ℕ × ℕ → ℕ := fun q => q.1 * q.2
  have hmaps : ∀ q ∈ pairs, prodMap q ∈ productRealIoc J J' M M' := by
    intro q hq
    have hq' : q.1 ∈ primeRealIcc J J' ∧ q.2 ∈ natRealIoc M M' := by
      simpa [pairs] using hq
    exact product_mem_productRealIoc hJ hM hJ' hM' hq'.1 hq'.2
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := pairs) (t := productRealIoc J J' M M')
    (g := prodMap) hmaps (pairSummand a σ g₁ g₂ α)
  unfold gramPolynomial collectedFourierCoefficient
  change (∑ q ∈ pairs, pairSummand a σ g₁ g₂ α q) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro l hl
  change (∑ q ∈ pairs with prodMap q = l,
      pairSummand a σ g₁ g₂ α q) =
    ((∑ q ∈ pairs with prodMap q = l,
        a q.2 * @fourier (1 : ℝ) (q.1 : ℤ)
          (α : AddCircle (1 : ℝ))) *
      (Real.rpow (l : ℝ) (-σ) : ℂ)) *
        negativeDirichletPhase l g₁ *
          star (negativeDirichletPhase l g₂)
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  have hprod : prodMap q = l := (Finset.mem_filter.mp hq).2
  change q.1 * q.2 = l at hprod
  unfold pairSummand
  rw [hprod]

theorem product_collection_identity
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ g₁ g₂ α : ℝ) :
    sourcePolynomial a M M' σ g₁ g₂ *
        primeFourierPolynomial J J' σ g₁ g₂ α =
      gramPolynomial (productRealIoc J J' M M')
        (fun l => collectedFourierCoefficient a J J' M M' α l *
          (Real.rpow (l : ℝ) (-σ) : ℂ))
        negativeDirichletPhase g₁ g₂ := by
  rw [source_mul_prime_eq_pairSum hJ hJ' hM hM',
    pairSum_eq_collectedPolynomial hJ hJ' hM hM']

/-! ## The two evaluations and Lemma 29.7 -/

def transferenceIntegrand
    (a : ℕ → ℂ) (J J' M M' σ : ℝ) (G : Finset ℝ) (α : ℝ) : ℝ :=
  ∑ g₁ ∈ G, ∑ g₂ ∈ G,
    ‖sourcePolynomial a M M' σ g₁ g₂ *
      primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2

theorem scaled_prime_parseval
    {J J' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (σ g₁ g₂ : ℝ) (c : ℂ) :
    (∫ α in (0 : ℝ)..1,
      ‖c * primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2) =
        ‖c‖ ^ 2 * primeReciprocalSum J J' σ := by
  calc
    (∫ α in (0 : ℝ)..1,
        ‖c * primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2) =
      ∫ α in (0 : ℝ)..1,
        ‖c‖ ^ 2 * ‖primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2 := by
          apply intervalIntegral.integral_congr
          intro α hα
          change ‖c * primeFourierPolynomial J J' σ g₁ g₂ α‖ ^ 2 = _
          rw [norm_mul]
          ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        prime_parseval hJ hJ' σ g₁ g₂]

/-- First evaluation of the source integral: Parseval in the prime
frequency gives exactly the reciprocal-prime normalization. -/
theorem transferenceIntegral_eq_source_mul_primeReciprocal
    {J J' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (a : ℕ → ℂ) (M M' σ : ℝ) (G : Finset ℝ) :
    (∫ α in (0 : ℝ)..1,
      transferenceIntegrand a J J' M M' σ G α) =
        sourceQuadratic a M M' σ G * primeReciprocalSum J J' σ := by
  unfold transferenceIntegrand sourceQuadratic realGramQuadratic
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro g₁ hg₁
    rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro g₂ hg₂
      exact scaled_prime_parseval hJ hJ' σ g₁ g₂
        (sourcePolynomial a M M' σ g₁ g₂)
    · intro g₂ hg₂
      apply Continuous.intervalIntegrable
      unfold primeFourierPolynomial natTrigPoly
      fun_prop
  · intro g₁ hg₁
    apply Continuous.intervalIntegrable
    unfold primeFourierPolynomial natTrigPoly
    fun_prop

/-- Second evaluation: after collecting the products `pn=l`, the same
integrand is the finite Gram quadratic with the exact Fourier-dependent
fiber coefficient. -/
theorem transferenceIntegrand_eq_collectedQuadratic
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ : ℝ) (G : Finset ℝ) (α : ℝ) :
    transferenceIntegrand a J J' M M' σ G α =
      realGramQuadratic (productRealIoc J J' M M') G
        (fun l => collectedFourierCoefficient a J J' M M' α l *
          (Real.rpow (l : ℝ) (-σ) : ℂ)) negativeDirichletPhase := by
  unfold transferenceIntegrand realGramQuadratic
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  apply Finset.sum_congr rfl
  intro g₂ hg₂
  rw [product_collection_identity hJ hJ' hM hM']

theorem transferenceIntegrand_le_target
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ : ℝ) (G : Finset ℝ) (α : ℝ) :
    transferenceIntegrand a J J' M M' σ G α ≤
      targetQuadratic a J J' M M' σ G := by
  rw [transferenceIntegrand_eq_collectedQuadratic hJ hJ' hM hM']
  unfold targetQuadratic
  exact gram_majorant_principle
    (productRealIoc J J' M M') G
    (fun l => collectedFourierCoefficient a J J' M M' α l *
      (Real.rpow (l : ℝ) (-σ) : ℂ))
    (fun l => collectedAbsoluteCoefficient a J J' M M' l *
      Real.rpow (l : ℝ) (-σ)) negativeDirichletPhase
    (fun l hl => sigmaCoefficient_norm_le_collected
      a J J' M M' σ α l)

theorem source_mul_primeReciprocal_le_target
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ : ℝ) (G : Finset ℝ) :
    sourceQuadratic a M M' σ G * primeReciprocalSum J J' σ ≤
      targetQuadratic a J J' M M' σ G := by
  rw [← transferenceIntegral_eq_source_mul_primeReciprocal hJ hJ']
  calc
    (∫ α in (0 : ℝ)..1,
        transferenceIntegrand a J J' M M' σ G α) ≤
      ∫ _α in (0 : ℝ)..1, targetQuadratic a J J' M M' σ G := by
        apply intervalIntegral.integral_mono_on (by norm_num)
        · apply Continuous.intervalIntegrable
          unfold transferenceIntegrand primeFourierPolynomial natTrigPoly
          fun_prop
        · exact intervalIntegral.intervalIntegrable_const
        · intro α hα
          exact transferenceIntegrand_le_target hJ hJ' hM hM' a σ G α
    _ = targetQuadratic a J J' M M' σ G := by
      rw [intervalIntegral.integral_const]
      norm_num

theorem primeReciprocalSum_pos
    {J J' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (σ : ℝ) (hprime : (primeRealIcc J J').Nonempty) :
    0 < primeReciprocalSum J J' σ := by
  obtain ⟨p, hp⟩ := hprime
  have hJ'0 : 0 ≤ J' := le_trans (by linarith) hJ'
  have hpData := (mem_primeRealIcc_iff hJ'0).mp hp
  unfold primeReciprocalSum
  apply Finset.sum_pos'
  · intro q hq
    exact Real.rpow_nonneg (Nat.cast_nonneg q) _
  · exact ⟨p, hp, Real.rpow_pos_of_pos (by exact_mod_cast hpData.2.2.pos) _⟩

/-- Lemma 29.7, with no analytic premise: the only hypothesis beyond the
literal endpoint assumptions is that the finite prime interval is nonempty. -/
theorem jutila_transference
    {J J' M M' : ℝ} (hJ : 2 ≤ J) (hJ' : J ≤ J')
    (hM : 0 ≤ M) (hM' : M < M')
    (a : ℕ → ℂ) (σ : ℝ) (G : Finset ℝ)
    (hprime : (primeRealIcc J J').Nonempty) :
    sourceQuadratic a M M' σ G ≤
      (primeReciprocalSum J J' σ)⁻¹ *
        targetQuadratic a J J' M M' σ G := by
  have hpos := primeReciprocalSum_pos hJ hJ' σ hprime
  have hmain := source_mul_primeReciprocal_le_target
    hJ hJ' hM hM' a σ G
  calc
    sourceQuadratic a M M' σ G =
        (primeReciprocalSum J J' σ)⁻¹ *
          (sourceQuadratic a M M' σ G *
            primeReciprocalSum J J' σ) := by
      field_simp [hpos.ne']
    _ ≤ (primeReciprocalSum J J' σ)⁻¹ *
          targetQuadratic a J J' M M' σ G :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hpos.le)

end

end GuthMaynardJutilaTransference

#print axioms GuthMaynardJutilaTransference.parseval_natTrigPoly
#print axioms GuthMaynardJutilaTransference.prime_parseval
#print axioms GuthMaynardJutilaTransference.collectedFourierCoefficient_norm_le
#print axioms GuthMaynardJutilaTransference.product_collection_identity
#print axioms GuthMaynardJutilaTransference.transferenceIntegral_eq_source_mul_primeReciprocal
#print axioms GuthMaynardJutilaTransference.transferenceIntegrand_eq_collectedQuadratic
#print axioms GuthMaynardJutilaTransference.jutila_transference
