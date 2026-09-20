import GuthMaynardLengthComparison

/-!
# The deterministic `k = 2` powering step in Lemma 29.9

At the start of the proof of Lemma 29.9 the coefficient-one Dirichlet
polynomial on the literal interval `N < n ≤ 2N` is squared.  Its collected
coefficient at `n` is the number of ordered pairs `(m₁,m₂)` in that interval
with `m₁m₂ = n`, and every such product lies in `N² < n ≤ 4N²`.

This file certifies that finite convolution identity and the preceding finite
Hölder (for `k = 2`, Cauchy--Schwarz) step.  It stops before the analytic
transference estimate used on the resulting quadratic form.
-/

namespace GuthMaynardPoweringKTwo

open scoped BigOperators
open GuthMaynardHeathBrownMajorant
open GuthMaynardLengthComparison

noncomputable section

/-! ## The exact product interval and actual multiplicity -/

/-- The natural numbers in the literal product interval `(N²,4N²]`. -/
def productIoc (N : ℝ) : Finset ℕ :=
  (Finset.range (Nat.ceil (4 * N ^ 2) + 1)).filter
    (fun n => N ^ 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * N ^ 2)

@[simp]
theorem mem_productIoc_iff {N : ℝ} {n : ℕ} :
    n ∈ productIoc N ↔ N ^ 2 < (n : ℝ) ∧ (n : ℝ) ≤ 4 * N ^ 2 := by
  constructor
  · intro hn
    exact (Finset.mem_filter.mp hn).2
  · intro hn
    apply Finset.mem_filter.mpr
    refine ⟨?_, hn⟩
    have hnceilR : (n : ℝ) ≤ (Nat.ceil (4 * N ^ 2) : ℝ) :=
      hn.2.trans (Nat.le_ceil (4 * N ^ 2))
    have hnceil : n ≤ Nat.ceil (4 * N ^ 2) := by
      exact_mod_cast hnceilR
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hnceil)

/-- The literal coefficient
`aₙ = #{(m₁,m₂) : m₁m₂=n, N<mⱼ≤2N}` from Lemma 29.9 for `k=2`.
The pairs are ordered, as they are in the expansion of a square. -/
def productMultiplicity (N : ℝ) (n : ℕ) : ℕ :=
  ((realDyadicIoc N).product (realDyadicIoc N)).filter
    (fun p => p.1 * p.2 = n) |>.card

/-- Positivity of `aₙ` is exactly the existence of an ordered factorization
with both factors in `(N,2N]`. -/
theorem productMultiplicity_pos_iff {N : ℝ} {n : ℕ} :
    0 < productMultiplicity N n ↔
      ∃ m₁ ∈ realDyadicIoc N, ∃ m₂ ∈ realDyadicIoc N, m₁ * m₂ = n := by
  unfold productMultiplicity
  rw [Finset.card_pos]
  constructor
  · rintro ⟨p, hp⟩
    have hp' := Finset.mem_filter.mp hp
    have hpmem :
        p.1 ∈ realDyadicIoc N ∧ p.2 ∈ realDyadicIoc N := by
      simpa using hp'.1
    exact ⟨p.1, hpmem.1, p.2, hpmem.2, hp'.2⟩
  · rintro ⟨m₁, hm₁, m₂, hm₂, hprod⟩
    refine ⟨(m₁, m₂), Finset.mem_filter.mpr ⟨?_, hprod⟩⟩
    simpa using And.intro hm₁ hm₂

/-- Every product occurring in the square belongs to the exact interval
`(N²,4N²]`. -/
theorem product_mem_productIoc {N : ℝ} (hN : 0 ≤ N)
    {m₁ m₂ : ℕ} (hm₁ : m₁ ∈ realDyadicIoc N)
    (hm₂ : m₂ ∈ realDyadicIoc N) :
    m₁ * m₂ ∈ productIoc N := by
  rw [mem_productIoc_iff]
  rw [mem_realDyadicIoc_iff] at hm₁ hm₂
  push_cast
  constructor <;> nlinarith

/-- The support of the actual coefficient is contained in the literal
product interval, with both endpoint conventions exposed. -/
theorem productMultiplicity_pos_implies_mem_productIoc
    {N : ℝ} (hN : 0 ≤ N) {n : ℕ}
    (hn : 0 < productMultiplicity N n) :
    n ∈ productIoc N := by
  obtain ⟨m₁, hm₁, m₂, hm₂, hprod⟩ :=
    productMultiplicity_pos_iff.mp hn
  rw [← hprod]
  exact product_mem_productIoc hN hm₁ hm₂

/-- Outside `(N²,4N²]` the actual product multiplicity is zero. -/
theorem productMultiplicity_eq_zero_of_not_mem {N : ℝ} (hN : 0 ≤ N)
    {n : ℕ} (hn : n ∉ productIoc N) :
    productMultiplicity N n = 0 := by
  rw [productMultiplicity, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro p hp hprod
  have hp' : p.1 ∈ realDyadicIoc N ∧ p.2 ∈ realDyadicIoc N := by
    simpa using hp
  apply hn
  simpa [hprod] using product_mem_productIoc hN hp'.1 hp'.2

/-- The exact finite maximum `A₂(N)` of the product multiplicities. -/
def maxProductMultiplicity (N : ℝ) : ℕ :=
  (productIoc N).sup (productMultiplicity N)

/-- Every coefficient inside the exact product interval is bounded by
`A₂(N)`. -/
theorem productMultiplicity_le_maxProductMultiplicity_of_mem
    {N : ℝ} {n : ℕ} (hn : n ∈ productIoc N) :
    productMultiplicity N n ≤ maxProductMultiplicity N := by
  exact Finset.le_sup hn

/-- When `N ≥ 0`, `A₂(N)` bounds every natural-index coefficient: outside
the product interval the coefficient is exactly zero. -/
theorem productMultiplicity_le_maxProductMultiplicity
    {N : ℝ} (hN : 0 ≤ N) (n : ℕ) :
    productMultiplicity N n ≤ maxProductMultiplicity N := by
  by_cases hn : n ∈ productIoc N
  · exact productMultiplicity_le_maxProductMultiplicity_of_mem hn
  · rw [productMultiplicity_eq_zero_of_not_mem hN hn]
    exact Nat.zero_le _

/-! ## The source Dirichlet monomial and its multiplicativity -/

/-- The literal monomial `n^(-1/2-i(g₁-g₂))`, with the real power written as
the inverse square-root weight already used in `jutilaSecondMoment`. -/
def poweringMonomial (n : ℕ) (g₁ g₂ : ℝ) : ℂ :=
  (inverseSqrtWeight n : ℂ) *
    Complex.exp
      (Complex.I * ((((g₂ - g₁) * Real.log n : ℝ) : ℂ)))

/-- The coefficient-one inner polynomial on the exact interval `(N,2N]`. -/
def poweringInner (N : ℝ) (g₁ g₂ : ℝ) : ℂ :=
  ∑ n ∈ realDyadicIoc N, poweringMonomial n g₁ g₂

/-- The powered polynomial, collected with the actual product multiplicity on
the exact interval `(N²,4N²]`. -/
def collectedPoweringInner (N : ℝ) (g₁ g₂ : ℝ) : ℂ :=
  ∑ n ∈ productIoc N,
    (productMultiplicity N n : ℂ) * poweringMonomial n g₁ g₂

/-- `poweringInner` is exactly the source-oriented (`-i(g₁-g₂)`) instance of
the existing Gram polynomial. -/
theorem poweringInner_eq_gramPolynomial (N : ℝ) (g₁ g₂ : ℝ) :
    poweringInner N g₁ g₂ =
      gramPolynomial (realDyadicIoc N)
        (fun n => (inverseSqrtWeight n : ℂ)) dirichletPhase g₂ g₁ := by
  unfold poweringInner gramPolynomial poweringMonomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, dirichletPhase_difference]
  push_cast
  ring_nf

/-- Multiplication of two positive source monomials combines their indices by
multiplication. -/
theorem poweringMonomial_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (g₁ g₂ : ℝ) :
    poweringMonomial m g₁ g₂ * poweringMonomial n g₁ g₂ =
      poweringMonomial (m * n) g₁ g₂ := by
  rw [poweringMonomial, poweringMonomial, poweringMonomial,
    inverseSqrtWeight_mul]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_mul, Real.log_mul hmR hnR]
  calc
    (inverseSqrtWeight m : ℂ) *
          Complex.exp (Complex.I * ↑((g₂ - g₁) * Real.log ↑m)) *
        ((inverseSqrtWeight n : ℂ) *
          Complex.exp (Complex.I * ↑((g₂ - g₁) * Real.log ↑n))) =
        ((inverseSqrtWeight m : ℂ) * (inverseSqrtWeight n : ℂ)) *
          (Complex.exp (Complex.I * ↑((g₂ - g₁) * Real.log ↑m)) *
            Complex.exp (Complex.I * ↑((g₂ - g₁) * Real.log ↑n))) := by ring_nf
    _ = ((inverseSqrtWeight m : ℂ) * (inverseSqrtWeight n : ℂ)) *
          Complex.exp
            (Complex.I * ↑((g₂ - g₁) * Real.log ↑m) +
              Complex.I * ↑((g₂ - g₁) * Real.log ↑n)) := by
      rw [Complex.exp_add]
    _ = ↑(inverseSqrtWeight m * inverseSqrtWeight n) *
          Complex.exp
            (Complex.I * ↑((g₂ - g₁) * (Real.log ↑m + Real.log ↑n))) := by
      push_cast
      ring_nf

/-! ## Squaring and collecting the convolution -/

/-- Expanding the square gives the ordered product-pair sum, before equal
products are collected. -/
theorem poweringInner_sq_eq_pairSum (N : ℝ) (g₁ g₂ : ℝ) :
    poweringInner N g₁ g₂ ^ 2 =
      ∑ p ∈ (realDyadicIoc N).product (realDyadicIoc N),
        poweringMonomial (p.1 * p.2) g₁ g₂ := by
  unfold poweringInner
  calc
    (∑ n ∈ realDyadicIoc N, poweringMonomial n g₁ g₂) ^ 2 =
        (∑ m ∈ realDyadicIoc N, poweringMonomial m g₁ g₂) *
          ∑ n ∈ realDyadicIoc N, poweringMonomial n g₁ g₂ := by
      rw [pow_two]
    _ = ∑ m ∈ realDyadicIoc N, ∑ n ∈ realDyadicIoc N,
          poweringMonomial m g₁ g₂ * poweringMonomial n g₁ g₂ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ = ∑ m ∈ realDyadicIoc N, ∑ n ∈ realDyadicIoc N,
          poweringMonomial (m * n) g₁ g₂ := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact poweringMonomial_mul
        (pos_of_mem_realDyadicIoc hm) (pos_of_mem_realDyadicIoc hn) g₁ g₂
    _ = ∑ p ∈ (realDyadicIoc N).product (realDyadicIoc N),
          poweringMonomial (p.1 * p.2) g₁ g₂ := by
      exact (Finset.sum_product (realDyadicIoc N) (realDyadicIoc N)
        (fun p => poweringMonomial (p.1 * p.2) g₁ g₂)).symm

/-- Grouping the product-pair sum by its product gives exactly the displayed
coefficient `aₙ`, with no coefficient majorization. -/
theorem pairSum_eq_collectedPoweringInner (N : ℝ) (hN : 0 ≤ N)
    (g₁ g₂ : ℝ) :
    (∑ p ∈ (realDyadicIoc N).product (realDyadicIoc N),
        poweringMonomial (p.1 * p.2) g₁ g₂) =
      collectedPoweringInner N g₁ g₂ := by
  let pairs := (realDyadicIoc N).product (realDyadicIoc N)
  let prodMap : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  have hmaps : ∀ p ∈ pairs, prodMap p ∈ productIoc N := by
    intro p hp
    have hp' : p.1 ∈ realDyadicIoc N ∧ p.2 ∈ realDyadicIoc N := by
      simpa [pairs] using hp
    exact product_mem_productIoc hN hp'.1 hp'.2
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := pairs) (t := productIoc N) (g := prodMap) hmaps
    (fun p => poweringMonomial (prodMap p) g₁ g₂)
  unfold collectedPoweringInner productMultiplicity
  change (∑ p ∈ pairs, poweringMonomial (prodMap p) g₁ g₂) = _
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro n hn
  change (∑ p ∈ pairs with prodMap p = n,
      poweringMonomial (prodMap p) g₁ g₂) =
    (((pairs.filter fun p => prodMap p = n).card : ℕ) : ℂ) *
      poweringMonomial n g₁ g₂
  calc
    (∑ p ∈ pairs with prodMap p = n,
        poweringMonomial (prodMap p) g₁ g₂) =
        ∑ _p ∈ pairs.filter (fun p => prodMap p = n),
          poweringMonomial n g₁ g₂ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hprod : prodMap p = n := (Finset.mem_filter.mp hp).2
      rw [hprod]
    _ = (((pairs.filter fun p => prodMap p = n).card : ℕ) : ℂ) *
          poweringMonomial n g₁ g₂ := by
      simp

/-- Exact square/product-convolution identity for the inner polynomial. -/
theorem poweringInner_sq_eq_collectedPoweringInner
    (N : ℝ) (hN : 0 ≤ N) (g₁ g₂ : ℝ) :
    poweringInner N g₁ g₂ ^ 2 = collectedPoweringInner N g₁ g₂ := by
  rw [poweringInner_sq_eq_pairSum,
    pairSum_eq_collectedPoweringInner N hN]

/-! ## The exact finite Hölder/cardinality factor -/

/-- `S(N)` written over the literal ordered-pair set `G²`. -/
def poweringSecondMoment (N : ℝ) (G : Finset ℝ) : ℝ :=
  ∑ g ∈ G.product G, ‖poweringInner N g.1 g.2‖ ^ 2

/-- The quadratic form after the square has been collected with coefficient
`aₙ = productMultiplicity N n`. -/
def multiplicityQuadraticForm (N : ℝ) (G : Finset ℝ) : ℝ :=
  ∑ g ∈ G.product G, ‖collectedPoweringInner N g.1 g.2‖ ^ 2

/-- The source-oriented presentation of `S(N)` is the existing
`jutilaSecondMoment`; the reversal of the two ordinates only reindexes `G²`. -/
theorem poweringSecondMoment_eq_jutilaSecondMoment
    (N : ℝ) (G : Finset ℝ) :
    poweringSecondMoment N G = jutilaSecondMoment N G := by
  unfold poweringSecondMoment jutilaSecondMoment realGramQuadratic
  calc
    (∑ g ∈ G.product G, ‖poweringInner N g.1 g.2‖ ^ 2) =
        ∑ g₁ ∈ G, ∑ g₂ ∈ G, ‖poweringInner N g₁ g₂‖ ^ 2 := by
      exact Finset.sum_product G G
        (fun g => ‖poweringInner N g.1 g.2‖ ^ 2)
    _ = ∑ g₁ ∈ G, ∑ g₂ ∈ G,
          ‖gramPolynomial (realDyadicIoc N)
            (fun n => (inverseSqrtWeight n : ℂ))
              dirichletPhase g₂ g₁‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro g₁ hg₁
      apply Finset.sum_congr rfl
      intro g₂ hg₂
      rw [poweringInner_eq_gramPolynomial]
    _ = ∑ g₂ ∈ G, ∑ g₁ ∈ G,
          ‖gramPolynomial (realDyadicIoc N)
            (fun n => (inverseSqrtWeight n : ℂ))
              dirichletPhase g₂ g₁‖ ^ 2 := by
      exact Finset.sum_comm

/-- The finite `k=2` Hölder step, isolated from all Dirichlet-polynomial
structure.  The cardinality factor is an exact finset cardinal, not an
asymptotic estimate. -/
theorem finite_holder_kTwo {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (F : ι → ℂ) :
    (∑ x ∈ I, ‖F x‖ ^ 2) ^ 2 ≤
      (I.card : ℝ) * ∑ x ∈ I, ‖F x ^ 2‖ ^ 2 := by
  simpa only [norm_pow] using
    (sq_sum_le_card_mul_sum_sq
      (s := I) (f := fun x => ‖F x‖ ^ 2))

/-- The exact deterministic first line of Lemma 29.9 for `k=2`:

`S(N)² ≤ |G|² ∑_(g₁,g₂) |∑_(N²<n≤4N²) aₙ n^(-1/2-i(g₁-g₂))|²`.

No logarithmic loss or analytic transference theorem is used here. -/
theorem poweringSecondMoment_sq_le_multiplicityQuadraticForm
    (N : ℝ) (hN : 0 ≤ N) (G : Finset ℝ) :
    poweringSecondMoment N G ^ 2 ≤
      (G.card : ℝ) ^ 2 * multiplicityQuadraticForm N G := by
  have h := finite_holder_kTwo (G.product G)
    (fun g => poweringInner N g.1 g.2)
  simp_rw [poweringInner_sq_eq_collectedPoweringInner N hN] at h
  have hcardNat : (G.product G).card = G.card * G.card :=
    Finset.card_product G G
  have hcardReal : ((G.product G).card : ℝ) = (G.card : ℝ) ^ 2 := by
    rw [hcardNat, Nat.cast_mul, pow_two]
  rw [hcardReal] at h
  simpa only [poweringSecondMoment, multiplicityQuadraticForm] using h

/-- The same result with the project's existing name `jutilaSecondMoment` for
`S(N)`. -/
theorem jutilaSecondMoment_sq_le_multiplicityQuadraticForm
    (N : ℝ) (hN : 0 ≤ N) (G : Finset ℝ) :
    jutilaSecondMoment N G ^ 2 ≤
      (G.card : ℝ) ^ 2 * multiplicityQuadraticForm N G := by
  rw [← poweringSecondMoment_eq_jutilaSecondMoment]
  exact poweringSecondMoment_sq_le_multiplicityQuadraticForm N hN G

end

end GuthMaynardPoweringKTwo

#print axioms GuthMaynardPoweringKTwo.mem_productIoc_iff
#print axioms GuthMaynardPoweringKTwo.productMultiplicity_pos_iff
#print axioms GuthMaynardPoweringKTwo.productMultiplicity_pos_implies_mem_productIoc
#print axioms GuthMaynardPoweringKTwo.productMultiplicity_eq_zero_of_not_mem
#print axioms GuthMaynardPoweringKTwo.productMultiplicity_le_maxProductMultiplicity
#print axioms GuthMaynardPoweringKTwo.poweringInner_sq_eq_collectedPoweringInner
#print axioms GuthMaynardPoweringKTwo.poweringSecondMoment_eq_jutilaSecondMoment
#print axioms GuthMaynardPoweringKTwo.poweringSecondMoment_sq_le_multiplicityQuadraticForm
#print axioms GuthMaynardPoweringKTwo.jutilaSecondMoment_sq_le_multiplicityQuadraticForm
