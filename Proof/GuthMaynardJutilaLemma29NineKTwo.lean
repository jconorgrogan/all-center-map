import GuthMaynardJutilaTransference
import GuthMaynardPoweringKTwo
import GuthMaynardHeathBrownIccIocEndpointAdapter

/-!
# Source-facing `k=2` form of Jutila--Heath--Brown Lemma 29.9

The source first powers `S(N)`, applies Lemma 29.7 with
`M=N²`, `M'=4N²`, `J=P/(4N²)`, `J'=2P/(4N²)`, splits
`(P/4,2P]` into three dyadic blocks, and applies Lemma 29.8.
This module keeps every one of those finite losses visible.
-/

namespace GuthMaynardJutilaLemma29NineKTwo

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardLengthComparison
open GuthMaynardPoweringKTwo
open GuthMaynardHeathBrownIccIocEndpointAdapter
open GuthMaynardRatioKernelIdentity

noncomputable section

def kTwoPrimeLower (N P : ℝ) : ℝ := P / (4 * N ^ 2)

def kTwoPrimeRange (N P : ℝ) : Finset ℕ :=
  primeRealIcc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)

def kTwoProductRange (N P : ℝ) : Finset ℕ :=
  productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
    (N ^ 2) (4 * N ^ 2)

/-- The three literal dyadic blocks `(P/4,P/2]`, `(P/2,P]`, `(P,2P]`. -/
def kTwoDyadicUnion (P : ℝ) : Finset ℕ :=
  realDyadicIoc (P / 4) ∪ realDyadicIoc (P / 2) ∪ realDyadicIoc P

theorem kTwoProductRange_eq_dyadicUnion
    {N P : ℝ} (hN : 0 < N)
    (hJ : 2 ≤ kTwoPrimeLower N P) :
    kTwoProductRange N P = kTwoDyadicUnion P := by
  have hden : 0 < 4 * N ^ 2 := by positivity
  have hP : 0 < P := by
    have hmul : 2 * (4 * N ^ 2) ≤ P := by
      calc
        2 * (4 * N ^ 2) ≤ kTwoPrimeLower N P * (4 * N ^ 2) :=
          mul_le_mul_of_nonneg_right hJ hden.le
        _ = P := by
          unfold kTwoPrimeLower
          field_simp
    nlinarith
  have hlower : kTwoPrimeLower N P * N ^ 2 = P / 4 := by
    unfold kTwoPrimeLower
    field_simp [hN.ne']
  have hupper :
      (2 * kTwoPrimeLower N P) * (4 * N ^ 2) = 2 * P := by
    unfold kTwoPrimeLower
    field_simp [hN.ne']
  ext l
  simp only [kTwoProductRange, productRealIoc,
    mem_natRealIoc_iff (by positivity :
      0 ≤ (2 * kTwoPrimeLower N P) * (4 * N ^ 2)),
    kTwoDyadicUnion, Finset.mem_union,
    mem_realDyadicIoc_iff]
  rw [hlower, hupper]
  constructor
  · intro hl
    by_cases h₁ : (l : ℝ) ≤ P / 2
    · exact Or.inl (Or.inl ⟨hl.1, by linarith⟩)
    · by_cases h₂ : (l : ℝ) ≤ P
      · exact Or.inl (Or.inr ⟨lt_of_not_ge h₁, by linarith⟩)
      · exact Or.inr ⟨lt_of_not_ge h₂, hl.2⟩
  · rintro ((hl | hl) | hl)
    · constructor <;> linarith
    · constructor <;> linarith
    · constructor <;> linarith

/-- Number of admissible `(p,n)` representations of `l` in the exact
transference ranges. -/
def kTwoTransferenceFiberCard (N P : ℝ) (l : ℕ) : ℕ :=
  (((kTwoPrimeRange N P).product (productIoc N)).filter
    (fun q => q.1 * q.2 = l)).card

/-- The exact finite divisor-fiber loss.  Bounding this by logarithms is a
separate elementary number-theoretic step in the printed proof. -/
def kTwoTransferenceFiberCap (N P : ℝ) : ℕ :=
  (kTwoProductRange N P).sup (kTwoTransferenceFiberCard N P)

theorem collectedAbsoluteCoefficient_productMultiplicity_le
    {N P : ℝ} (hN : 0 ≤ N) {l : ℕ}
    (hl : l ∈ kTwoProductRange N P) :
    collectedAbsoluteCoefficient (fun n => (productMultiplicity N n : ℂ))
        (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
        (N ^ 2) (4 * N ^ 2) l ≤
      (kTwoTransferenceFiberCap N P : ℝ) *
        (maxProductMultiplicity N : ℝ) := by
  unfold collectedAbsoluteCoefficient kTwoTransferenceFiberCap
    kTwoTransferenceFiberCard kTwoPrimeRange kTwoProductRange
  have hcard :
      (((primeRealIcc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)).product
        (natRealIoc (N ^ 2) (4 * N ^ 2))).filter
          (fun q => q.1 * q.2 = l)).card ≤
        (productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
          (N ^ 2) (4 * N ^ 2)).sup
            (fun l =>
              (((primeRealIcc (kTwoPrimeLower N P)
                (2 * kTwoPrimeLower N P)).product (productIoc N)).filter
                  (fun q => q.1 * q.2 = l)).card) := by
    simpa [productIoc, natRealIoc] using!
      (Finset.le_sup
        (f := fun l : ℕ =>
          (((primeRealIcc (kTwoPrimeLower N P)
            (2 * kTwoPrimeLower N P)).product (productIoc N)).filter
              (fun q => q.1 * q.2 = l)).card) hl)
  calc
    (∑ q ∈ (primeRealIcc (kTwoPrimeLower N P)
          (2 * kTwoPrimeLower N P)).product
          (natRealIoc (N ^ 2) (4 * N ^ 2)) with q.1 * q.2 = l,
        ‖(productMultiplicity N q.2 : ℂ)‖) ≤
      ∑ _q ∈ ((primeRealIcc (kTwoPrimeLower N P)
          (2 * kTwoPrimeLower N P)).product
          (natRealIoc (N ^ 2) (4 * N ^ 2))).filter
            (fun q => q.1 * q.2 = l),
        (maxProductMultiplicity N : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      simp only [Complex.norm_natCast]
      exact_mod_cast productMultiplicity_le_maxProductMultiplicity hN q.2
    _ = ((((primeRealIcc (kTwoPrimeLower N P)
          (2 * kTwoPrimeLower N P)).product
          (natRealIoc (N ^ 2) (4 * N ^ 2))).filter
            (fun q => q.1 * q.2 = l)).card : ℝ) *
          (maxProductMultiplicity N : ℝ) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
      (Nat.cast_nonneg _)

theorem inverseSqrtWeight_eq_rpow_neg_half (n : ℕ) :
    inverseSqrtWeight n = Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) := by
  unfold inverseSqrtWeight
  rw [Real.sqrt_eq_rpow]
  exact (Real.rpow_neg (Nat.cast_nonneg n) (1 / 2 : ℝ)).symm

theorem sourcePolynomial_productMultiplicity_eq_collectedPoweringInner
    (N : ℝ) (g₁ g₂ : ℝ) :
    sourcePolynomial (fun n => (productMultiplicity N n : ℂ))
        (N ^ 2) (4 * N ^ 2) (1 / 2) g₁ g₂ =
      collectedPoweringInner N g₁ g₂ := by
  unfold sourcePolynomial gramPolynomial sigmaCoefficient
    collectedPoweringInner poweringMonomial negativeDirichletPhase
  have hsets : natRealIoc (N ^ 2) (4 * N ^ 2) = productIoc N := by
    rfl
  rw [hsets]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (fun n => (productMultiplicity N n : ℂ)) n *
          (Real.rpow (n : ℝ) (-(1 / 2)) : ℂ) *
          dirichletPhase n (-g₁) * star (dirichletPhase n (-g₂)) =
      (productMultiplicity N n : ℂ) *
        (Real.rpow (n : ℝ) (-(1 / 2)) : ℂ) *
          (dirichletPhase n (-g₁) * star (dirichletPhase n (-g₂))) := by
        ring
    _ = _ := by
      rw [dirichletPhase_difference,
        inverseSqrtWeight_eq_rpow_neg_half]
      push_cast
      ring_nf

theorem multiplicityQuadraticForm_eq_sourceQuadratic
    (N : ℝ) (G : Finset ℝ) :
    multiplicityQuadraticForm N G =
      sourceQuadratic (fun n => (productMultiplicity N n : ℂ))
        (N ^ 2) (4 * N ^ 2) (1 / 2) G := by
  unfold multiplicityQuadraticForm sourceQuadratic realGramQuadratic
  change (∑ g ∈ G ×ˢ G, ‖collectedPoweringInner N g.1 g.2‖ ^ 2) = _
  rw [Finset.sum_product G G
    (fun g => ‖collectedPoweringInner N g.1 g.2‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  apply Finset.sum_congr rfl
  intro g₂ hg₂
  change ‖collectedPoweringInner N g₁ g₂‖ ^ 2 =
    ‖sourcePolynomial (fun n => (productMultiplicity N n : ℂ))
      (N ^ 2) (4 * N ^ 2) (1 / 2) g₁ g₂‖ ^ 2
  rw [sourcePolynomial_productMultiplicity_eq_collectedPoweringInner]

def kTwoFullCoefficientOneMoment (N P : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (kTwoProductRange N P) G
    (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase

theorem realGramQuadratic_const_mul
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (S : Finset ι) (W : Finset κ) (c : ℂ) (a : ι → ℂ)
    (z : ι → κ → ℂ) :
    realGramQuadratic S W (fun n => c * a n) z =
      ‖c‖ ^ 2 * realGramQuadratic S W a z := by
  unfold realGramQuadratic gramPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hpoly :
      (∑ n ∈ S, c * a n * z n t * star (z n u)) =
        c * ∑ n ∈ S, a n * z n t * star (z n u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hpoly, norm_mul]
  ring

theorem targetQuadratic_productMultiplicity_le_fiberCap
    {N P : ℝ} (hN : 0 ≤ N) (G : Finset ℝ) :
    targetQuadratic (fun n => (productMultiplicity N n : ℂ))
        (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
        (N ^ 2) (4 * N ^ 2) (1 / 2) G ≤
      ((kTwoTransferenceFiberCap N P : ℝ) *
          (maxProductMultiplicity N : ℝ)) ^ 2 *
        kTwoFullCoefficientOneMoment N P G := by
  let B : ℝ := (kTwoTransferenceFiberCap N P : ℝ) *
    (maxProductMultiplicity N : ℝ)
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmajor := gram_majorant_principle
    (kTwoProductRange N P) G
    (fun l => ((collectedAbsoluteCoefficient
        (fun n => (productMultiplicity N n : ℂ))
        (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
        (N ^ 2) (4 * N ^ 2) l *
          Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
    (fun l => B * Real.rpow (l : ℝ) (-(1 / 2 : ℝ)))
    negativeDirichletPhase
    (fun l hl => by
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hA := collectedAbsoluteCoefficient_productMultiplicity_le
        hN hl
      have hpow := Real.rpow_nonneg (Nat.cast_nonneg l) (-(1 / 2 : ℝ))
      have hAnonneg : 0 ≤ collectedAbsoluteCoefficient
          (fun n => (productMultiplicity N n : ℂ))
          (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
          (N ^ 2) (4 * N ^ 2) l := by
        unfold collectedAbsoluteCoefficient
        positivity
      have habs :
          |collectedAbsoluteCoefficient
              (fun n => (productMultiplicity N n : ℂ))
              (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
              (N ^ 2) (4 * N ^ 2) l *
            Real.rpow (l : ℝ) (-(1 / 2 : ℝ))| =
          collectedAbsoluteCoefficient
              (fun n => (productMultiplicity N n : ℂ))
              (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
              (N ^ 2) (4 * N ^ 2) l *
            Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) :=
        abs_of_nonneg (mul_nonneg hAnonneg hpow)
      rw [habs]
      exact mul_le_mul_of_nonneg_right hA hpow)
  unfold kTwoProductRange at hmajor
  unfold targetQuadratic kTwoFullCoefficientOneMoment kTwoProductRange
  calc
    _ ≤ realGramQuadratic
        (productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
          (N ^ 2) (4 * N ^ 2)) G
        (fun l => ((B * Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℝ) : ℂ))
        negativeDirichletPhase := hmajor
    _ = ‖(B : ℂ)‖ ^ 2 *
        realGramQuadratic
          (productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
            (N ^ 2) (4 * N ^ 2)) G
          (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      convert realGramQuadratic_const_mul
        (productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
          (N ^ 2) (4 * N ^ 2)) G (B : ℂ)
        (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase using 1 <;> norm_cast
    _ = B ^ 2 *
        realGramQuadratic
          (productRealIoc (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
            (N ^ 2) (4 * N ^ 2)) G
          (fun l => (Real.rpow (l : ℝ) (-(1 / 2 : ℝ)) : ℂ))
          negativeDirichletPhase := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
    _ = _ := by rfl

theorem norm_sq_add_add_le_three (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have hxy := norm_add_le x y
  have hxyz := norm_add_le (x + y) z
  have hnorm : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by linarith
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hz := norm_nonneg z
  have hsum : 0 ≤ ‖x‖ + ‖y‖ + ‖z‖ := by positivity
  have hsquare : ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hsum).2 hnorm
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
    sq_nonneg (‖y‖ - ‖z‖)]

theorem gramPolynomial_union
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A B : Finset ι) (hAB : Disjoint A B) (a : ι → ℂ)
    (z : ι → κ → ℂ) (t u : κ) :
    gramPolynomial (A ∪ B) a z t u =
      gramPolynomial A a z t u + gramPolynomial B a z t u := by
  unfold gramPolynomial
  exact Finset.sum_union hAB

theorem realGramQuadratic_union_three_le
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (A B C : Finset ι) (hAB : Disjoint A B)
    (hAC : Disjoint A C) (hBC : Disjoint B C)
    (W : Finset κ) (a : ι → ℂ) (z : ι → κ → ℂ) :
    realGramQuadratic (A ∪ B ∪ C) W a z ≤
      3 * (realGramQuadratic A W a z +
        realGramQuadratic B W a z + realGramQuadratic C W a z) := by
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  unfold realGramQuadratic
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖gramPolynomial (A ∪ B ∪ C) a z t u‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        3 * (‖gramPolynomial A a z t u‖ ^ 2 +
          ‖gramPolynomial B a z t u‖ ^ 2 +
          ‖gramPolynomial C a z t u‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro t ht
      apply Finset.sum_le_sum
      intro u hu
      rw [gramPolynomial_union (A ∪ B) C hABC,
        gramPolynomial_union A B hAB]
      exact norm_sq_add_add_le_three _ _ _
    _ = _ := by
      simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]

def negativeJutilaSecondMoment (X : ℝ) (G : Finset ℝ) : ℝ :=
  realGramQuadratic (realDyadicIoc X) G
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase

theorem negativeJutilaSecondMoment_eq_jutilaSecondMoment
    (X : ℝ) (G : Finset ℝ) :
    negativeJutilaSecondMoment X G = jutilaSecondMoment X G := by
  unfold negativeJutilaSecondMoment jutilaSecondMoment realGramQuadratic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  apply Finset.sum_congr rfl
  intro g₂ hg₂
  congr 2
  unfold gramPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  change (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
      negativeDirichletPhase n g₂ * star (negativeDirichletPhase n g₁) =
    (inverseSqrtWeight n : ℂ) * dirichletPhase n g₁ *
      star (dirichletPhase n g₂)
  rw [inverseSqrtWeight_eq_rpow_neg_half]
  unfold negativeDirichletPhase
  calc
    (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
          dirichletPhase n (-g₂) * star (dirichletPhase n (-g₁)) =
      (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
        (dirichletPhase n (-g₂) * star (dirichletPhase n (-g₁))) := by ring
    _ = (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ) *
        (dirichletPhase n g₁ * star (dirichletPhase n g₂)) := by
      rw [dirichletPhase_difference, dirichletPhase_difference]
      congr 2
      push_cast
      ring
    _ = _ := by ring

theorem kTwoDyadicBlocks_pairwise_disjoint (P : ℝ) :
    Disjoint (realDyadicIoc (P / 4)) (realDyadicIoc (P / 2)) ∧
    Disjoint (realDyadicIoc (P / 4)) (realDyadicIoc P) ∧
    Disjoint (realDyadicIoc (P / 2)) (realDyadicIoc P) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro n hn₁ hn₂
    rw [mem_realDyadicIoc_iff] at hn₁ hn₂
    linarith
  · constructor
    · apply Finset.disjoint_left.mpr
      intro n hn₁ hn₂
      rw [mem_realDyadicIoc_iff] at hn₁ hn₂
      linarith
    · apply Finset.disjoint_left.mpr
      intro n hn₁ hn₂
      rw [mem_realDyadicIoc_iff] at hn₁ hn₂
      linarith

/-- The printed three-block Cauchy step, before Lemma 29.8 is applied. -/
theorem kTwoFullCoefficientOneMoment_le_three_dyadic
    {N P : ℝ} (hN : 0 < N)
    (hJ : 2 ≤ kTwoPrimeLower N P) (G : Finset ℝ) :
    kTwoFullCoefficientOneMoment N P G ≤
      3 * (jutilaSecondMoment (P / 4) G +
        jutilaSecondMoment (P / 2) G + jutilaSecondMoment P G) := by
  have hdis := kTwoDyadicBlocks_pairwise_disjoint P
  unfold kTwoFullCoefficientOneMoment
  rw [kTwoProductRange_eq_dyadicUnion hN hJ]
  have hsplit := realGramQuadratic_union_three_le
    (realDyadicIoc (P / 4)) (realDyadicIoc (P / 2))
    (realDyadicIoc P) hdis.1 hdis.2.1 hdis.2.2 G
    (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
    negativeDirichletPhase
  unfold kTwoDyadicUnion
  have hA : realGramQuadratic (realDyadicIoc (P / 4)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (P / 4) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 4) G
  have hB : realGramQuadratic (realDyadicIoc (P / 2)) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment (P / 2) G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment (P / 2) G
  have hC : realGramQuadratic (realDyadicIoc P) G
      (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
      negativeDirichletPhase = jutilaSecondMoment P G :=
    negativeJutilaSecondMoment_eq_jutilaSecondMoment P G
  rw [hA, hB, hC] at hsplit
  exact hsplit

/-- The three dyadic blocks cost exactly `4+2+1=7` under Lemma 29.8. -/
theorem three_dyadic_jutilaSecondMoments_le_seven
    (P : ℝ) (G : Finset ℝ) :
    jutilaSecondMoment (P / 4) G +
        jutilaSecondMoment (P / 2) G + jutilaSecondMoment P G ≤
      7 * jutilaSecondMoment P G := by
  have h4 := jutilaSecondMoment_div_le P 4 G (by norm_num)
  have h2 := jutilaSecondMoment_div_le P 2 G (by norm_num)
  nlinarith

theorem kTwoFullCoefficientOneMoment_le_twentyOne
    {N P : ℝ} (hN : 0 < N)
    (hJ : 2 ≤ kTwoPrimeLower N P) (G : Finset ℝ) :
    kTwoFullCoefficientOneMoment N P G ≤
      21 * jutilaSecondMoment P G := by
  have hsplit := kTwoFullCoefficientOneMoment_le_three_dyadic hN hJ G
  have hlength := three_dyadic_jutilaSecondMoments_le_seven P G
  nlinarith

def kTwoPrimeReciprocal (N P : ℝ) : ℝ :=
  primeReciprocalSum (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P) (1 / 2)

/-- Fully deterministic, normalized `k=2` Lemma 29.9.  The divisor-fiber
cap and reciprocal-prime sum are exact finite objects; no logarithmic
asymptotic has been inserted. -/
theorem jutila_lemma29Nine_kTwo_normalized
    {N P : ℝ} (hN : 0 < N)
    (hJ : 2 ≤ kTwoPrimeLower N P) (G : Finset ℝ)
    (hprime : (kTwoPrimeRange N P).Nonempty) :
    jutilaSecondMoment N G ^ 2 ≤
      21 * (G.card : ℝ) ^ 2 *
        ((kTwoTransferenceFiberCap N P : ℝ) *
          (maxProductMultiplicity N : ℝ)) ^ 2 *
        (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := by
  have hJnonneg : 0 ≤ kTwoPrimeLower N P := le_trans (by norm_num) hJ
  have hJupper : kTwoPrimeLower N P ≤ 2 * kTwoPrimeLower N P := by linarith
  have hM : 0 ≤ N ^ 2 := sq_nonneg N
  have hM' : N ^ 2 < 4 * N ^ 2 := by nlinarith [sq_pos_of_pos hN]
  have hpow := jutilaSecondMoment_sq_le_multiplicityQuadraticForm N hN.le G
  have htrans := jutila_transference hJ hJupper hM hM'
    (fun n => (productMultiplicity N n : ℂ)) (1 / 2) G hprime
  rw [← multiplicityQuadraticForm_eq_sourceQuadratic] at htrans
  have hcap := targetQuadratic_productMultiplicity_le_fiberCap
    (P := P) hN.le G
  have hdyadic := kTwoFullCoefficientOneMoment_le_twentyOne hN hJ G
  have hqnonneg : 0 ≤ (kTwoPrimeReciprocal N P)⁻¹ := by
    unfold kTwoPrimeReciprocal
    exact inv_nonneg.mpr (Finset.sum_nonneg
      (fun p hp => Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hRnonneg : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hBnonneg :
      0 ≤ ((kTwoTransferenceFiberCap N P : ℝ) *
        (maxProductMultiplicity N : ℝ)) ^ 2 := sq_nonneg _
  calc
    jutilaSecondMoment N G ^ 2 ≤
        (G.card : ℝ) ^ 2 * multiplicityQuadraticForm N G := hpow
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          targetQuadratic (fun n => (productMultiplicity N n : ℂ))
            (kTwoPrimeLower N P) (2 * kTwoPrimeLower N P)
            (N ^ 2) (4 * N ^ 2) (1 / 2) G) :=
      mul_le_mul_of_nonneg_left htrans hRnonneg
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          (((kTwoTransferenceFiberCap N P : ℝ) *
              (maxProductMultiplicity N : ℝ)) ^ 2 *
            kTwoFullCoefficientOneMoment N P G)) := by
      gcongr
    _ ≤ (G.card : ℝ) ^ 2 *
        ((kTwoPrimeReciprocal N P)⁻¹ *
          (((kTwoTransferenceFiberCap N P : ℝ) *
              (maxProductMultiplicity N : ℝ)) ^ 2 *
            (21 * jutilaSecondMoment P G))) := by
      gcongr
    _ = _ := by ring

/-- The single remaining finite-prime estimate needed to turn the normalized
theorem into the printed `(log P)^3` form.  It combines exactly the source's
prime-reciprocal lower bound and its elementary divisor-fiber count. -/
def KTwoPrimeArithmeticLogBudget : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (N P : ℝ), 0 < N → 2 ≤ kTwoPrimeLower N P →
      (kTwoPrimeRange N P).Nonempty →
      21 * (kTwoTransferenceFiberCap N P : ℝ) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹ ≤
        C * (Real.log P) ^ 3

theorem jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudget
    (hbudget : KTwoPrimeArithmeticLogBudget) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (N P : ℝ) (G : Finset ℝ), 0 < N →
        2 ≤ kTwoPrimeLower N P →
        (kTwoPrimeRange N P).Nonempty →
        jutilaSecondMoment N G ^ 2 ≤
          C * (G.card : ℝ) ^ 2 * (Real.log P) ^ 3 *
            (maxProductMultiplicity N : ℝ) ^ 2 *
              jutilaSecondMoment P G := by
  obtain ⟨C, hC, hbudget⟩ := hbudget
  refine ⟨C, hC, ?_⟩
  intro N P G hN hJ hprime
  have hdet := jutila_lemma29Nine_kTwo_normalized hN hJ G hprime
  have hprimeBudget := hbudget N P hN hJ hprime
  have hR : 0 ≤ (G.card : ℝ) ^ 2 := sq_nonneg _
  have hA : 0 ≤ (maxProductMultiplicity N : ℝ) ^ 2 := sq_nonneg _
  have hS : 0 ≤ jutilaSecondMoment P G := by
    unfold jutilaSecondMoment realGramQuadratic
    positivity
  calc
    jutilaSecondMoment N G ^ 2 ≤
        21 * (G.card : ℝ) ^ 2 *
          ((kTwoTransferenceFiberCap N P : ℝ) *
            (maxProductMultiplicity N : ℝ)) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹ * jutilaSecondMoment P G := hdet
    _ = ((G.card : ℝ) ^ 2 * (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment P G) *
        (21 * (kTwoTransferenceFiberCap N P : ℝ) ^ 2 *
          (kTwoPrimeReciprocal N P)⁻¹) := by ring
    _ ≤ ((G.card : ℝ) ^ 2 * (maxProductMultiplicity N : ℝ) ^ 2 *
          jutilaSecondMoment P G) * (C * (Real.log P) ^ 3) := by
      exact mul_le_mul_of_nonneg_left hprimeBudget
        (mul_nonneg (mul_nonneg hR hA) hS)
    _ = _ := by ring

/-! ## Explicit endpoint bridge to the coefficient-one Heath--Brown block -/

theorem inverseSqrtWeight_le_one_of_one_le
    {n : ℕ} (hn : 1 ≤ n) : inverseSqrtWeight n ≤ 1 := by
  unfold inverseSqrtWeight
  exact inv_le_one_of_one_le₀ ((Real.one_le_sqrt).2 (by exact_mod_cast hn))

theorem jutilaSecondMoment_natCast_le_openLeftRatioSecondMoment
    (M : ℕ) (G : Finset ℝ) (hM : 1 ≤ M) :
    jutilaSecondMoment (M : ℝ) G ≤ openLeftRatioSecondMoment M G := by
  rw [jutilaSecondMoment_eq_coefficientOneRatioQuadratic]
  unfold coefficientOneRatioQuadratic openLeftRatioSecondMoment
  rw [realDyadicIoc_natCast]
  apply Finset.sum_le_sum
  intro m hm
  apply Finset.sum_le_sum
  intro n hn
  have hmOne : 1 ≤ m := by
    have := (Finset.mem_Ioc.mp hm).1
    omega
  have hnOne : 1 ≤ n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hwm0 := inverseSqrtWeight_nonneg m
  have hwn0 := inverseSqrtWeight_nonneg n
  have hwm := inverseSqrtWeight_le_one_of_one_le hmOne
  have hwn := inverseSqrtWeight_le_one_of_one_le hnOne
  have hweights : inverseSqrtWeight m * inverseSqrtWeight n ≤ 1 := by
    calc
      inverseSqrtWeight m * inverseSqrtWeight n ≤ 1 * 1 :=
        mul_le_mul hwm hwn hwn0 (by norm_num)
      _ = 1 := by ring
  unfold coefficientOneRatioSummand ratioKernelSquare
  exact mul_le_of_le_one_left
    (sq_nonneg ‖ratioDirichletKernel G ((m : ℝ) / (n : ℝ))‖)
    hweights

/-- The endpoint correction is displayed rather than absorbed: Jutila's
open-left moment is bounded by the open-left coefficient-one block, and the
closed Heath--Brown block is exactly that block plus two cross arms and the
rank-one endpoint atom. -/
theorem jutilaSecondMoment_natCast_le_openLeft_add_boundary
    (M : ℕ) (G : Finset ℝ) (hM : 1 ≤ M) :
    jutilaSecondMoment (M : ℝ) G ≤
      openLeftRatioSecondMoment M G +
        leftEndpointBoundaryContribution M G := by
  have hopen := jutilaSecondMoment_natCast_le_openLeftRatioSecondMoment M G hM
  exact hopen.trans (le_add_of_nonneg_right (by
    unfold leftEndpointBoundaryContribution leftEndpointCrossContribution
      leftEndpointRankOneContribution ratioKernelSquare
    positivity))

theorem jutilaSecondMoment_natCast_le_differenceQuadraticForm_one
    (M : ℕ) (G : Finset ℝ) (hM : 1 ≤ M) :
    jutilaSecondMoment (M : ℝ) G ≤
      GuthMaynardHeathBrownInterface.differenceQuadraticForm
        (fun _ => (1 : ℂ)) M G := by
  calc
    jutilaSecondMoment (M : ℝ) G ≤
        openLeftRatioSecondMoment M G +
          leftEndpointBoundaryContribution M G :=
      jutilaSecondMoment_natCast_le_openLeft_add_boundary M G hM
    _ = GuthMaynardHeathBrownInterface.differenceQuadraticForm
        (fun _ => (1 : ℂ)) M G :=
      (differenceQuadraticForm_one_eq_openLeft_add_boundary M G hM).symm

end

end GuthMaynardJutilaLemma29NineKTwo

#print axioms GuthMaynardJutilaLemma29NineKTwo.kTwoProductRange_eq_dyadicUnion
#print axioms GuthMaynardJutilaLemma29NineKTwo.collectedAbsoluteCoefficient_productMultiplicity_le
#print axioms GuthMaynardJutilaLemma29NineKTwo.multiplicityQuadraticForm_eq_sourceQuadratic
#print axioms GuthMaynardJutilaLemma29NineKTwo.kTwoFullCoefficientOneMoment_le_three_dyadic
#print axioms GuthMaynardJutilaLemma29NineKTwo.three_dyadic_jutilaSecondMoments_le_seven
#print axioms GuthMaynardJutilaLemma29NineKTwo.jutila_lemma29Nine_kTwo_normalized
#print axioms GuthMaynardJutilaLemma29NineKTwo.jutila_lemma29Nine_kTwo_of_primeArithmeticLogBudget
#print axioms GuthMaynardJutilaLemma29NineKTwo.jutilaSecondMoment_natCast_le_openLeft_add_boundary
#print axioms GuthMaynardJutilaLemma29NineKTwo.jutilaSecondMoment_natCast_le_differenceQuadraticForm_one
