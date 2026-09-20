import GuthMaynardLemma296SmoothingCore

/-!
# Exact finite reduction in Jutila Lemma 29.6

This module proves the algebraic smoothing step at the start of the proof on
p. 267.  The hard dyadic coefficient is first extended by zero to the literal
support `(N/2,5N/2]`, and the finite Gram majorant is then applied with the
source cutoff `w₀`.  The remaining estimates in this file are only finite-sum
and support-cardinality bounds.
-/

namespace GuthMaynardLemma296SmoothingReduction

open scoped BigOperators ComplexConjugate
open GuthMaynardHeathBrownMajorant
open GuthMaynardJutilaTransference
open GuthMaynardJutilaLemma29NineKTwo
open GuthMaynardJutilaReflection2941
open GuthMaynardSourceWZeroProperties
open GuthMaynardLengthComparison
open GuthMaynardLemma295OffDiagonalAssembly
open GuthMaynardLemma295ReflectedPairConstruction
open GuthMaynardLemma296SmoothingCore

noncomputable section

def lemma296HardCoefficient (N : ℝ) (n : ℕ) : ℝ :=
  if n ∈ realDyadicIoc N then inverseSqrtWeight n else 0

/-- Extending the hard coefficient by zero to the smooth support changes no
Gram polynomial. -/
theorem gramPolynomial_hard_bigSupport_eq_dyadic
    {N : ℝ} (hN : 0 ≤ N) (g₁ g₂ : ℝ) :
    gramPolynomial (lemma296BigSupport N)
        (fun n => (lemma296HardCoefficient N n : ℂ))
        negativeDirichletPhase g₁ g₂ =
      gramPolynomial (realDyadicIoc N)
        (fun n => (Real.rpow (n : ℝ) (-(1 / 2 : ℝ)) : ℂ))
        negativeDirichletPhase g₁ g₂ := by
  unfold gramPolynomial
  symm
  apply Finset.sum_subset_zero_on_sdiff
      (realDyadicIoc_subset_lemma296BigSupport hN)
  · intro n hn
    simp only [Finset.mem_sdiff] at hn
    simp [lemma296HardCoefficient, hn.2]
  · intro n hn
    simp [lemma296HardCoefficient, hn,
      inverseSqrtWeight_eq_rpow_neg_half]

/-- Exact support extension for the negative-phase second moment. -/
theorem negativeJutilaSecondMoment_eq_bigSupport_hard
    {N : ℝ} (hN : 0 ≤ N) (G : Finset ℝ) :
    negativeJutilaSecondMoment N G =
      realGramQuadratic (lemma296BigSupport N) G
        (fun n => (lemma296HardCoefficient N n : ℂ))
        negativeDirichletPhase := by
  unfold negativeJutilaSecondMoment realGramQuadratic
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  apply Finset.sum_congr rfl
  intro g₂ hg₂
  rw [gramPolynomial_hard_bigSupport_eq_dyadic hN]

/-- Pointwise coefficient domination in the exact common support. -/
theorem norm_hardCoefficient_le_smooth
    {N : ℝ} (hN : 0 < N) {n : ℕ} (_hn : n ∈ lemma296BigSupport N) :
    ‖(lemma296HardCoefficient N n : ℂ)‖ ≤
      Real.rpow N (-(1 / 2 : ℝ)) * lemma296SmoothCoefficient N n := by
  by_cases hncore : n ∈ realDyadicIoc N
  · rw [lemma296HardCoefficient, if_pos hncore, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (inverseSqrtWeight_nonneg n)]
    exact inverseSqrtWeight_le_scale_mul_smooth hN hncore
  · rw [lemma296HardCoefficient, if_neg hncore]
    simp only [Complex.ofReal_zero, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg hN.le _)
      (sourceWZero_nonneg _ _ _ _ _)

/-- The literal hard second moment is bounded by `N⁻¹` times the smooth
Gram moment. -/
theorem negativeJutilaSecondMoment_le_smoothGram
    {N : ℝ} (hN : 0 < N) (G : Finset ℝ) :
    negativeJutilaSecondMoment N G ≤
      N⁻¹ * realGramQuadratic (lemma296BigSupport N) G
        (fun n => (lemma296SmoothCoefficient N n : ℂ))
        negativeDirichletPhase := by
  rw [negativeJutilaSecondMoment_eq_bigSupport_hard hN.le]
  calc
    realGramQuadratic (lemma296BigSupport N) G
        (fun n => (lemma296HardCoefficient N n : ℂ))
        negativeDirichletPhase ≤
      realGramQuadratic (lemma296BigSupport N) G
        (fun n => ((Real.rpow N (-(1 / 2 : ℝ)) *
          lemma296SmoothCoefficient N n : ℝ) : ℂ))
        negativeDirichletPhase :=
      gram_majorant_principle _ _ _ _ _
        (fun n hn => norm_hardCoefficient_le_smooth hN hn)
    _ = ‖(Real.rpow N (-(1 / 2 : ℝ)) : ℂ)‖ ^ 2 *
        realGramQuadratic (lemma296BigSupport N) G
          (fun n => (lemma296SmoothCoefficient N n : ℂ))
          negativeDirichletPhase := by
      rw [← realGramQuadratic_const_mul]
      congr 3
      funext n
      push_cast
      ring
    _ = N⁻¹ * realGramQuadratic (lemma296BigSupport N) G
          (fun n => (lemma296SmoothCoefficient N n : ℂ))
          negativeDirichletPhase := by
      congr 1
      calc
        ‖(Real.rpow N (-(1 / 2 : ℝ)) : ℂ)‖ ^ 2 =
            Real.rpow N (-(1 / 2 : ℝ)) ^ 2 := by
          rw [Complex.norm_real]
          exact congrArg (· ^ 2)
            (Real.norm_of_nonneg (Real.rpow_nonneg hN.le _))
        _ = Real.rpow N (-(1 / 2 : ℝ) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hN.le _ 2).symm
        _ = N⁻¹ := by
          have hexp : -(1 / 2 : ℝ) * (2 : ℕ) = -1 := by norm_num
          rw [hexp]
          exact Real.rpow_neg_one N

/-- Exact identification of the smooth Gram moment with the full ordered
pair moment of `h_g⁺`. -/
theorem smoothGram_eq_fullHPlusPairMoment
    {N : ℝ} (hN : 0 < N) (G : Finset ℝ) :
    realGramQuadratic (lemma296BigSupport N) G
        (fun n => (lemma296SmoothCoefficient N n : ℂ))
        negativeDirichletPhase =
      ∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2 := by
  unfold realGramQuadratic
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g₁ hg₁
  apply Finset.sum_congr rfl
  intro g₂ hg₂
  exact (norm_sourceHPlusSum_sq_eq_gram hN g₁ g₂).symm

/-- Exact diagonal/off-diagonal split of the full ordered pair moment. -/
theorem fullHPlusPairMoment_eq_diagonal_add_offDiagonal
    (N : ℝ) (G : Finset ℝ) :
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2) =
      (G.card : ℝ) * ‖sourceHPlusSum N 0‖ ^ 2 +
        offDiagonalHPlusPairMoment N G := by
  classical
  unfold offDiagonalHPlusPairMoment
  calc
    (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2) =
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        if g₁ = g₂ then ‖sourceHPlusSum N 0‖ ^ 2 else 0) +
      (∑ g₁ ∈ G, ∑ g₂ ∈ G,
        if g₁ = g₂ then 0
        else ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g₁ hg₁
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro g₂ hg₂
      by_cases h : g₁ = g₂
      · subst g₂
        simp
      · simp [h]
    _ = (G.card : ℝ) * ‖sourceHPlusSum N 0‖ ^ 2 +
        offDiagonalHPlusPairMoment N G := by
      congr 1
      simp

/-- The literal smooth support has at most `5N` integers for `N ≥ 1`.
The deliberately coarse constant leaves the endpoint convention visible. -/
theorem card_lemma296BigSupport_le_five_mul
    {N : ℝ} (hN : 1 ≤ N) :
    ((lemma296BigSupport N).card : ℝ) ≤ 5 * N := by
  have hupper : 0 ≤ 5 * N / 2 := by positivity
  have hsubset : lemma296BigSupport N ⊆
      Finset.range (Nat.ceil (5 * N / 2) + 1) := by
    unfold lemma296BigSupport natRealIoc
    exact Finset.filter_subset _ _
  have hcardNat := Finset.card_le_card hsubset
  have hcardNat' : (lemma296BigSupport N).card ≤
      Nat.ceil (5 * N / 2) + 1 := by
    simpa using hcardNat
  have hcard : ((lemma296BigSupport N).card : ℝ) ≤
      (Nat.ceil (5 * N / 2) : ℝ) + 1 := by
    exact_mod_cast hcardNat'
  have hceil := Nat.ceil_lt_add_one hupper
  nlinarith

/-- At frequency zero every summand in the smooth polynomial has norm at
most one. -/
theorem norm_sourceHPlus_zero_le_one (alpha : ℝ) :
    ‖sourceHPlus 0 alpha‖ ≤ 1 := by
  unfold sourceHPlus
  calc
    ‖(sourceWZero alpha (1 / 2) 1 2 (5 / 2) : ℂ) *
        Complex.exp (Complex.I * (0 * Real.log alpha))‖ =
      sourceWZero alpha (1 / 2) 1 2 (5 / 2) := by
        rw [norm_mul, Complex.norm_real,
          Real.norm_of_nonneg (sourceWZero_nonneg _ _ _ _ _)]
        simp
    _ ≤ 1 := sourceWZero_le_one _ _ _ _ _

/-- The zero-frequency smooth sum is bounded by the cardinality of its
literal support, hence by `5N`. -/
theorem norm_sourceHPlusSum_zero_le_five_mul
    {N : ℝ} (hN : 1 ≤ N) :
    ‖sourceHPlusSum N 0‖ ≤ 5 * N := by
  unfold sourceHPlusSum
  calc
    ‖∑ n ∈ lemma296BigSupport N,
        sourceHPlus 0 ((n : ℝ) / N)‖ ≤
      ∑ n ∈ lemma296BigSupport N,
        ‖sourceHPlus 0 ((n : ℝ) / N)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ lemma296BigSupport N, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact norm_sourceHPlus_zero_le_one _
    _ = ((lemma296BigSupport N).card : ℝ) := by simp
    _ ≤ 5 * N := card_lemma296BigSupport_le_five_mul hN

/-- Premise-free inhabitant of the exact p. 267 smoothing reduction.  The
constant `25` is a transparent coarse support constant; no asymptotic or
analytic theorem is used. -/
theorem lemma296SmoothedSecondMomentReduction_certified :
    Lemma296SmoothedSecondMomentReduction := by
  refine ⟨25, by norm_num, ?_⟩
  intro N G hN
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNinv0 : 0 ≤ N⁻¹ := inv_nonneg.mpr hNpos.le
  have hcard0 : 0 ≤ (G.card : ℝ) := by positivity
  have hoff0 := offDiagonalHPlusPairMoment_nonneg N G
  have hnorm := norm_sourceHPlusSum_zero_le_five_mul hN
  have hnormsq : ‖sourceHPlusSum N 0‖ ^ 2 ≤ 25 * N ^ 2 := by
    have hfive0 : 0 ≤ 5 * N := mul_nonneg (by norm_num) hNpos.le
    calc
      ‖sourceHPlusSum N 0‖ ^ 2 ≤ (5 * N) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = 25 * N ^ 2 := by ring
  calc
    jutilaSecondMoment N G = negativeJutilaSecondMoment N G :=
      (negativeJutilaSecondMoment_eq_jutilaSecondMoment N G).symm
    _ ≤ N⁻¹ * realGramQuadratic (lemma296BigSupport N) G
          (fun n => (lemma296SmoothCoefficient N n : ℂ))
          negativeDirichletPhase :=
      negativeJutilaSecondMoment_le_smoothGram hNpos G
    _ = N⁻¹ * (∑ g₁ ∈ G, ∑ g₂ ∈ G,
          ‖sourceHPlusSum N (g₁ - g₂)‖ ^ 2) := by
      rw [smoothGram_eq_fullHPlusPairMoment hNpos]
    _ = N⁻¹ * ((G.card : ℝ) * ‖sourceHPlusSum N 0‖ ^ 2 +
          offDiagonalHPlusPairMoment N G) := by
      rw [fullHPlusPairMoment_eq_diagonal_add_offDiagonal]
    _ ≤ N⁻¹ * ((G.card : ℝ) * (25 * N ^ 2) +
          offDiagonalHPlusPairMoment N G) := by
      gcongr
    _ = 25 * ((G.card : ℝ) * N) +
          N⁻¹ * offDiagonalHPlusPairMoment N G := by
      field_simp [hNpos.ne']
    _ ≤ 25 * ((G.card : ℝ) * N +
          N⁻¹ * offDiagonalHPlusPairMoment N G) := by
      nlinarith

end

end GuthMaynardLemma296SmoothingReduction

#print axioms GuthMaynardLemma296SmoothingReduction.negativeJutilaSecondMoment_le_smoothGram
#print axioms GuthMaynardLemma296SmoothingReduction.smoothGram_eq_fullHPlusPairMoment
#print axioms GuthMaynardLemma296SmoothingReduction.lemma296SmoothedSecondMomentReduction_certified
