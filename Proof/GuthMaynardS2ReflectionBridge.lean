import GuthMaynardS2LiteralReduction
import GuthMaynardLemma62InfiniteTail
import GuthMaynardLemma62PairAssembly
import GuthMaynardHeathBrownCertified
import GuthMaynardS2PoweredPair

/-! # The exact nonzero Fourier sum enters Lemma 6.2
The integer tsum is partitioned into the positive and negative finite prefixes
and the complete tails used by the reflection theorem. This identifies its
left side with the kernel in the literal S2 reduction.
-/

namespace GuthMaynardS2ReflectionBridge

open scoped BigOperators
open GuthMaynardSectorFactorization GuthMaynardS1Source GuthMaynardSectionFourPoisson
open GuthMaynardLemma62FarTail GuthMaynardLemma62InfiniteTail
open GuthMaynardLemma62NegativeNonstationary
open GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62PairAssembly GuthMaynardHeathBrownMajorant
open GuthMaynardHeathBrownInterface
open GuthMaynardS2LiteralReduction GuthMaynardS1Tail

noncomputable section

private theorem sum_Icc_one_eq_range (f : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, f m) = ∑ i ∈ Finset.range M, f (i + 1) := by
  symm
  apply Finset.sum_bij (fun i _ => i + 1)
  · intro i hi
    simp only [Finset.mem_range] at hi
    simp only [Finset.mem_Icc]
    omega
  · intro i hi j hj hij
    omega
  · intro m hm
    simp only [Finset.mem_Icc] at hm
    refine ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
  · intro i hi
    rfl

private theorem tsum_nonzero_eq_prefix_and_tails
    (f : ℤ → ℂ) (hf : Summable f) (M : ℕ) :
    (∑' m : ℤ, if m ≠ 0 then f m else 0) =
      (∑ m ∈ Finset.Icc 1 M, f (m : ℤ)) +
      (∑ m ∈ Finset.Icc 1 M, f (-(m : ℤ))) +
      (∑' i : ℕ, f ((M + (i + 1) : ℕ) : ℤ)) +
      (∑' i : ℕ, f (-((M + (i + 1) : ℕ) : ℤ))) := by
  let g : ℤ → ℂ := fun m => if m ≠ 0 then f m else 0
  have hg : Summable g := by
    refine (hf.indicator {m : ℤ | m ≠ 0}).congr ?_
    intro m
    simp [g, Set.indicator]
  have hpi : Function.Injective (fun n : ℕ => (n : ℤ) + 1) := by
    intro a b h
    exact Int.ofNat.inj (add_right_cancel h)
  have hni : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h
    exact Int.ofNat.inj (add_right_cancel (neg_injective h))
  have hp0 := hg.comp_injective hpi
  have hn0 := hg.comp_injective hni
  have hp : Summable fun n : ℕ => g ((n : ℤ) + 1) := by
    simpa only [Function.comp_apply] using! hp0
  have hn : Summable fun n : ℕ => g (-((n : ℤ) + 1)) := by
    simpa only [Function.comp_apply] using! hn0
  have hpos (n : ℕ) : g ((n : ℤ) + 1) = f ((n + 1 : ℕ) : ℤ) := by
    have hh : (n : ℤ) + 1 ≠ 0 := by positivity
    simp [g, hh]
  have hneg (n : ℕ) : g (-((n : ℤ) + 1)) = f (-((n + 1 : ℕ) : ℤ)) := by
    have hh : (n : ℤ) + 1 ≠ 0 := by positivity
    dsimp only [g]
    rw [if_pos (neg_ne_zero.mpr hh)]
    simp only [Nat.cast_add, Nat.cast_one]
  have heq := tsum_of_add_one_of_neg_add_one hp hn
  simp only [hpos, hneg, show g 0 = 0 by simp [g], add_zero] at heq
  have hp' : Summable fun n : ℕ => f ((n + 1 : ℕ) : ℤ) := hp.congr hpos
  have hn' : Summable fun n : ℕ => f (-((n + 1 : ℕ) : ℤ)) := hn.congr hneg
  have hpt := hp'.sum_add_tsum_nat_add M
  have hnt := hn'.sum_add_tsum_nat_add M
  rw [sum_Icc_one_eq_range, sum_Icc_one_eq_range]
  change (∑' m, g m) = _
  rw [heq, ← hpt, ← hnt]
  simp only [show ∀ i : ℕ, i + M + 1 = M + (i + 1) from fun i => by ac_rfl]
  ring

/-- Exact signed prefix/tail representation, valid for every finite cutoff. -/
theorem sourceNonzeroFourier_eq_prefix_and_tails
    {N : ℕ} (hN : 0 < N) (t : ℝ) (M : ℕ) :
    sourceNonzeroFourier N t =
      (∑ m ∈ Finset.Icc 1 M, sectionThreeFourierCoefficient t ((m : ℝ) * N)) +
      (∑ m ∈ Finset.Icc 1 M, sectionThreeFourierCoefficient t (-((m : ℝ) * N))) +
      (∑' i, positiveFourierTail t N M i) +
      (∑' i, negativeFourierTail t N M i) := by
  have h := tsum_nonzero_eq_prefix_and_tails
    (fun m : ℤ => sourceHhat t ((m : ℝ) * N))
    (summable_norm_sourceHhat_scaled t hN).of_norm M
  simpa only [sourceNonzeroFourier, positiveFourierTail, negativeFourierTail,
    Int.cast_natCast, Int.cast_neg, neg_mul, sourceHhat,
    sectionThreeFourierCoefficient] using h

/-- Reflection in the ordinate preserves the complete Fourier sum by conjugation. -/
theorem sourceNonzeroFourier_neg (N : ℕ) (t : ℝ) :
    sourceNonzeroFourier N (-t) = starRingEnd ℂ (sourceNonzeroFourier N t) := by
  unfold sourceNonzeroFourier
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg ℤ).tsum_eq
    (fun m : ℤ => if m ≠ 0 then sourceHhat (-t) ((m : ℝ) * N) else 0)]
  apply tsum_congr
  intro m
  by_cases hm : m = 0
  · simp [hm]
  · simp only [Equiv.neg_apply, Int.cast_neg, neg_mul]
    have h := GuthMaynardLemma62ReflectionSubstitution.sectionThreeFourierCoefficient_neg_eq_conj
      (-t) ((m : ℝ) * N)
    simpa [sectionThreeFourierCoefficient, sourceHhat, hm] using h

theorem norm_sourceNonzeroFourier_abs (N : ℕ) (t : ℝ) :
    ‖sourceNonzeroFourier N |t|‖ = ‖sourceNonzeroFourier N t‖ := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht]
  · rw [abs_of_neg (lt_of_not_ge ht), sourceNonzeroFourier_neg]
    exact Complex.norm_conj _

/-- The actual constant-explicit reflection budget, including both tails. -/
def sourceReflectionBudget (N : ℕ) (t R : ℝ) (J k ell : ℕ) : ℝ :=
      (∫ r : ℝ in Set.Ioc (-R) R,
        ((1 / (2 * Real.pi)) *
          ((J + 1) * (20 * Real.sqrt (8 * Real.pi) /
            Real.sqrt (t - R)))) *
          (‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖ *
            ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
              (2 ^ J) (t - r)‖)) +
      ((1 / (2 * Real.pi)) *
          Real.log (2 * ((2 ^ J : ℕ) : ℝ)) * ((2 ^ J : ℕ) : ℝ)) *
        (2 * (((2 * Real.pi) ^ k *
          GuthMaynardLemma62AbsoluteMellinTail.sectionThreeMellinSeminorm k) *
          (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)))) +
      ((2 ^ J : ℕ) : ℝ) * (negativeSectorConstant / t) +
      2 * ((lemma43DerivativeConstant ell * (1 + |t|) ^ ell *
          N ^ (-(ell : ℝ))) *
        (((2 ^ J : ℕ) : ℝ) ^ (1 - (ell : ℝ)) /
          ((ell : ℝ) - 1)))

/-- Lemma 6.2 now bounds the exact kernel used by the S2 pair reduction. -/
theorem norm_sourceNonzeroFourier_le_reflection
    {N : ℕ} (hN : 0 < N) (t : ℝ) {R : ℝ} (hR : 0 < R) (htR : R < t)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖sourceNonzeroFourier N t‖ ≤ sourceReflectionBudget N t R J k ell := by
  rw [sourceNonzeroFourier_eq_prefix_and_tails hN t (2 ^ J)]
  exact norm_infinite_twoSided_coefficients_le_reflectedPolynomialIntegral
    t (by exact_mod_cast hN) hR htR J k ell hk hell

/-- The reflection estimate at either sign of the ordinate difference. -/
theorem norm_sourceNonzeroFourier_le_reflection_abs
    {N : ℕ} (hN : 0 < N) (t : ℝ) {R : ℝ} (hR : 0 < R) (htR : R < |t|)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖sourceNonzeroFourier N t‖ ≤ sourceReflectionBudget N |t| R J k ell := by
  rw [← norm_sourceNonzeroFourier_abs]
  exact norm_sourceNonzeroFourier_le_reflection hN |t| hR htR J k ell hk hell

/-- The reflected off-diagonal budget and the literal diagonal contribution. -/
def sourceReflectionPairBudget
    (N : ℕ) (W : Finset ℝ) (R : ℝ) (J k ell : ℕ) : ℝ :=
  (W.card : ℝ) * ‖sourceNonzeroFourier N 0‖ ^ 2 +
    ∑ a ∈ W, ∑ b ∈ W,
      if a ≠ b then sourceReflectionBudget N |a - b| R J k ell ^ 2 else 0

/-- The complete Fourier pair moment enters the reflected budget with its
actual diagonal retained and every off-diagonal pair represented once. -/
theorem sourceNonzeroFourierPairMoment_le_reflection
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) {R : ℝ} (hR : 0 < R)
    (hsep : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → R < |a - b|)
    (J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    sourceNonzeroFourierPairMoment N W ≤ sourceReflectionPairBudget N W R J k ell := by
  have hpoint : ∀ a ∈ W, ∀ b ∈ W,
      ‖sourceNonzeroFourier N (a - b)‖ ^ 2 ≤
        (if a = b then ‖sourceNonzeroFourier N 0‖ ^ 2 else 0) +
          (if a ≠ b then sourceReflectionBudget N |a - b| R J k ell ^ 2 else 0) := by
    intro a ha b hb
    by_cases hab : a = b
    · simp [hab]
    · rw [if_neg hab, if_pos hab, zero_add]
      have h := norm_sourceNonzeroFourier_le_reflection_abs hN (a - b)
        hR (hsep a ha b hb hab) J k ell hk hell
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
  unfold sourceNonzeroFourierPairMoment sourceReflectionPairBudget
  calc
    _ ≤ ∑ a ∈ W, ∑ b ∈ W,
        ((if a = b then ‖sourceNonzeroFourier N 0‖ ^ 2 else 0) +
          (if a ≠ b then sourceReflectionBudget N |a - b| R J k ell ^ 2 else 0)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.sum_le_sum (fun b hb => hpoint a ha b hb)
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Literal S2 is now bounded by the source reflection integrals and explicit
tails, without a sector or mean-value premise. -/
theorem norm_sourceS2_le_reflectionPair
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) {D R : ℝ}
    (hD : 0 < D) (hR : 0 < R) (hRD : R < D)
    (hsep : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → D ≤ |a - b|)
    (j J k ell : ℕ) (hk : 2 ≤ k) (hell : 2 ≤ ell) :
    ‖GuthMaynardEquation55Infinite.sourceS2 N W‖ ≤
      3 * (N : ℝ) ^ 3 *
        (lemma43DerivativeConstant 0 + (W.card : ℝ) *
          (s1VerticalConstant j / (D / (2 * Real.pi)) ^ j)) *
        sourceReflectionPairBudget N W R J k ell := by
  apply (norm_sourceS2_le_pairMoment hN W hD hsep j).trans
  apply mul_le_mul_of_nonneg_left
    (sourceNonzeroFourierPairMoment_le_reflection hN W hR
      (fun a ha b hb hab => hRD.trans_le (hsep a ha b hb hab)) J k ell hk hell)
  exact mul_nonneg (by positivity)
    (add_nonneg (lemma43DerivativeConstant_nonneg 0)
      (mul_nonneg (by positivity)
        (div_nonneg (s1VerticalConstant_nonneg j) (by positivity))))

/-- Certified central reflected pair estimate, now without a Heath--Brown premise. -/
theorem reflectedDyadic_pair_integral_sq_le {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (R : ℝ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M → CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W,
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
                ((1 : ℂ) + r * Complex.I)‖ *
              ‖reflectedDyadicPolynomial M ((t - u) - r)‖) ^ 2) ≤
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
            (C * Real.rpow T eta * heathBrownShape T M W) :=
  mellin_reflectedDyadic_pair_integral_sq_le_of_oneCoefficientCore
    GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore heta

/-- The entire reflected prefix, with disjoint dyadic blocks and the endpoint
one retained, is controlled by the certified Heath--Brown estimate. -/
theorem reflectedPrefix_pair_integral_sq_le {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (J : ℕ) (R : ℝ) (W : Finset ℝ),
        T₀ ≤ T → CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W,
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
                ((1 : ℂ) + r * Complex.I)‖ *
              ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
                (2 ^ J) ((t - u) - r)‖) ^ 2) ≤
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
          (((J + 1 : ℕ) : ℝ) * ((W.card : ℝ) ^ 2 +
            C * Real.rpow T eta * ∑ j ∈ Finset.range J, heathBrownShape T (2 ^ j) W)) := by
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ :=
    GuthMaynardHeathBrownCertified.heathBrownOneCoefficientCore eta heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T J R W hT hsep hinterval
  apply (mellin_reflectedPrefix_pair_integral_sq_le J R W).trans
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add_right
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  exact hHB T (2 ^ j) W hT (Nat.one_le_pow j 2 (by norm_num)) hsep hinterval

/-- The reflected open-left block obeys the powered k=2 pair estimate after
Mellin integration. The auxiliary shift is retained as a unit coefficient. -/
theorem reflectedDyadicIoc_pair_integral_sq_le_powered {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (M : ℕ) (R : ℝ) (W : Finset ℝ),
        T₀ ≤ T → 1 ≤ M → (M : ℝ) ≤ T → CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W,
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
                ((1 : ℂ) + r * Complex.I)‖ *
              ‖reflectedDyadicIocPolynomial M ((t - u) - r)‖) ^ 2) ≤
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
            (C * Real.rpow T eta * (W.card : ℝ) *
              Real.sqrt (heathBrownShape T (M ^ 2) W)) := by
  obtain ⟨C, T₀, hC, hT₀, hsecond⟩ :=
    GuthMaynardS2PoweredPair.unweightedPairSecondMoment_bound heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M R W hT hM hMT hsep hinterval
  apply finitePair_weighted_integral_sq_le W
  · exact GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm
  · intro t u
    unfold reflectedDyadicIocPolynomial
      GuthMaynardLemma62ReflectionSubstitution.reflectionScalePhase
    fun_prop
  · intro r
    exact norm_nonneg _
  · intro t u r
    exact norm_nonneg _
  · intro r
    simp_rw [reflectedDyadicIocPolynomial_eq_dirichlet_swap]
    rw [Finset.sum_comm]
    exact hsecond T M (reflectedMellinCoefficient r) W hT hM hMT
      (fun n _ => (norm_reflectedMellinCoefficient r n).le) hsep hinterval

/-- Full-prefix version of the powered reflected estimate. Every dyadic block
is charged once and the singleton endpoint is retained explicitly. -/
theorem reflectedPrefix_pair_integral_sq_le_powered {eta : ℝ} (heta : 0 < eta) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
      ∀ (T : ℝ) (J : ℕ) (R : ℝ) (W : Finset ℝ),
        T₀ ≤ T → ((2 ^ J : ℕ) : ℝ) ≤ T → CGLProofDAG.OneSeparated W →
        ContainedInIntervalOfLength W T →
        (∑ t ∈ W, ∑ u ∈ W,
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
                ((1 : ℂ) + r * Complex.I)‖ *
              ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
                (2 ^ J) ((t - u) - r)‖) ^ 2) ≤
          (∫ r : ℝ in Set.Ioc (-R) R,
            ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
              ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
          (((J + 1 : ℕ) : ℝ) * ((W.card : ℝ) ^ 2 +
            ∑ j ∈ Finset.range J,
              C * Real.rpow T eta * (W.card : ℝ) *
                Real.sqrt (heathBrownShape T ((2 ^ j) ^ 2) W))) := by
  obtain ⟨C, T₀, hC, hT₀, hsecond⟩ :=
    GuthMaynardS2PoweredPair.unweightedPairSecondMoment_bound heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T J R W hT hJT hsep hinterval
  apply finitePair_weighted_integral_sq_le W
  · exact GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm
  · intro t u
    unfold GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
      GuthMaynardLemma62ReflectionSubstitution.reflectionScalePhase
    fun_prop
  · intro r
    exact norm_nonneg _
  · intro t u r
    exact norm_nonneg _
  · intro r
    let f := fun t u j => ‖reflectedDyadicIocPolynomial (2 ^ j) ((t - u) - r)‖ ^ 2
    have hcomm : (∑ t ∈ W, ∑ u ∈ W, ∑ j ∈ Finset.range J, f t u j) =
        ∑ j ∈ Finset.range J, ∑ t ∈ W, ∑ u ∈ W, f t u j := by
      calc
        _ = ∑ t ∈ W, ∑ j ∈ Finset.range J, ∑ u ∈ W, f t u j :=
          Finset.sum_congr rfl (fun t _ => Finset.sum_comm)
        _ = _ := Finset.sum_comm
    calc
      _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          (((J + 1 : ℕ) : ℝ) * (1 + ∑ j ∈ Finset.range J, f t u j)) := by
        apply Finset.sum_le_sum
        intro t ht
        apply Finset.sum_le_sum
        intro u hu
        exact norm_reflectedDirichletPolynomial_pow_sq_le_dyadicIoc J ((t - u) - r)
      _ = ((J + 1 : ℕ) : ℝ) * ((W.card : ℝ) ^ 2 +
          ∑ j ∈ Finset.range J, ∑ t ∈ W, ∑ u ∈ W, f t u j) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib,
          Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hcomm]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro j hj
        have hjJ := (Finset.mem_range.mp hj).le
        have hpowlen : ((2 ^ j : ℕ) : ℝ) ≤ ((2 ^ J : ℕ) : ℝ) := by
          exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ (2 : ℕ)) hjJ)
        have hlen := hpowlen.trans hJT
        unfold f
        simp_rw [reflectedDyadicIocPolynomial_eq_dirichlet_swap]
        rw [Finset.sum_comm]
        exact hsecond T (2 ^ j) (reflectedMellinCoefficient r) W hT
          (Nat.one_le_pow j 2 (by norm_num)) hlen
          (fun n _ => (norm_reflectedMellinCoefficient r n).le) hsep hinterval

end
end GuthMaynardS2ReflectionBridge

#print axioms GuthMaynardS2ReflectionBridge.sourceNonzeroFourier_eq_prefix_and_tails
#print axioms GuthMaynardS2ReflectionBridge.norm_sourceNonzeroFourier_le_reflection
#print axioms GuthMaynardS2ReflectionBridge.reflectedDyadic_pair_integral_sq_le

#print axioms GuthMaynardS2ReflectionBridge.reflectedPrefix_pair_integral_sq_le

#print axioms GuthMaynardS2ReflectionBridge.norm_sourceS2_le_reflectionPair

#print axioms GuthMaynardS2ReflectionBridge.reflectedDyadicIoc_pair_integral_sq_le_powered

#print axioms GuthMaynardS2ReflectionBridge.reflectedPrefix_pair_integral_sq_le_powered
