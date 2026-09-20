import GuthMaynardLemma62NegativeNonstationary
import GuthMaynardHeathBrownMajorant
import GuthMaynardJIterationAffineEnergy

/-!
# Pair-moment assembly after Guth--Maynard Lemma 6.2

The approximate functional equation in Section 6 produces, for each Mellin
parameter `r`, a unit-coefficient reflected polynomial on a dyadic block.
This file identifies its complete `W x W` second moment with the literal
Heath--Brown difference quadratic form.  In particular the Mellin shift is
retained as a coefficient of norm one; it is not discarded or confused with
the original detector coefficient.

This is the deterministic seam immediately after Lemma 6.2 and immediately
before the analytic Heath--Brown estimate (6.3).
-/

namespace GuthMaynardLemma62PairAssembly

open Real Complex Set MeasureTheory
open scoped BigOperators
open GuthMaynardSource
open GuthMaynardLemma62ReflectionSubstitution
open GuthMaynardHeathBrownInterface
open GuthMaynardHeathBrownMajorant

noncomputable section

/-- The exact dyadic reflected polynomial occurring after the prefix in
Lemma 6.2 is split into dyadic blocks. -/
def reflectedDyadicPolynomial (M : ℕ) (tau : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc M (2 * M), reflectionScalePhase tau (n : ℝ)

/-- The exact open-left dyadic block used by the paper's background
convention `M < n <= 2M`. -/
def reflectedDyadicIocPolynomial (M : ℕ) (tau : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc M (2 * M), reflectionScalePhase tau (n : ℝ)

/-- The auxiliary Mellin shift, kept as a literal coefficient sequence. -/
def reflectedMellinCoefficient (r : ℝ) (n : ℕ) : ℂ :=
  reflectionScalePhase (-r) (n : ℝ)

theorem norm_reflectedMellinCoefficient (r : ℝ) (n : ℕ) :
    ‖reflectedMellinCoefficient r n‖ = 1 := by
  exact norm_reflectionScalePhase (-r) (n : ℝ)

/-- Exact one-step dyadic splitting of the prefix produced by Lemma 6.2.
Iterating this identity partitions the prefix into disjoint open-left blocks,
so no endpoint is duplicated. -/
theorem reflectedDirichletPolynomial_pow_succ_eq_add_dyadicIoc
    (J : ℕ) (tau : ℝ) :
    GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ (J + 1)) tau =
      GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
          (2 ^ J) tau +
        reflectedDyadicIocPolynomial (2 ^ J) tau := by
  let A : Finset ℕ := Finset.Icc 1 (2 ^ J)
  let B : Finset ℕ := Finset.Ioc (2 ^ J) (2 * 2 ^ J)
  have htop : 2 ^ (J + 1) = 2 * 2 ^ J := by
    rw [pow_succ]
    ring
  have hunion : Finset.Icc 1 (2 ^ (J + 1)) = A ∪ B := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc, A, B]
    rw [htop]
    omega
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro n hnA hnB
    have ha := (Finset.mem_Icc.mp hnA).2
    have hb := (Finset.mem_Ioc.mp hnB).1
    omega
  unfold GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
    reflectedDyadicIocPolynomial
  rw [hunion, Finset.sum_union hdisjoint]

/-- Iterated exact dyadic decomposition of the Lemma-6.2 prefix. -/
theorem reflectedDirichletPolynomial_pow_eq_one_add_sum_dyadicIoc
    (J : ℕ) (tau : ℝ) :
    GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) tau =
      1 + ∑ j ∈ Finset.range J,
        reflectedDyadicIocPolynomial (2 ^ j) tau := by
  induction J with
  | zero =>
      unfold GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        reflectionScalePhase
      simp
  | succ J ih =>
      rw [show J + 1 = Nat.succ J by rfl,
        reflectedDirichletPolynomial_pow_succ_eq_add_dyadicIoc J tau,
        ih, Finset.sum_range_succ]
      ring

/-- Pointwise dyadic Cauchy bound for the exact prefix.  The factor `J+1`
is the complete logarithmic cost of splitting the singleton plus `J`
open-left blocks. -/
theorem norm_reflectedDirichletPolynomial_pow_sq_le_dyadicIoc
    (J : ℕ) (tau : ℝ) :
    ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) tau‖ ^ 2 ≤
      ((J + 1 : ℕ) : ℝ) *
        (1 + ∑ j ∈ Finset.range J,
          ‖reflectedDyadicIocPolynomial (2 ^ j) tau‖ ^ 2) := by
  let a : ℕ → ℝ := fun i =>
    if i = 0 then 1
    else ‖reflectedDyadicIocPolynomial (2 ^ (i - 1)) tau‖
  have hsumA :
      (∑ i ∈ Finset.range (J + 1), a i) =
        1 + ∑ j ∈ Finset.range J,
          ‖reflectedDyadicIocPolynomial (2 ^ j) tau‖ := by
    rw [Finset.sum_range_succ']
    simp [a]
    ring
  have hsumASq :
      (∑ i ∈ Finset.range (J + 1), a i ^ 2) =
        1 + ∑ j ∈ Finset.range J,
          ‖reflectedDyadicIocPolynomial (2 ^ j) tau‖ ^ 2 := by
    rw [Finset.sum_range_succ']
    simp [a]
    ring
  have hnorm :
      ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
          (2 ^ J) tau‖ ≤ ∑ i ∈ Finset.range (J + 1), a i := by
    rw [reflectedDirichletPolynomial_pow_eq_one_add_sum_dyadicIoc,
      hsumA]
    calc
      ‖(1 : ℂ) + ∑ j ∈ Finset.range J,
          reflectedDyadicIocPolynomial (2 ^ j) tau‖ ≤
        1 + ‖∑ j ∈ Finset.range J,
          reflectedDyadicIocPolynomial (2 ^ j) tau‖ := by
            simpa using norm_add_le (1 : ℂ)
              (∑ j ∈ Finset.range J,
                reflectedDyadicIocPolynomial (2 ^ j) tau)
      _ ≤ 1 + ∑ j ∈ Finset.range J,
          ‖reflectedDyadicIocPolynomial (2 ^ j) tau‖ := by
            gcongr
            exact norm_sum_le _ _
  have hsumNonneg : 0 ≤ ∑ i ∈ Finset.range (J + 1), a i := by
    apply Finset.sum_nonneg
    intro i hi
    unfold a
    split_ifs <;> positivity
  have hsquare :
      ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
          (2 ^ J) tau‖ ^ 2 ≤
        (∑ i ∈ Finset.range (J + 1), a i) ^ 2 := by
    nlinarith [norm_nonneg
      (GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) tau)]
  have hcauchy :
      (∑ i ∈ Finset.range (J + 1), a i) ^ 2 ≤
        ((Finset.range (J + 1)).card : ℝ) *
          ∑ i ∈ Finset.range (J + 1), a i ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq
  calc
    ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) tau‖ ^ 2 ≤
      (∑ i ∈ Finset.range (J + 1), a i) ^ 2 := hsquare
    _ ≤ ((Finset.range (J + 1)).card : ℝ) *
        ∑ i ∈ Finset.range (J + 1), a i ^ 2 := hcauchy
    _ = _ := by rw [Finset.card_range, hsumASq]

/-- The sign and shift identity needed in Section 6.  Swapping the pair
`(t,u)` turns the negative reflected phase into the positive phase convention
of the published Heath--Brown polynomial. -/
theorem reflectedDyadicPolynomial_eq_displayed_swap
    (M : ℕ) (r t u : ℝ) :
    reflectedDyadicPolynomial M ((t - u) - r) =
      displayedDirichletPolynomial (reflectedMellinCoefficient r) M (u - t) := by
  unfold reflectedDyadicPolynomial displayedDirichletPolynomial
    reflectedMellinCoefficient reflectionScalePhase
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Open-left version of the sign/shift identity, matching the paper's
default dyadic convention exactly. -/
theorem reflectedDyadicIocPolynomial_eq_dirichlet_swap
    (M : ℕ) (r t u : ℝ) :
    reflectedDyadicIocPolynomial M ((t - u) - r) =
      CGLProofDAG.dirichletPolynomial (reflectedMellinCoefficient r) M (u - t) := by
  unfold reflectedDyadicIocPolynomial CGLProofDAG.dirichletPolynomial
    reflectedMellinCoefficient reflectionScalePhase
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The exact open-left block is the displayed closed block with its lower
endpoint coefficient set to zero. -/
theorem reflectedDyadicIocPolynomial_eq_displayedLowerEndpointZero_swap
    (M : ℕ) (r t u : ℝ) :
    reflectedDyadicIocPolynomial M ((t - u) - r) =
      displayedDirichletPolynomial
        (lowerEndpointZero M (reflectedMellinCoefficient r)) M (u - t) := by
  rw [displayedDirichletPolynomial_lowerEndpointZero]
  exact reflectedDyadicIocPolynomial_eq_dirichlet_swap M r t u

/-- The complete pair moment of one reflected dyadic block is exactly the
Heath--Brown difference quadratic form.  This equality retains the Mellin
coefficient and is source-faithful at both dyadic endpoints. -/
theorem reflectedDyadicPairMoment_eq_differenceQuadraticForm
    (M : ℕ) (r : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicPolynomial M ((t - u) - r)‖ ^ 2) =
      differenceQuadraticForm (reflectedMellinCoefficient r) M W := by
  unfold differenceQuadraticForm differencePolynomial
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicPolynomial M ((t - u) - r)‖ ^ 2) =
      ∑ u ∈ W, ∑ t ∈ W,
        ‖reflectedDyadicPolynomial M ((u - t) - r)‖ ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ u ∈ W, ∑ t ∈ W,
        ‖displayedDirichletPolynomial
            (reflectedMellinCoefficient r) M (t - u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro t ht
          rw [reflectedDyadicPolynomial_eq_displayed_swap]
    _ = _ := by rw [Finset.sum_comm]

/-- Pair-moment identity for the exact open-left source block. -/
theorem reflectedDyadicIocPairMoment_eq_differenceQuadraticForm
    (M : ℕ) (r : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicIocPolynomial M ((t - u) - r)‖ ^ 2) =
      differenceQuadraticForm
        (lowerEndpointZero M (reflectedMellinCoefficient r)) M W := by
  unfold differenceQuadraticForm differencePolynomial
  calc
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicIocPolynomial M ((t - u) - r)‖ ^ 2) =
      ∑ u ∈ W, ∑ t ∈ W,
        ‖reflectedDyadicIocPolynomial M ((u - t) - r)‖ ^ 2 := by
          rw [Finset.sum_comm]
    _ = ∑ u ∈ W, ∑ t ∈ W,
        ‖displayedDirichletPolynomial
          (lowerEndpointZero M (reflectedMellinCoefficient r)) M (t - u)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro u hu
          apply Finset.sum_congr rfl
          intro t ht
          rw [reflectedDyadicIocPolynomial_eq_displayedLowerEndpointZero_swap]
    _ = _ := by rw [Finset.sum_comm]

/-- The Mellin-shifted pair moment is bounded by the coefficient-one
Heath--Brown block.  Thus the auxiliary integration variable costs no
coefficient size and no detector-specific hypothesis. -/
theorem reflectedDyadicPairMoment_le_oneCoefficient
    (M : ℕ) (r : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicPolynomial M ((t - u) - r)‖ ^ 2) ≤
      differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  rw [reflectedDyadicPairMoment_eq_differenceQuadraticForm]
  exact differenceQuadraticForm_le_oneCoefficient M W
    (fun n hn => by rw [norm_reflectedMellinCoefficient])

/-- Coefficient-one control for the exact open-left source block, including
the lower-endpoint zero rather than adding an extra atom. -/
theorem reflectedDyadicIocPairMoment_le_oneCoefficient
    (M : ℕ) (r : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
        ‖reflectedDyadicIocPolynomial M ((t - u) - r)‖ ^ 2) ≤
      differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  rw [reflectedDyadicIocPairMoment_eq_differenceQuadraticForm]
  exact differenceQuadraticForm_le_oneCoefficient M W (fun n hn => by
    unfold lowerEndpointZero
    split_ifs
    · simp
    · rw [norm_reflectedMellinCoefficient])

/-- Pairwise version of the exact prefix split.  Each open-left block is
sent to its literal coefficient-one Heath--Brown form; the singleton
contributes exactly `|W|^2`. -/
theorem reflectedPrefixPairMoment_le_sum_differenceQuadraticForms
    (J : ℕ) (r : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
      ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) ((t - u) - r)‖ ^ 2) ≤
      ((J + 1 : ℕ) : ℝ) *
        ((W.card : ℝ) ^ 2 +
          ∑ j ∈ Finset.range J,
            differenceQuadraticForm (fun _ => (1 : ℂ)) (2 ^ j) W) := by
  let C : ℝ := ((J + 1 : ℕ) : ℝ)
  let blockSq : ℝ → ℝ → ℕ → ℝ := fun t u j =>
    ‖reflectedDyadicIocPolynomial (2 ^ j) ((t - u) - r)‖ ^ 2
  have hraw :
      (∑ t ∈ W, ∑ u ∈ W,
        ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
          (2 ^ J) ((t - u) - r)‖ ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W,
          C * (1 + ∑ j ∈ Finset.range J, blockSq t u j) := by
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro u hu
    simpa [C, blockSq] using
      norm_reflectedDirichletPolynomial_pow_sq_le_dyadicIoc
        J ((t - u) - r)
  have hblocks :
      (∑ j ∈ Finset.range J,
        ∑ t ∈ W, ∑ u ∈ W, blockSq t u j) ≤
      ∑ j ∈ Finset.range J,
        differenceQuadraticForm (fun _ => (1 : ℂ)) (2 ^ j) W := by
    apply Finset.sum_le_sum
    intro j hj
    simpa [blockSq] using
      reflectedDyadicIocPairMoment_le_oneCoefficient (2 ^ j) r W
  have hswap :
      (∑ t ∈ W, ∑ u ∈ W, ∑ j ∈ Finset.range J, blockSq t u j) =
        ∑ j ∈ Finset.range J, ∑ t ∈ W, ∑ u ∈ W, blockSq t u j := by
    calc
      (∑ t ∈ W, ∑ u ∈ W, ∑ j ∈ Finset.range J, blockSq t u j) =
        ∑ t ∈ W, ∑ j ∈ Finset.range J, ∑ u ∈ W, blockSq t u j := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.sum_comm]
      _ = ∑ j ∈ Finset.range J, ∑ t ∈ W, ∑ u ∈ W, blockSq t u j := by
          rw [Finset.sum_comm]
  have hrearrange :
      (∑ t ∈ W, ∑ u ∈ W,
          C * (1 + ∑ j ∈ Finset.range J, blockSq t u j)) =
        C * ((W.card : ℝ) ^ 2 +
          ∑ j ∈ Finset.range J,
            ∑ t ∈ W, ∑ u ∈ W, blockSq t u j) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
    have hfactor :
        (∑ t ∈ W, ∑ u ∈ W,
          C * ∑ j ∈ Finset.range J, blockSq t u j) =
          C * (∑ t ∈ W, ∑ u ∈ W,
            ∑ j ∈ Finset.range J, blockSq t u j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.mul_sum]
    rw [hfactor, hswap]
    simp
    ring
  calc
    (∑ t ∈ W, ∑ u ∈ W,
      ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
        (2 ^ J) ((t - u) - r)‖ ^ 2) ≤
      ∑ t ∈ W, ∑ u ∈ W,
        C * (1 + ∑ j ∈ Finset.range J, blockSq t u j) := hraw
    _ = C * ((W.card : ℝ) ^ 2 +
        ∑ j ∈ Finset.range J,
          ∑ t ∈ W, ∑ u ∈ W, blockSq t u j) := hrearrange
    _ ≤ C * ((W.card : ℝ) ^ 2 +
        ∑ j ∈ Finset.range J,
          differenceQuadraticForm (fun _ => (1 : ℂ)) (2 ^ j) W) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl hblocks)
        (by positivity)
    _ = _ := rfl

/-! ## The weighted Cauchy step in the Mellin variable -/

/-- Weighted Cauchy--Schwarz on the literal central Mellin interval.  This is
the scalar inequality used before the finite `W x W` sum is interchanged
with the `r`-integral. -/
theorem integral_weight_mul_sq_le
    {w f : ℝ → ℝ} {R : ℝ}
    (hw : Continuous w) (hf : Continuous f)
    (hw0 : ∀ r, 0 ≤ w r) (hf0 : ∀ r, 0 ≤ f r) :
    (∫ r : ℝ in Set.Ioc (-R) R, w r * f r) ^ 2 ≤
      (∫ r : ℝ in Set.Ioc (-R) R, w r) *
        (∫ r : ℝ in Set.Ioc (-R) R, w r * f r ^ 2) := by
  let s : Set ℝ := Set.Ioc (-R) R
  let F : ℝ → ℝ := s.indicator (fun r => Real.sqrt (w r))
  let G : ℝ → ℝ := s.indicator (fun r => Real.sqrt (w r) * f r)
  have hs : MeasurableSet s := measurableSet_Ioc
  have hFmeas : AEStronglyMeasurable F :=
    ((Real.continuous_sqrt.comp hw).aestronglyMeasurable.indicator hs)
  have hGmeas : AEStronglyMeasurable G :=
    (((Real.continuous_sqrt.comp hw).mul hf).aestronglyMeasurable.indicator hs)
  have hwInt : IntegrableOn w s :=
    hw.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hwf2Int : IntegrableOn (fun r => w r * f r ^ 2) s :=
    (hw.mul (hf.pow 2)).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hF2 : Integrable (fun r => F r ^ 2) := by
    apply (hwInt.integrable_indicator hs).congr
    filter_upwards with r
    by_cases hr : r ∈ s
    · simp [F, hr, Real.sq_sqrt (hw0 r)]
    · simp [F, hr]
  have hG2 : Integrable (fun r => G r ^ 2) := by
    apply (hwf2Int.integrable_indicator hs).congr
    filter_upwards with r
    by_cases hr : r ∈ s
    · simp [G, hr, mul_pow, Real.sq_sqrt (hw0 r)]
    · simp [G, hr]
  have hF0 : ∀ r, 0 ≤ F r := by
    intro r
    by_cases hr : r ∈ s <;> simp [F, hr, Real.sqrt_nonneg]
  have hG0 : ∀ r, 0 ≤ G r := by
    intro r
    by_cases hr : r ∈ s
    · simp only [G, Set.indicator_of_mem hr]
      exact mul_nonneg (Real.sqrt_nonneg _) (hf0 r)
    · simp [G, hr]
  have hcs := GuthMaynardJIteration.integral_mul_sq_le
    F G hFmeas hGmeas hF2 hG2 hF0 hG0
  have hleft :
      (∫ r : ℝ, F r * G r) =
        ∫ r : ℝ in s, w r * f r := by
    rw [← MeasureTheory.integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ s
    · simp only [F, G, Set.indicator_of_mem hr]
      calc
        Real.sqrt (w r) * (Real.sqrt (w r) * f r) =
            Real.sqrt (w r) ^ 2 * f r := by ring
        _ = w r * f r := by rw [Real.sq_sqrt (hw0 r)]
    · simp [F, G, hr]
  have hfirst :
      (∫ r : ℝ, F r ^ 2) = ∫ r : ℝ in s, w r := by
    rw [← MeasureTheory.integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ s
    · simp [F, hr, Real.sq_sqrt (hw0 r)]
    · simp [F, hr]
  have hsecond :
      (∫ r : ℝ, G r ^ 2) =
        ∫ r : ℝ in s, w r * f r ^ 2 := by
    rw [← MeasureTheory.integral_indicator hs]
    apply integral_congr_ae
    filter_upwards with r
    by_cases hr : r ∈ s
    · simp [G, hr, mul_pow, Real.sq_sqrt (hw0 r)]
    · simp [G, hr]
  simpa only [s, hleft, hfirst, hsecond] using hcs

/-- Cauchy--Schwarz specialized to the literal Mellin weight and one
reflected dyadic polynomial from Lemma 6.2. -/
theorem mellin_reflectedDyadic_integral_sq_le
    (M : ℕ) (t u R : ℝ) :
    (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖ *
          ‖reflectedDyadicPolynomial M ((t - u) - r)‖) ^ 2 ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖) *
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖ *
          ‖reflectedDyadicPolynomial M ((t - u) - r)‖ ^ 2) := by
  apply integral_weight_mul_sq_le
  · exact GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm
  · unfold reflectedDyadicPolynomial reflectionScalePhase
    fun_prop
  · intro r
    exact norm_nonneg _
  · intro r
    exact norm_nonneg _

/-- Finite-pair weighted Cauchy and Fubini in a reusable exact form.  The
sole arithmetic input is the pointwise pair-moment bound `hpair`. -/
theorem finitePair_weighted_integral_sq_le
    {ι : Type*} (S : Finset ι) {w : ℝ → ℝ}
    {f : ι → ι → ℝ → ℝ} {R Q : ℝ}
    (hw : Continuous w) (hf : ∀ x y, Continuous (f x y))
    (hw0 : ∀ r, 0 ≤ w r) (hf0 : ∀ x y r, 0 ≤ f x y r)
    (hpair : ∀ r, (∑ x ∈ S, ∑ y ∈ S, f x y r ^ 2) ≤ Q) :
    (∑ x ∈ S, ∑ y ∈ S,
      (∫ r : ℝ in Set.Ioc (-R) R, w r * f x y r) ^ 2) ≤
      (∫ r : ℝ in Set.Ioc (-R) R, w r) ^ 2 * Q := by
  let s : Set ℝ := Set.Ioc (-R) R
  let A : ℝ := ∫ r : ℝ in s, w r
  have hwf2 : ∀ x y,
      IntegrableOn (fun r => w r * f x y r ^ 2) s := by
    intro x y
    exact (hw.mul ((hf x y).pow 2)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hA0 : 0 ≤ A := by
    unfold A
    exact integral_nonneg hw0
  have hcs :
      (∑ x ∈ S, ∑ y ∈ S,
        (∫ r : ℝ in s, w r * f x y r) ^ 2) ≤
      ∑ x ∈ S, ∑ y ∈ S,
        A * (∫ r : ℝ in s, w r * f x y r ^ 2) := by
    apply Finset.sum_le_sum
    intro x hx
    apply Finset.sum_le_sum
    intro y hy
    simpa [s, A] using
      integral_weight_mul_sq_le hw (hf x y) hw0 (hf0 x y)
  have hsumIntegral :
      (∑ x ∈ S, ∑ y ∈ S,
        ∫ r : ℝ in s, w r * f x y r ^ 2) =
      ∫ r : ℝ in s,
        ∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2 := by
    rw [integral_finsetSum S]
    · apply Finset.sum_congr rfl
      intro x hx
      rw [integral_finsetSum S]
      intro y hy
      exact hwf2 x y
    · intro x hx
      exact integrable_finsetSum S (fun y hy => hwf2 x y)
  have hpoint : ∀ r,
      (∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2) ≤ w r * Q := by
    intro r
    calc
      (∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2) =
          w r * (∑ x ∈ S, ∑ y ∈ S, f x y r ^ 2) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x hx
            rw [Finset.mul_sum]
      _ ≤ w r * Q := mul_le_mul_of_nonneg_left (hpair r) (hw0 r)
  have hleftInt : IntegrableOn
      (fun r => ∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2) s :=
    integrable_finsetSum S (fun x hx =>
      integrable_finsetSum S (fun y hy => hwf2 x y))
  have hrightInt : IntegrableOn (fun r => w r * Q) s :=
    (hw.mul continuous_const).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hintegral :
      (∫ r : ℝ in s,
        ∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2) ≤
      ∫ r : ℝ in s, w r * Q :=
    integral_mono hleftInt hrightInt hpoint
  have hrightEq : (∫ r : ℝ in s, w r * Q) = A * Q := by
    rw [MeasureTheory.integral_mul_const]
  calc
    (∑ x ∈ S, ∑ y ∈ S,
      (∫ r : ℝ in Set.Ioc (-R) R, w r * f x y r) ^ 2) ≤
      ∑ x ∈ S, ∑ y ∈ S,
        A * (∫ r : ℝ in s, w r * f x y r ^ 2) := hcs
    _ = A * (∑ x ∈ S, ∑ y ∈ S,
        ∫ r : ℝ in s, w r * f x y r ^ 2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.mul_sum]
    _ = A * (∫ r : ℝ in s,
        ∑ x ∈ S, ∑ y ∈ S, w r * f x y r ^ 2) := by
          rw [← hsumIntegral]
    _ ≤ A * (∫ r : ℝ in s, w r * Q) :=
      mul_le_mul_of_nonneg_left hintegral hA0
    _ = A ^ 2 * Q := by rw [hrightEq]; ring
    _ = _ := rfl

/-- The literal Lemma-6.2 prefix, including its complete dyadic logarithmic
cost, after weighted Cauchy and finite Fubini. -/
theorem mellin_reflectedPrefix_pair_integral_sq_le
    (J : ℕ) (R : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖ *
          ‖GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
            (2 ^ J) ((t - u) - r)‖) ^ 2) ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
      (((J + 1 : ℕ) : ℝ) *
        ((W.card : ℝ) ^ 2 +
          ∑ j ∈ Finset.range J,
            differenceQuadraticForm (fun _ => (1 : ℂ)) (2 ^ j) W)) := by
  apply finitePair_weighted_integral_sq_le W
  · exact GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm
  · intro t u
    unfold GuthMaynardLemma62FiniteFactorization.reflectedDirichletPolynomial
      reflectionScalePhase
    fun_prop
  · intro r
    exact norm_nonneg _
  · intro t u r
    exact norm_nonneg _
  · intro r
    exact reflectedPrefixPairMoment_le_sum_differenceQuadraticForms J r W

/-- The complete central Mellin contribution over `W x W` is controlled by
one coefficient-one Heath--Brown block.  This theorem performs both Cauchy in
`r` and the finite Fubini interchange; the only estimate after it is the
published difference-set inequality itself. -/
theorem mellin_reflectedDyadic_pair_integral_sq_le
    (M : ℕ) (R : ℝ) (W : Finset ℝ) :
    (∑ t ∈ W, ∑ u ∈ W,
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖ *
          ‖reflectedDyadicPolynomial M ((t - u) - r)‖) ^ 2) ≤
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖) ^ 2 *
        differenceQuadraticForm (fun _ => (1 : ℂ)) M W := by
  let s : Set ℝ := Set.Ioc (-R) R
  let wgt : ℝ → ℝ := fun r =>
    ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
      ((1 : ℂ) + r * Complex.I)‖
  let polySq : ℝ → ℝ → ℝ → ℝ := fun t u r =>
    ‖reflectedDyadicPolynomial M ((t - u) - r)‖ ^ 2
  let A : ℝ := ∫ r : ℝ in s, wgt r
  let Q : ℝ := differenceQuadraticForm (fun _ => (1 : ℂ)) M W
  have hw : Continuous wgt := by
    exact GuthMaynardLemma62Fubini.continuous_mellin_line_sectionThree.norm
  have hp : ∀ t u, Continuous (polySq t u) := by
    intro t u
    unfold polySq reflectedDyadicPolynomial reflectionScalePhase
    fun_prop
  have hwp : ∀ t u, IntegrableOn (fun r => wgt r * polySq t u r) s := by
    intro t u
    exact (hw.mul (hp t u)).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hA0 : 0 ≤ A := by
    unfold A
    exact integral_nonneg (fun r => norm_nonneg _)
  have hQ0 : 0 ≤ Q := by
    exact differenceQuadraticForm_nonneg _ _ _
  have hcs :
      (∑ t ∈ W, ∑ u ∈ W,
        (∫ r : ℝ in s, wgt r * Real.sqrt (polySq t u r)) ^ 2) ≤
        ∑ t ∈ W, ∑ u ∈ W,
          A * (∫ r : ℝ in s, wgt r * polySq t u r) := by
    apply Finset.sum_le_sum
    intro t ht
    apply Finset.sum_le_sum
    intro u hu
    have h := mellin_reflectedDyadic_integral_sq_le M t u R
    simpa [s, wgt, polySq, A, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg _)] using h
  have hsumIntegral :
      (∑ t ∈ W, ∑ u ∈ W,
        ∫ r : ℝ in s, wgt r * polySq t u r) =
      ∫ r : ℝ in s,
        ∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r := by
    rw [integral_finsetSum W]
    · apply Finset.sum_congr rfl
      intro t ht
      rw [integral_finsetSum W]
      intro u hu
      exact hwp t u
    · intro t ht
      exact integrable_finsetSum W (fun u hu => hwp t u)
  have hpoint : ∀ r,
      (∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r) ≤ wgt r * Q := by
    intro r
    have hpair := reflectedDyadicPairMoment_le_oneCoefficient M r W
    calc
      (∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r) =
          wgt r * (∑ t ∈ W, ∑ u ∈ W, polySq t u r) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t ht
            rw [Finset.mul_sum]
      _ ≤ wgt r * Q :=
        mul_le_mul_of_nonneg_left (by simpa [polySq, Q] using hpair)
          (norm_nonneg _)
  have hleftInt : IntegrableOn
      (fun r => ∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r) s :=
    integrable_finsetSum W (fun t ht =>
      integrable_finsetSum W (fun u hu => hwp t u))
  have hrightInt : IntegrableOn (fun r => wgt r * Q) s :=
    (hw.mul continuous_const).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  have hintegral :
      (∫ r : ℝ in s,
        ∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r) ≤
      ∫ r : ℝ in s, wgt r * Q :=
    integral_mono hleftInt hrightInt hpoint
  have hrightEq : (∫ r : ℝ in s, wgt r * Q) = A * Q := by
    rw [MeasureTheory.integral_mul_const]
  calc
    (∑ t ∈ W, ∑ u ∈ W,
      (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
            ((1 : ℂ) + r * Complex.I)‖ *
          ‖reflectedDyadicPolynomial M ((t - u) - r)‖) ^ 2) =
        ∑ t ∈ W, ∑ u ∈ W,
          (∫ r : ℝ in s, wgt r * Real.sqrt (polySq t u r)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t ht
            apply Finset.sum_congr rfl
            intro u hu
            simp [s, wgt, polySq]
    _ ≤ ∑ t ∈ W, ∑ u ∈ W,
          A * (∫ r : ℝ in s, wgt r * polySq t u r) := hcs
    _ = A * (∑ t ∈ W, ∑ u ∈ W,
          ∫ r : ℝ in s, wgt r * polySq t u r) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          rw [Finset.mul_sum]
    _ = A * (∫ r : ℝ in s,
          ∑ t ∈ W, ∑ u ∈ W, wgt r * polySq t u r) := by
          rw [← hsumIntegral]
    _ ≤ A * (∫ r : ℝ in s, wgt r * Q) :=
      mul_le_mul_of_nonneg_left hintegral hA0
    _ = A ^ 2 * Q := by rw [hrightEq]; ring
    _ = _ := rfl

/-- Exact consumer of the remaining published analytic leaf.  Everything on
the left is the concrete central output of Lemma 6.2; the only hypothesis not
proved in this file is `HeathBrownOneCoefficientCore`. -/
theorem mellin_reflectedDyadic_pair_integral_sq_le_of_oneCoefficientCore
    (hcore : HeathBrownOneCoefficientCore) {eta : ℝ} (heta : 0 < eta) :
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
            (C * Real.rpow T eta * heathBrownShape T M W) := by
  obtain ⟨C, T₀, hC, hT₀, hHB⟩ := hcore eta heta
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T M R W hT hM hsep hinterval
  have hcentral := mellin_reflectedDyadic_pair_integral_sq_le M R W
  have hdiff := hHB T M W hT hM hsep hinterval
  have hweight :
      0 ≤ (∫ r : ℝ in Set.Ioc (-R) R,
        ‖mellin GuthMaynardSectionThreeCutoff.sectionThreeCutoff
          ((1 : ℂ) + r * Complex.I)‖) ^ 2 := sq_nonneg _
  exact hcentral.trans (mul_le_mul_of_nonneg_left hdiff hweight)

end

end GuthMaynardLemma62PairAssembly

#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicPolynomial_eq_displayed_swap
#print axioms GuthMaynardLemma62PairAssembly.reflectedDirichletPolynomial_pow_succ_eq_add_dyadicIoc
#print axioms GuthMaynardLemma62PairAssembly.reflectedDirichletPolynomial_pow_eq_one_add_sum_dyadicIoc
#print axioms GuthMaynardLemma62PairAssembly.norm_reflectedDirichletPolynomial_pow_sq_le_dyadicIoc
#print axioms GuthMaynardLemma62PairAssembly.reflectedPrefixPairMoment_le_sum_differenceQuadraticForms
#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicIocPolynomial_eq_dirichlet_swap
#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicIocPairMoment_eq_differenceQuadraticForm
#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicIocPairMoment_le_oneCoefficient
#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicPairMoment_eq_differenceQuadraticForm
#print axioms GuthMaynardLemma62PairAssembly.reflectedDyadicPairMoment_le_oneCoefficient
#print axioms GuthMaynardLemma62PairAssembly.integral_weight_mul_sq_le
#print axioms GuthMaynardLemma62PairAssembly.mellin_reflectedDyadic_integral_sq_le
#print axioms GuthMaynardLemma62PairAssembly.finitePair_weighted_integral_sq_le
#print axioms GuthMaynardLemma62PairAssembly.mellin_reflectedPrefix_pair_integral_sq_le
#print axioms GuthMaynardLemma62PairAssembly.mellin_reflectedDyadic_pair_integral_sq_le
#print axioms GuthMaynardLemma62PairAssembly.mellin_reflectedDyadic_pair_integral_sq_le_of_oneCoefficientCore
