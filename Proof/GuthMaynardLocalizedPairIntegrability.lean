import GuthMaynardJIterationMediumRegionIntegration

/-!
# Integrability of the literal first-Poisson localized pair sum

The corrected whole-frequency theorem previously carried low- and
medium-region integrability of this finite, windowed sum as hypotheses.  The
sum is a finite sum of continuous terms cut off by bounded measurable
intervals, so those hypotheses are discharged here.
-/

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Complex-valued version of the fixed-product indicator expansion. -/
theorem sourceFirstPoissonLocalizedPairSum_eq_indicatorSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) :
    sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi =
      ∑ p ∈ m1Range ×ˢ ellRange,
        (sourceMediumPairWindow M3 B p).indicator
          (sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p) xi := by
  unfold sourceFirstPoissonLocalizedPairSum sourceMediumLocalizedPairs
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hwindow :
      |xi - (p.1 : ℝ) * (p.2 : ℝ)| < (|(p.1 : ℝ)| / M3) * B
  · have hmem : xi ∈ sourceMediumPairWindow M3 B p :=
      mem_sourceMediumPairWindow_iff.mpr hwindow
    rw [if_pos hwindow, Set.indicator_of_mem hmem]
  · have hnotmem : xi ∉ sourceMediumPairWindow M3 B p := by
      intro hmem
      exact hwindow (mem_sourceMediumPairWindow_iff.mp hmem)
    rw [if_neg hwindow, Set.indicator_of_notMem hnotmem]

/-- Each untruncated localized-pair summand is continuous in frequency when
the two Fourier fields are continuous. -/
theorem continuous_sourceFirstPoissonLocalizedPairTerm
    (m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hF : Continuous F) (hfhat : Continuous fhat)
    (M3 : ℝ) (p : ℤ × ℤ) :
    Continuous (sourceFirstPoissonLocalizedPairTerm
      m2Range F fhat M3 p) := by
  unfold sourceFirstPoissonLocalizedPairTerm
  exact (continuous_const.mul
    (hF.comp (continuous_const.mul
      (continuous_const.sub (continuous_id.div_const _))))).mul
    (continuous_sourceCorrectedM2FourierInner m2Range fhat hfhat p.1)

/-- The squared norm of one windowed pair term is globally integrable. -/
theorem integrable_norm_sq_sourceFirstPoissonPairIndicator
    (m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hF : Continuous F) (hfhat : Continuous fhat)
    {M3 B : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B)
    (p : ℤ × ℤ) :
    Integrable (fun xi : ℝ =>
      ‖(sourceMediumPairWindow M3 B p).indicator
        (sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p) xi‖ ^ 2) := by
  let c : ℝ := (p.1 : ℝ) * (p.2 : ℝ)
  let r : ℝ := (|(p.1 : ℝ)| / M3) * B
  have hr : 0 ≤ r := mul_nonneg (div_nonneg (abs_nonneg _) hM3.le) hB
  have hsub : sourceMediumPairWindow M3 B p ⊆ Set.Icc (c - r) (c + r) := by
    intro xi hxi
    change |xi - c| < r at hxi
    rw [abs_lt] at hxi
    constructor <;> linarith
  let term : ℝ → ℂ :=
    sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p
  have hterm : Continuous term :=
    continuous_sourceFirstPoissonLocalizedPairTerm
      m2Range F fhat hF hfhat M3 p
  have hon : IntegrableOn (fun xi => ‖term xi‖ ^ 2)
      (sourceMediumPairWindow M3 B p) :=
    (hterm.norm.pow 2).integrableOn_Icc.mono_set hsub
  have heq : (fun xi : ℝ =>
      ‖(sourceMediumPairWindow M3 B p).indicator term xi‖ ^ 2) =
      (sourceMediumPairWindow M3 B p).indicator
        (fun xi => ‖term xi‖ ^ 2) := by
    funext xi
    by_cases hxi : xi ∈ sourceMediumPairWindow M3 B p
    · simp [Set.indicator_of_mem hxi]
    · simp [Set.indicator_of_notMem hxi]
  rw [heq]
  exact hon.integrable_indicator (measurableSet_sourceMediumPairWindow M3 B p)

/-- The full literal localized first-Poisson field has integrable squared
norm on the whole line, hence on both source frequency regions. -/
theorem integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hF : Continuous F) (hfhat : Continuous fhat)
    {M3 B : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B) :
    Integrable (fun xi : ℝ =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi‖ ^ 2) := by
  let ranges : Finset (ℤ × ℤ) := m1Range ×ˢ ellRange
  let term : (ℤ × ℤ) → ℝ → ℂ := fun p =>
    sourceFirstPoissonLocalizedPairTerm m2Range F fhat M3 p
  let g : (ℤ × ℤ) → ℝ → ℂ := fun p =>
    (sourceMediumPairWindow M3 B p).indicator (term p)
  let major : ℝ → ℝ := fun xi =>
    (ranges.card : ℝ) * ∑ p ∈ ranges, ‖g p xi‖ ^ 2
  have hgMeas : ∀ p ∈ ranges, AEStronglyMeasurable (g p) := by
    intro p hp
    exact (continuous_sourceFirstPoissonLocalizedPairTerm
      m2Range F fhat hF hfhat M3 p).aestronglyMeasurable.indicator
        (measurableSet_sourceMediumPairWindow M3 B p)
  have hsumMeas : AEStronglyMeasurable
      (fun xi => ∑ p ∈ ranges, g p xi) := by
    have hfun : (∑ p ∈ ranges, g p) =
        (fun xi => ∑ p ∈ ranges, g p xi) := by
      funext xi
      simp only [Finset.sum_apply]
    rw [← hfun]
    exact Finset.aestronglyMeasurable_sum ranges hgMeas
  have hmajorInt : Integrable major := by
    dsimp only [major]
    apply Integrable.const_mul
    apply integrable_finsetSum ranges
    intro p hp
    exact integrable_norm_sq_sourceFirstPoissonPairIndicator
      m2Range F fhat hF hfhat hM3 hB p
  have hsumEq : (fun xi =>
      sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi) = fun xi => ∑ p ∈ ranges, g p xi := by
    funext xi
    exact sourceFirstPoissonLocalizedPairSum_eq_indicatorSum
      m1Range ellRange m2Range F fhat M3 B xi
  have htargetMeas : AEStronglyMeasurable (fun xi =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi‖ ^ 2) := by
    have heq : (fun xi =>
        ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
          F fhat M3 B xi‖ ^ 2) =
        (fun xi => ‖∑ p ∈ ranges, g p xi‖ ^ 2) := by
      funext xi
      rw [congrFun hsumEq xi]
    rw [heq]
    exact hsumMeas.norm.pow 2
  apply hmajorInt.mono' htargetMeas
  filter_upwards with xi
  have hbound := norm_finset_sum_sq_le_card_mul_sum_norm_sq
    ranges (fun p => g p xi)
  rw [congrFun hsumEq xi]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [major] using hbound

/-- Direct source-facing discharge of both regional integrability premises. -/
theorem sourceFirstPoissonLocalizedPairSum_regionIntegrable
    (m1Range ellRange m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (hF : Continuous F) (hfhat : Continuous fhat)
    {M3 B a b : ℝ} (hM3 : 0 < M3) (hB : 0 ≤ B) :
    IntegrableOn (fun xi : ℝ =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi‖ ^ 2) (lowFrequencyRegion a) ∧
    IntegrableOn (fun xi : ℝ =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        F fhat M3 B xi‖ ^ 2) (mediumFrequencyRegion a b) := by
  have h := integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
    m1Range ellRange m2Range F fhat hF hfhat hM3 hB
  exact ⟨h.integrableOn, h.integrableOn⟩

#print axioms GuthMaynardJIteration.sourceFirstPoissonLocalizedPairSum_eq_indicatorSum
#print axioms GuthMaynardJIteration.continuous_sourceFirstPoissonLocalizedPairTerm
#print axioms GuthMaynardJIteration.integrable_norm_sq_sourceFirstPoissonPairIndicator
#print axioms GuthMaynardJIteration.integrable_norm_sq_sourceFirstPoissonLocalizedPairSum
#print axioms GuthMaynardJIteration.sourceFirstPoissonLocalizedPairSum_regionIntegrable

end GuthMaynardJIteration
