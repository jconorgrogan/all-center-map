import GuthMaynardJIterationFirstPoissonLocalization

/-!
# Finite `m₁` assembly of the first-Poisson localization

This is the finite-range triangle-inequality step in Guth--Maynard (9.7).
The full and retained expressions are literal finite `m₁` sums.  The error
is bounded first by the exact sum of corrected Fourier inners and only then by
a cardinality/supremum estimate.
-/

open scoped BigOperators Real FourierTransform

noncomputable section
namespace GuthMaynardJIteration

def sourceFirstPoissonFullFinite
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 xi : ℝ) : ℂ :=
  ∑ m1 ∈ m1Range,
    sourceFirstPoissonContribution F m2Range fhat M3 m1 xi

def sourceFirstPoissonRetainedFinite
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    (M3 B xi : ℝ) : ℂ :=
  ∑ m1 ∈ m1Range,
    sourceFirstPoissonRetainedContribution F m2Range fhat M3 B m1 xi

/-- Exact finite-range identity: the discarded part of the source formula is
the finite `m₁` sum of first-Poisson tails times the corrected
`|m₂/m₁|` inner. -/
theorem sourceFirstPoissonFullFinite_sub_retained
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {K0 M3 B : ℝ} (hM3 : 0 < M3)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0) (xi : ℝ) :
    sourceFirstPoissonFullFinite m1Range m2Range F fhat M3 xi -
        sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi =
      ∑ m1 ∈ m1Range,
        sourceFirstPoissonTail F M3 B (m1 : ℝ) xi *
          sourceCorrectedM2FourierInner m2Range fhat m1 xi := by
  unfold sourceFirstPoissonFullFinite sourceFirstPoissonRetainedFinite
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  exact sourceFirstPoissonContribution_sub_retained F m2Range fhat hM3
    hdecay2 m1 (hm1 m1 hm1mem) xi

/-- Exact triangle-inequality majorant before any cardinality loss. -/
theorem norm_sourceFirstPoissonFullFinite_sub_retained_le
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ)
    {K0 M3 B : ℝ} (hM3 : 0 < M3)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0) (xi : ℝ) :
    ‖sourceFirstPoissonFullFinite m1Range m2Range F fhat M3 xi -
        sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi‖ ≤
      ∑ m1 ∈ m1Range,
        ‖sourceFirstPoissonTail F M3 B (m1 : ℝ) xi‖ *
          ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ := by
  rw [sourceFirstPoissonFullFinite_sub_retained m1Range m2Range F fhat
    hM3 hdecay2 hm1 xi]
  calc
    ‖∑ m1 ∈ m1Range,
        sourceFirstPoissonTail F M3 B (m1 : ℝ) xi *
          sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ ≤
      ∑ m1 ∈ m1Range,
        ‖sourceFirstPoissonTail F M3 B (m1 : ℝ) xi *
          sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [norm_mul]

/-- Uniform finite-range `T⁻¹⁰⁰` truncation with the exact sum of
corrected Fourier inners retained. -/
theorem norm_sourceFirstPoissonFullFinite_sub_retained_le_time_neg100
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ) (q : ℕ)
    {K0 K M3 B Y C T : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z, ‖F z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (xi : ℝ) (hxi : ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y) :
    ‖sourceFirstPoissonFullFinite m1Range m2Range F fhat M3 xi -
        sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi‖ ≤
      (C / T ^ 100) *
        ∑ m1 ∈ m1Range,
          ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ := by
  refine (norm_sourceFirstPoissonFullFinite_sub_retained_le
    m1Range m2Range F fhat hM3 hdecay2 hm1 xi).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro m1 hm1mem
  exact mul_le_mul_of_nonneg_right
    (norm_sourceFirstPoissonTail_le_time_neg100 F q hK hM3 hB hY hT
      hdecay hbudget (by exact_mod_cast hm1 m1 hm1mem) (hxi m1 hm1mem))
    (norm_nonneg _)

/-- The conventional `O(T⁻¹⁰⁰)` form after bounding the number of
`m₁` values and the corrected Fourier inner.  All losses are visible in
`L` and `H`; none are absorbed into the Poisson lemma. -/
theorem norm_sourceFirstPoissonFullFinite_sub_retained_le_card
    (m1Range m2Range : Finset ℤ) (F fhat : ℝ → ℂ) (q : ℕ)
    {K0 K M3 B Y C T L H : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y) (hT : 0 < T)
    (hdecay2 : ∀ z, ‖F z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z, ‖F z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hcard : (m1Range.card : ℝ) ≤ L)
    (xi : ℝ)
    (hinner : ∀ m1 ∈ m1Range,
      ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖ ≤ H)
    (hxi : ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y) :
    ‖sourceFirstPoissonFullFinite m1Range m2Range F fhat M3 xi -
        sourceFirstPoissonRetainedFinite m1Range m2Range F fhat M3 B xi‖ ≤
      (C / T ^ 100) * (L * H) := by
  refine (norm_sourceFirstPoissonFullFinite_sub_retained_le_time_neg100
    m1Range m2Range F fhat q hK hM3 hB hY hT hdecay2 hdecay hbudget
      hm1 xi hxi).trans ?_
  have hfactor : 0 ≤ C / T ^ 100 := div_nonneg hC (pow_pos hT _).le
  apply mul_le_mul_of_nonneg_left _ hfactor
  calc
    (∑ m1 ∈ m1Range,
        ‖sourceCorrectedM2FourierInner m2Range fhat m1 xi‖) ≤
        ∑ _m1 ∈ m1Range, H := by
      apply Finset.sum_le_sum
      intro m1 hm1mem
      exact hinner m1 hm1mem
    _ = (m1Range.card : ℝ) * H := by simp
    _ ≤ L * H := mul_le_mul_of_nonneg_right hcard hH

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceFirstPoissonFullFinite_sub_retained
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonFullFinite_sub_retained_le
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonFullFinite_sub_retained_le_time_neg100
#print axioms GuthMaynardJIteration.norm_sourceFirstPoissonFullFinite_sub_retained_le_card
