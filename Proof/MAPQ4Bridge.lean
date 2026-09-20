import Mathlib

/-!
# Axiom-free finite bridge from translated variance to Q4+ and density one

This file certifies only downstream finite algebra.  In particular, it does
not state MAP, a major-arc estimate, a von Mangoldt variance theorem, or a
singular-series estimate as an axiom.  Such analytic inputs can later be
supplied as ordinary hypotheses to the implication lemmas below.
-/

namespace MAPQ4Bridge

open scoped BigOperators

noncomputable section

/-- A finite additive correlation.  For the prime-pair application, `support`
is the integer interval `(X, 2X]`, and both coefficient functions are the von
Mangoldt function (with prime powers retained). -/
def finiteCorrelation (support : Finset ℤ) (f g : ℤ → ℝ) (h : ℤ) : ℝ :=
  ∑ n ∈ support, f n * g (n + h)

/-- The model main term `X * singular h`.  No value at shift zero is needed,
because all physical moments below are taken over `translatedWindow`. -/
def modelMain (X : ℝ) (singular : ℤ → ℝ) (h : ℤ) : ℝ :=
  X * singular h

/-- The literal translated integer window `|h - h₀| ≤ H`, with the zero shift
deleted.  `H` remains the normalization parameter; it is not replaced by the
cardinality of this finset. -/
def translatedWindow (h₀ : ℤ) (H : ℕ) : Finset ℤ :=
  (Finset.Icc (h₀ - (H : ℤ)) (h₀ + (H : ℤ))).erase 0

/-- Exact membership in the translated, zero-deleted window. -/
theorem mem_translatedWindow_iff {h h₀ : ℤ} {H : ℕ} :
    h ∈ translatedWindow h₀ H ↔
      h₀ - (H : ℤ) ≤ h ∧ h ≤ h₀ + (H : ℤ) ∧ h ≠ 0 := by
  simp only [translatedWindow, Finset.mem_erase, ne_eq, Finset.mem_Icc]
  constructor
  · rintro ⟨hne, hlo, hhi⟩
    omega
  · rintro ⟨hlo, hhi, hne⟩
    omega

/-- In particular, the forbidden zero shift never enters the window. -/
theorem zero_not_mem_translatedWindow (h₀ : ℤ) (H : ℕ) :
    0 ∉ translatedWindow h₀ H := by
  simp [translatedWindow]

/-- Squared error from a supplied model over a finite shift set. -/
def variance (I : Finset ℤ) (R model : ℤ → ℝ) : ℝ :=
  ∑ h ∈ I, (R h - model h) ^ 2

/-- The Q4 (correlation-square) moment over a finite shift set. -/
def q4Moment (I : Finset ℤ) (R : ℤ → ℝ) : ℝ :=
  ∑ h ∈ I, (R h) ^ 2

/-- The exact singular-series second moment appearing in the Q4+ main term. -/
def modelSecondMoment (I : Finset ℤ) (singular : ℤ → ℝ) : ℝ :=
  ∑ h ∈ I, (singular h) ^ 2

/-- The shifts whose pointwise error is strictly larger than `threshold`. -/
def exceptionSet (I : Finset ℤ) (R model : ℤ → ℝ) (threshold : ℝ) : Finset ℤ :=
  I.filter fun h ↦ threshold < |R h - model h|

/-- The corresponding exception count, coerced to `ℝ` for quantitative bounds. -/
def exceptionCount (I : Finset ℤ) (R model : ℤ → ℝ) (threshold : ℝ) : ℝ :=
  ((exceptionSet I R model threshold).card : ℝ)

theorem variance_nonneg (I : Finset ℤ) (R model : ℤ → ℝ) :
    0 ≤ variance I R model := by
  simp only [variance]
  positivity

theorem modelSecondMoment_nonneg (I : Finset ℤ) (singular : ℤ → ℝ) :
    0 ≤ modelSecondMoment I singular := by
  simp only [modelSecondMoment]
  positivity

/-- Values assigned to a model at the excluded shift zero cannot affect its
translated second moment.  This records formally that no mathematical value
of the singular series at zero is used. -/
theorem translated_modelSecondMoment_congr_off_zero
    (h₀ : ℤ) (H : ℕ) (singular₁ singular₂ : ℤ → ℝ)
    (hoff : ∀ h, h ≠ 0 → singular₁ h = singular₂ h) :
    modelSecondMoment (translatedWindow h₀ H) singular₁ =
      modelSecondMoment (translatedWindow h₀ H) singular₂ := by
  apply Finset.sum_congr rfl
  intro h hh
  rw [hoff h ((mem_translatedWindow_iff.mp hh).2.2)]

/-- The translated variance is likewise independent of the model's arbitrary
extension to the deleted zero shift. -/
theorem translated_variance_congr_off_zero
    (h₀ : ℤ) (H : ℕ) (R model₁ model₂ : ℤ → ℝ)
    (hoff : ∀ h, h ≠ 0 → model₁ h = model₂ h) :
    variance (translatedWindow h₀ H) R model₁ =
      variance (translatedWindow h₀ H) R model₂ := by
  apply Finset.sum_congr rfl
  intro h hh
  rw [hoff h ((mem_translatedWindow_iff.mp hh).2.2)]

/-- Exact square expansion behind the variance-to-Q4 implication. -/
theorem q4_expansion (I : Finset ℤ) (R singular : ℤ → ℝ) (X : ℝ) :
    q4Moment I R =
      X ^ 2 * modelSecondMoment I singular +
        2 * X * (∑ h ∈ I, singular h * (R h - modelMain X singular h)) +
          variance I R (modelMain X singular) := by
  simp only [q4Moment, modelSecondMoment, variance, modelMain]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  ring

/-- Finite Cauchy--Schwarz for the singular-series/error cross term. -/
theorem crossTerm_abs_le (I : Finset ℤ) (R singular : ℤ → ℝ) (X : ℝ) :
    |∑ h ∈ I, singular h * (R h - modelMain X singular h)| ≤
      Real.sqrt (modelSecondMoment I singular) *
        Real.sqrt (variance I R (modelMain X singular)) := by
  let e : ℤ → ℝ := fun h ↦ R h - modelMain X singular h
  have hupper :
      (∑ h ∈ I, singular h * e h) ≤
        Real.sqrt (∑ h ∈ I, (singular h) ^ 2) *
          Real.sqrt (∑ h ∈ I, (e h) ^ 2) := by
    exact Real.sum_mul_le_sqrt_mul_sqrt I singular e
  have hlower :
      -(Real.sqrt (∑ h ∈ I, (singular h) ^ 2) *
          Real.sqrt (∑ h ∈ I, (e h) ^ 2)) ≤
        (∑ h ∈ I, singular h * e h) := by
    have hneg := Real.sum_mul_le_sqrt_mul_sqrt I (fun h ↦ -singular h) e
    have hneg' :
        -(∑ h ∈ I, singular h * e h) ≤
          Real.sqrt (∑ h ∈ I, (singular h) ^ 2) *
            Real.sqrt (∑ h ∈ I, (e h) ^ 2) := by
      simpa [Finset.sum_neg_distrib] using hneg
    linarith
  rw [abs_le]
  simpa [e, modelSecondMoment, variance] using And.intro hlower hupper

/-- Strong finite form of variance plus Cauchy: the Q4 moment differs from
its exact model moment by at most the variance plus the explicit cross term.
This is the reusable downstream implication; all analytic estimates remain
ordinary hypotheses in its corollaries. -/
theorem q4_deviation_le (I : Finset ℤ) (R singular : ℤ → ℝ) (X : ℝ) :
    |q4Moment I R - X ^ 2 * modelSecondMoment I singular| ≤
      variance I R (modelMain X singular) +
        2 * |X| * Real.sqrt
          (modelSecondMoment I singular * variance I R (modelMain X singular)) := by
  let C : ℝ := ∑ h ∈ I, singular h * (R h - modelMain X singular h)
  let V : ℝ := variance I R (modelMain X singular)
  let M : ℝ := modelSecondMoment I singular
  have hV : 0 ≤ V := by
    dsimp [V, variance]
    positivity
  have hM : 0 ≤ M := by
    dsimp [M, modelSecondMoment]
    positivity
  have hcross : |C| ≤ Real.sqrt M * Real.sqrt V := by
    simpa [C, M, V] using crossTerm_abs_le I R singular X
  have hexpand : q4Moment I R - X ^ 2 * M = 2 * X * C + V := by
    rw [q4_expansion I R singular X]
    simp only [M, C, V]
    ring
  rw [hexpand]
  calc
    |2 * X * C + V| ≤ |2 * X * C| + |V| := abs_add_le _ _
    _ = 2 * |X| * |C| + V := by rw [abs_mul, abs_mul, abs_of_nonneg hV]; norm_num
    _ ≤ 2 * |X| * (Real.sqrt M * Real.sqrt V) + V := by
      gcongr
    _ = V + 2 * |X| * Real.sqrt (M * V) := by
      rw [Real.sqrt_mul hM]
      ring

/-- One-sided Q4+ form of `q4_deviation_le`. -/
theorem q4Moment_le_main_add_error (I : Finset ℤ) (R singular : ℤ → ℝ) (X : ℝ) :
    q4Moment I R ≤
      X ^ 2 * modelSecondMoment I singular +
        variance I R (modelMain X singular) +
          2 * |X| * Real.sqrt
            (modelSecondMoment I singular * variance I R (modelMain X singular)) := by
  have h := q4_deviation_le I R singular X
  linarith [le_abs_self (q4Moment I R - X ^ 2 * modelSecondMoment I singular)]

/-- A directly pluggable implication lemma.  `modelBound` is an upper bound
for the singular-series second moment, and `varianceBound` is an upper bound
for the translated variance.  Both are ordinary hypotheses, not asserted
analytic facts. -/
theorem q4_from_variance_and_model_second_moment
    (I : Finset ℤ) (R singular : ℤ → ℝ) (X modelBound varianceBound : ℝ)
    (hmodelBound : 0 ≤ modelBound)
    (hmodel : modelSecondMoment I singular ≤ modelBound)
    (hvariance : variance I R (modelMain X singular) ≤ varianceBound) :
    q4Moment I R ≤
      X ^ 2 * modelSecondMoment I singular + varianceBound +
        2 * |X| * Real.sqrt (modelBound * varianceBound) := by
  have hproduct :
      modelSecondMoment I singular * variance I R (modelMain X singular) ≤
        modelBound * varianceBound := by
    exact mul_le_mul hmodel hvariance
      (variance_nonneg I R (modelMain X singular)) hmodelBound
  calc
    q4Moment I R ≤
        X ^ 2 * modelSecondMoment I singular +
          variance I R (modelMain X singular) +
            2 * |X| * Real.sqrt
              (modelSecondMoment I singular * variance I R (modelMain X singular)) :=
      q4Moment_le_main_add_error I R singular X
    _ ≤ X ^ 2 * modelSecondMoment I singular + varianceBound +
          2 * |X| * Real.sqrt (modelBound * varianceBound) := by
      gcongr

/-- Chebyshev/Markov in exact finite form.  Every exception contributes more
than `threshold²` to the variance. -/
theorem threshold_sq_mul_exceptionCount_le_variance
    (I : Finset ℤ) (R model : ℤ → ℝ) (threshold : ℝ)
    (hthreshold : 0 ≤ threshold) :
    threshold ^ 2 * exceptionCount I R model threshold ≤ variance I R model := by
  let B := exceptionSet I R model threshold
  calc
    threshold ^ 2 * exceptionCount I R model threshold =
        ∑ _h ∈ B, threshold ^ 2 := by
          simp [exceptionCount, B, mul_comm]
    _ ≤ ∑ h ∈ B, (R h - model h) ^ 2 := by
      apply Finset.sum_le_sum
      intro h hh
      have hbad : threshold < |R h - model h| := by
        exact (Finset.mem_filter.mp hh).2
      nlinarith [sq_nonneg (R h - model h), sq_abs (R h - model h)]
    _ ≤ ∑ h ∈ I, (R h - model h) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro h _ _
        positivity
    _ = variance I R model := rfl

/-- Density-one implication with explicit normalization.  The radius `H`, not
the cardinality of the translated integer window, occurs on the right. -/
theorem variance_implies_exception_bound
    (h₀ : ℤ) (H : ℕ) (R model : ℤ → ℝ) (threshold varianceRate : ℝ)
    (hthreshold : 0 < threshold)
    (hvariance : variance (translatedWindow h₀ H) R model ≤
      (H : ℝ) * varianceRate) :
    exceptionCount (translatedWindow h₀ H) R model threshold ≤
      (H : ℝ) * varianceRate / threshold ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hthreshold)).2
  simpa [mul_comm] using
    (threshold_sq_mul_exceptionCount_le_variance
      (translatedWindow h₀ H) R model threshold hthreshold.le).trans hvariance

/-- The exact exponent bookkeeping used in the density-one application.
Writing `δ = (log X)⁻ᴬ`, variance at rate `δ³` and pointwise threshold `X δ`
leave at most `H δ` exceptions.  Thus the paper's `3A` input exponent yields
its `A` exceptional-count exponent. -/
theorem cubic_variance_implies_linear_exception_bound
    (h₀ : ℤ) (H : ℕ) (R model : ℤ → ℝ) (X δ : ℝ)
    (hX : 0 < X) (hδ : 0 < δ)
    (hvariance : variance (translatedWindow h₀ H) R model ≤
      (H : ℝ) * X ^ 2 * δ ^ 3) :
    exceptionCount (translatedWindow h₀ H) R model (X * δ) ≤
      (H : ℝ) * δ := by
  have hraw := (threshold_sq_mul_exceptionCount_le_variance
    (translatedWindow h₀ H) R model (X * δ) (mul_pos hX hδ).le).trans hvariance
  have hfactor : 0 < (X * δ) ^ 2 := sq_pos_of_pos (mul_pos hX hδ)
  apply le_of_mul_le_mul_right (a := (X * δ) ^ 2) (a0 := hfactor)
  calc
    exceptionCount (translatedWindow h₀ H) R model (X * δ) * (X * δ) ^ 2 =
        (X * δ) ^ 2 * exceptionCount (translatedWindow h₀ H) R model (X * δ) :=
      mul_comm _ _
    _ ≤ (H : ℝ) * X ^ 2 * δ ^ 3 := hraw
    _ = ((H : ℝ) * δ) * (X * δ) ^ 2 := by ring

end

end MAPQ4Bridge
