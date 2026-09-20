import GuthMaynardFirstPoissonSourcePackage
import GuthMaynardSourceGGeneralPlancherel
import GuthMaynardLocalizedPairIntegrability

/-!
# Literal dyadic structural inputs for the whole-frequency theorem

The unit source bump is supported in `|x| < 2`, so its exact finite `m₃`
range at scale `M₃` is the integer window `|m₃| ≤ 2 M₃`.  Keeping this
factor of two visible avoids the false truncation to `|m₃| ≤ M₃`.
-/

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The literal unit bump vanishes outside the exact centered radius-`2M₃`
integer window. -/
theorem sourceBump_eq_zero_outside_centeredTwoScale
    {M3 : ℕ} (hM3 : 0 < M3) {m3 : ℤ}
    (hm3 : m3 ∉ sourceIntegerWindow 0 (2 * (M3 : ℝ))) :
    sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) = 0 := by
  have hM3R : 0 < (M3 : ℝ) := Nat.cast_pos.mpr hM3
  have habs : 2 * (M3 : ℝ) ≤ |(m3 : ℝ)| := by
    by_contra hnot
    have hlt : |(m3 : ℝ)| < 2 * (M3 : ℝ) := lt_of_not_ge hnot
    exact hm3 (mem_sourceIntegerWindow_zero_of_abs_le hlt.le)
  apply sourceBump_eq_zero_of_two_mul_le_abs 1 zero_lt_one
  rw [abs_div, abs_of_pos hM3R]
  exact (le_div_iff₀ hM3R).2 (by simpa [mul_comm] using habs)

/-- Exact cardinality envelope for the literal radius-`2M₃` source window. -/
theorem card_centeredTwoScale_cast_le (M3 : ℕ) :
    ((sourceIntegerWindow 0 (2 * (M3 : ℝ))).card : ℝ) ≤
      4 * (M3 : ℝ) + 3 := by
  have h := card_sourceIntegerWindow_cast_le 0
    (2 * (M3 : ℝ)) (by positivity)
  convert h using 1 <;> ring

/-- The unit source bump has norm at most one on the entire literal source
window. -/
theorem norm_sourceBump_unit_le_one (x : ℝ) :
    ‖(sourceBump 1 zero_lt_one x : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sourceBump_nonneg 1 zero_lt_one x)]
  exact sourceBump_le_one 1 zero_lt_one x

/-- The literal dyadic numerator and denominator ranges supply all nonzero,
size, and ratio facts needed by the corrected whole-frequency theorem. -/
theorem sourceDyadic_wholeFrequency_rangeFacts
    {M1 M2 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) :
    (∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0) ∧
    (∀ m1 ∈ sourceSignedDyadicRange M1,
      (M1 : ℝ) ≤ |(m1 : ℝ)|) ∧
    (∀ m1 ∈ sourceSignedDyadicRange M1,
      |(m1 : ℝ)| ≤ 2 * (M1 : ℝ)) ∧
    (∀ m2 ∈ sourcePositiveDyadicRange M2, 0 < m2) ∧
    (∀ m1 ∈ sourceSignedDyadicRange M1,
      ∀ m2 ∈ sourcePositiveDyadicRange M2,
        (M2 : ℝ) / (2 * (M1 : ℝ)) ≤
          |((m2 : ℝ) / (m1 : ℝ))|) ∧
    (∀ m1 ∈ sourceSignedDyadicRange M1,
      ∀ m2 ∈ sourcePositiveDyadicRange M2,
        |((m2 : ℝ) / (m1 : ℝ))| ≤
          (2 * (M2 : ℝ)) / (M1 : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm
  · exact fun _ hm => (sourceSignedDyadicRange_abs_bounds hM1 hm).1
  · exact fun _ hm => (sourceSignedDyadicRange_abs_bounds hM1 hm).2
  · exact fun _ hm => sourcePositiveDyadicRange_pos hM2 hm
  · exact fun _ hm1 _ hm2 => (sourceDyadic_ratio_bounds hM1 hM2 hm1 hm2).1
  · exact fun _ hm1 _ hm2 => (sourceDyadic_ratio_bounds hM1 hM2 hm1 hm2).2

#print axioms GuthMaynardJIteration.sourceBump_eq_zero_outside_centeredTwoScale
#print axioms GuthMaynardJIteration.card_centeredTwoScale_cast_le
#print axioms GuthMaynardJIteration.norm_sourceBump_unit_le_one
#print axioms GuthMaynardJIteration.sourceDyadic_wholeFrequency_rangeFacts

end GuthMaynardJIteration
