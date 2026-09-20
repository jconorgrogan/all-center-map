import GuthMaynardJIterationFrequencyBounds

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def poissonRetainedIndicator (A B y : ℝ) (j : ℤ) : ℝ :=
  if |((j : ℝ) - y) / A| < B then 1 else 0

theorem poissonRetainedIndicator_le_quadratic
    {A B : ℝ} (hB : 0 ≤ B) (y : ℝ) (j : ℤ) :
    poissonRetainedIndicator A B y j ≤
      (1 + B) ^ 2 * scaledShiftedQuadraticWeight A y j := by
  unfold poissonRetainedIndicator scaledShiftedQuadraticWeight
  split_ifs with hj
  · have hd : 0 ≤ |((j : ℝ) - y) / A| := abs_nonneg _
    have hle : 1 + |((j : ℝ) - y) / A| ≤ 1 + B := by linarith
    let d : ℝ := |((j : ℝ) - y) / A|
    have hratio : 1 ≤ (1 + B) / (1 + d) :=
      (le_div_iff₀ (by dsimp only [d]; positivity)).2 (by simpa [d] using hle)
    calc
      1 ≤ ((1 + B) / (1 + d)) ^ 2 := by nlinarith [sq_nonneg ((1 + B) / (1 + d) - 1)]
      _ = (1 + B) ^ 2 * (1 / (1 + d) ^ 2) := by
        rw [div_pow]
        ring
  · positivity

theorem poissonRetainedIndicator_le_uniformEnvelope
    {A B Y : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    {y : ℝ} (hy : |y| ≤ Y) (j : ℤ) :
    poissonRetainedIndicator A B y j ≤
      ((1 + B) ^ 2 * (1 + Y / A) ^ 2 * max 1 (A ^ 2)) *
        integerQuadraticEnvelope j := by
  have hquad := poissonRetainedIndicator_le_quadratic (A := A) hB y j
  have hweight := scaledShiftedQuadraticWeight_le_envelope hA y j
  have hydiv : |y| / A ≤ Y / A := div_le_div_of_nonneg_right hy hA.le
  have hone : 0 ≤ 1 + |y| / A := by positivity
  have hYone : 0 ≤ 1 + Y / A := by positivity
  have hsquares : (1 + |y| / A) ^ 2 ≤ (1 + Y / A) ^ 2 := by
    nlinarith
  calc
    poissonRetainedIndicator A B y j ≤
        (1 + B) ^ 2 * scaledShiftedQuadraticWeight A y j := hquad
    _ ≤ (1 + B) ^ 2 *
        ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) *
          integerQuadraticEnvelope j) := by gcongr
    _ ≤ ((1 + B) ^ 2 * (1 + Y / A) ^ 2 * max 1 (A ^ 2)) *
        integerQuadraticEnvelope j := by
      have hBsq : 0 ≤ (1 + B) ^ 2 := sq_nonneg _
      have hmax : 0 ≤ max 1 (A ^ 2) := le_trans (by norm_num) (le_max_left _ _)
      have henv : 0 ≤ integerQuadraticEnvelope j := by
        unfold integerQuadraticEnvelope
        split_ifs <;> positivity
      calc
        (1 + B) ^ 2 *
            ((1 + |y| / A) ^ 2 * max 1 (A ^ 2) *
              integerQuadraticEnvelope j) =
          (1 + B) ^ 2 * (1 + |y| / A) ^ 2 *
            max 1 (A ^ 2) * integerQuadraticEnvelope j := by ring
        _ ≤ (1 + B) ^ 2 * (1 + Y / A) ^ 2 *
            max 1 (A ^ 2) * integerQuadraticEnvelope j := by gcongr
        _ = _ := by ring

theorem summable_poissonRetainedIndicator
    {A B : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (y : ℝ) :
    Summable (poissonRetainedIndicator A B y) := by
  apply (summable_scaledShiftedQuadraticWeight hA y).mul_left ((1 + B) ^ 2)
    |>.of_nonneg_of_le
  · intro j
    unfold poissonRetainedIndicator
    split_ifs <;> positivity
  · intro j
    exact poissonRetainedIndicator_le_quadratic hB y j

theorem norm_sourceSecondPoissonRetained_le_indicator
    (F : ℝ → ℂ) {K M2 T B : ℝ}
    (hM2 : 0 < M2) (hT : 0 < T) (hB : 0 ≤ B)
    (hF : ∀ xi, ‖F xi‖ ≤ K) (y : ℝ) :
    ‖sourceSecondPoissonRetained F M2 T B y‖ ≤
      (T / M2) * K *
        ∑' j : ℤ, poissonRetainedIndicator (M2 / T) B y j := by
  have hA : 0 < M2 / T := div_pos hM2 hT
  have hind := summable_poissonRetainedIndicator hA hB y
  have hpoint : ∀ j : ℤ,
      ‖schwartzIntegerRetained F (M2 / T) B y j‖ ≤
        K * poissonRetainedIndicator (M2 / T) B y j := by
    intro j
    unfold schwartzIntegerRetained poissonRetainedIndicator
    split_ifs
    · simpa using hF (((j : ℝ) - y) / (M2 / T))
    · simp
  have hnorms : Summable (fun j : ℤ =>
      ‖schwartzIntegerRetained F (M2 / T) B y j‖) :=
    (hind.mul_left K).of_nonneg_of_le (fun j => norm_nonneg _) hpoint
  unfold sourceSecondPoissonRetained
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hT hM2)]
  calc
    (T / M2) * ‖∑' j : ℤ,
        schwartzIntegerRetained F (M2 / T) B y j‖ ≤
      (T / M2) * ∑' j : ℤ,
        ‖schwartzIntegerRetained F (M2 / T) B y j‖ := by
        exact mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorms)
          (div_nonneg hT.le hM2.le)
    _ ≤ (T / M2) * ∑' j : ℤ,
        K * poissonRetainedIndicator (M2 / T) B y j := by
      exact mul_le_mul_of_nonneg_left
        (Summable.tsum_le_tsum hpoint hnorms (hind.mul_left K))
        (div_nonneg hT.le hM2.le)
    _ = (T / M2) * K * ∑' j : ℤ,
        poissonRetainedIndicator (M2 / T) B y j := by
      rw [hind.tsum_mul_left]
      ring

/-- Tonelli majorant for the retained Poisson window with an affine shift.
The bound is uniform on the actual support of `g`; outside that support the
integrand vanishes. -/
theorem integral_tsum_poissonRetainedIndicator_mul
    {alpha : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) {A B Y : ℝ}
    (hA : 0 < A) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (y : alpha → ℝ) (g : alpha → ℝ)
    (hg0 : ∀ x, 0 ≤ g x) (hg : Integrable g mu)
    (hy : ∀ x, g x ≠ 0 → |y x| ≤ Y)
    (hmeas : ∀ j : ℤ, AEStronglyMeasurable
      (fun x => poissonRetainedIndicator A B (y x) j * g x) mu) :
    (∫ x, ∑' j : ℤ,
        poissonRetainedIndicator A B (y x) j * g x ∂mu) =
      ∑' j : ℤ, ∫ x,
        poissonRetainedIndicator A B (y x) j * g x ∂mu ∧
    (∑' j : ℤ, ∫ x,
        poissonRetainedIndicator A B (y x) j * g x ∂mu) ≤
      (((1 + B) ^ 2 * (1 + Y / A) ^ 2 * max 1 (A ^ 2)) *
        integerQuadraticMass) * ∫ x, g x ∂mu := by
  let W : ℝ := (1 + B) ^ 2 * (1 + Y / A) ^ 2 * max 1 (A ^ 2)
  have hW : 0 ≤ W := by
    dsimp only [W]
    positivity
  have hweights : Summable (fun j : ℤ => W * integerQuadraticEnvelope j) :=
    summable_integerQuadraticEnvelope.mul_left W
  have hphi0 : ∀ j : ℤ, ∀ x,
      0 ≤ poissonRetainedIndicator A B (y x) j * g x := by
    intro j x
    exact mul_nonneg (by unfold poissonRetainedIndicator; split_ifs <;> positivity)
      (hg0 x)
  have hmajor : ∀ j : ℤ, ∀ x,
      poissonRetainedIndicator A B (y x) j * g x ≤
        (W * integerQuadraticEnvelope j) * g x := by
    intro j x
    by_cases hx : g x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right
        (poissonRetainedIndicator_le_uniformEnvelope hA hB hY (hy x hx) j)
        (hg0 x)
  have h := integral_tsum_of_summable_majorant mu
    (fun j x => poissonRetainedIndicator A B (y x) j * g x)
    (fun j => W * integerQuadraticEnvelope j) g hweights hg0 hg
    hphi0 hmeas hmajor
  refine ⟨h.1, h.2.trans_eq ?_⟩
  unfold W integerQuadraticMass
  rw [summable_integerQuadraticEnvelope.tsum_mul_left]

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.poissonRetainedIndicator_le_quadratic
#print axioms GuthMaynardJIteration.poissonRetainedIndicator_le_uniformEnvelope
#print axioms GuthMaynardJIteration.summable_poissonRetainedIndicator
#print axioms GuthMaynardJIteration.norm_sourceSecondPoissonRetained_le_indicator
#print axioms GuthMaynardJIteration.integral_tsum_poissonRetainedIndicator_mul
