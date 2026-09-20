import GuthMaynardJIterationMediumRetained

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def poissonStrictLocalizationSet
    (M2 T B m2 m2' u : ℝ) (j : ℤ) : Set ℝ :=
  {u' | |(j : ℝ) - m2' * u' + m2 * u| < (M2 / T) * B}

theorem measurable_poissonRetainedIndicator_comp
    {alpha : Type*} [MeasurableSpace alpha]
    {A B : ℝ} (y : alpha → ℝ) (hy : Measurable y) (j : ℤ) :
    Measurable (fun x => poissonRetainedIndicator A B (y x) j) := by
  unfold poissonRetainedIndicator
  apply Measurable.ite
  · exact measurableSet_lt
      (((measurable_const.sub hy).div_const A).abs) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem integral_poissonRetainedIndicator_mul_eq_setIntegral
    {A B : ℝ} (y : ℝ → ℝ) (hy : Measurable y)
    (g : ℝ → ℝ) (j : ℤ) :
    (∫ x : ℝ, poissonRetainedIndicator A B (y x) j * g x) =
      ∫ x in {x | |((j : ℝ) - y x) / A| < B}, g x := by
  have hset : MeasurableSet {x : ℝ | |((j : ℝ) - y x) / A| < B} :=
    measurableSet_lt (((measurable_const.sub hy).div_const A).abs)
      measurable_const
  rw [← integral_indicator hset]
  apply integral_congr_ae
  filter_upwards with x
  unfold poissonRetainedIndicator
  by_cases hx : |((j : ℝ) - y x) / A| < B
  · rw [if_pos hx]
    rw [Set.indicator_of_mem (show x ∈
      {x : ℝ | |((j : ℝ) - y x) / A| < B} from hx)]
    simp
  · rw [if_neg hx]
    rw [Set.indicator_of_notMem (show x ∉
      {x : ℝ | |((j : ℝ) - y x) / A| < B} from hx)]
    simp

theorem retainedIndicatorSet_eq_strictLocalizationSet
    {M2 T : ℝ} (hM2 : 0 < M2) (hT : 0 < T)
    (B m2 m2' u : ℝ) (j : ℤ) :
    {u' : ℝ |
      |((j : ℝ) - (m2' * u' - m2 * u)) / (M2 / T)| < B} =
      poissonStrictLocalizationSet M2 T B m2 m2' u j := by
  ext u'
  unfold poissonStrictLocalizationSet
  have hA : 0 < M2 / T := div_pos hM2 hT
  change |((j : ℝ) - (m2' * u' - m2 * u)) / (M2 / T)| < B ↔
    |(j : ℝ) - m2' * u' + m2 * u| < (M2 / T) * B
  rw [abs_div, abs_of_pos hA, div_lt_iff₀ hA]
  have hnum : (j : ℝ) - (m2' * u' - m2 * u) =
      (j : ℝ) - m2' * u' + m2 * u := by ring
  rw [hnum]
  constructor <;> intro h <;> simpa only [mul_comm] using h

/-- The strict retained window is dominated by the closed affine ball used by
the source smoothing. -/
theorem tsum_poissonStrictLocalizedIntegral_le_sourceAffineSmoothing
    {m2 m2' M2 B T u : ℝ}
    (hm2' : 0 < m2') (hT : 0 < T)
    (psi f : ℝ → ℝ)
    (hf0 : ∀ u', 0 ≤ f u') (hpsi0 : ∀ z, 0 ≤ psi z)
    (hpsi_major : ∀ z, |z| ≤ (M2 / m2') * B → 1 ≤ psi z)
    (hlocal : ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B})
    (hsmooth : ∀ j : ℤ, Integrable
      (fun u' => T * psi (T * (sourceAffineCenter m2 m2' u j - u')) * f u'))
    (hsum : Summable
      (fun j : ℤ => affineSmoothing T psi f (sourceAffineCenter m2 m2' u j))) :
    (∑' j : ℤ, ∫ u' in
        poissonStrictLocalizationSet M2 T B m2 m2' u j, T * f u') ≤
      ∑' j : ℤ, affineSmoothing T psi f (sourceAffineCenter m2 m2' u j) := by
  let closed : ℤ → Set ℝ := fun j =>
    {u' | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B}
  let strict : ℤ → Set ℝ := fun j =>
    poissonStrictLocalizationSet M2 T B m2 m2' u j
  have hT0 : 0 ≤ T := hT.le
  have hclosed0 : ∀ j : ℤ, 0 ≤ ∫ u' in closed j, T * f u' := by
    intro j
    exact integral_nonneg fun u' => mul_nonneg hT0 (hf0 u')
  have hclosed_le : ∀ j : ℤ,
      (∫ u' in closed j, T * f u') ≤
        affineSmoothing T psi f (sourceAffineCenter m2 m2' u j) := by
    intro j
    have hset : closed j = Metric.closedBall
        (sourceAffineCenter m2 m2' u j) ((M2 / m2') * B / T) := by
      ext u'
      exact poissonLocalization_iff_mem_affineBall hm2' hT m2 (j : ℝ) u u' B
    have hl : IntegrableOn (fun u' => T * f u')
        (Metric.closedBall (sourceAffineCenter m2 m2' u j)
          ((M2 / m2') * B / T)) := by
      rw [← hset]
      exact hlocal j
    rw [hset]
    exact source_localized_integral_le_affineSmoothing hT psi f hf0 hpsi0
      hpsi_major hl (hsmooth j)
  have hclosedSum : Summable (fun j : ℤ => ∫ u' in closed j, T * f u') :=
    hsum.of_nonneg_of_le hclosed0 hclosed_le
  have hstrict0 : ∀ j : ℤ, 0 ≤ ∫ u' in strict j, T * f u' := by
    intro j
    exact integral_nonneg fun u' => mul_nonneg hT0 (hf0 u')
  have hstrict_le : ∀ j : ℤ,
      (∫ u' in strict j, T * f u') ≤ ∫ u' in closed j, T * f u' := by
    intro j
    apply setIntegral_mono_set (hlocal j)
    · exact Filter.Eventually.of_forall fun u' => mul_nonneg hT0 (hf0 u')
    · apply Filter.Eventually.of_forall
      intro u' hu'
      exact le_of_lt hu'
  have hstrictSum : Summable (fun j : ℤ => ∫ u' in strict j, T * f u') :=
    hclosedSum.of_nonneg_of_le hstrict0 hstrict_le
  calc
    (∑' j : ℤ, ∫ u' in strict j, T * f u') ≤
        ∑' j : ℤ, ∫ u' in closed j, T * f u' :=
      Summable.tsum_le_tsum hstrict_le hstrictSum hclosedSum
    _ ≤ ∑' j : ℤ,
        affineSmoothing T psi f (sourceAffineCenter m2 m2' u j) :=
      tsum_poissonLocalizedIntegral_le_sourceAffineSmoothing hm2' hT psi f
        hf0 hpsi0 hpsi_major hlocal hsmooth hsum

/-- Complete Tonelli-to-smoothing weld for the retained second-Poisson
window at the exact affine center `(m2*u+j)/m2'`. -/
theorem integral_tsum_retainedIndicator_affine_le_smoothing
    {m2 m2' M2 B T Y u : ℝ}
    (hm2' : 0 < m2') (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (psi f : ℝ → ℝ) (hf : Integrable f)
    (hf0 : ∀ u', 0 ≤ f u') (hpsi0 : ∀ z, 0 ≤ psi z)
    (hy : ∀ u', f u' ≠ 0 → |m2' * u' - m2 * u| ≤ Y)
    (hpsi_major : ∀ z, |z| ≤ (M2 / m2') * B → 1 ≤ psi z)
    (hlocal : ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - m2' * u' + m2 * u| ≤ (M2 / T) * B})
    (hsmooth : ∀ j : ℤ, Integrable
      (fun u' => T * psi (T * (sourceAffineCenter m2 m2' u j - u')) * f u'))
    (hsum : Summable
      (fun j : ℤ => affineSmoothing T psi f (sourceAffineCenter m2 m2' u j))) :
    (∫ u' : ℝ, ∑' j : ℤ,
        poissonRetainedIndicator (M2 / T) B (m2' * u' - m2 * u) j *
          (T * f u')) ≤
      ∑' j : ℤ, affineSmoothing T psi f (sourceAffineCenter m2 m2' u j) := by
  have hyMeas : Measurable (fun u' : ℝ => m2' * u' - m2 * u) := by fun_prop
  have hmeas : ∀ j : ℤ, AEStronglyMeasurable
      (fun u' => poissonRetainedIndicator (M2 / T) B
        (m2' * u' - m2 * u) j * (T * f u')) := by
    intro j
    exact (measurable_poissonRetainedIndicator_comp _ hyMeas j).aestronglyMeasurable.mul
      (hf.const_mul T).aestronglyMeasurable
  have hTonelli := (integral_tsum_poissonRetainedIndicator_mul volume
    (div_pos hM2 hT) hB hY (fun u' => m2' * u' - m2 * u)
    (fun u' => T * f u')
    (fun u' => mul_nonneg hT.le (hf0 u')) (hf.const_mul T)
    (fun u' hu' => hy u' (fun hfu => hu' (by simp [hfu]))) hmeas).1
  rw [hTonelli]
  have hterm (j : ℤ) :
      (∫ u' : ℝ, poissonRetainedIndicator (M2 / T) B
          (m2' * u' - m2 * u) j * (T * f u')) =
        ∫ u' in poissonStrictLocalizationSet M2 T B m2 m2' u j,
          T * f u' := by
    rw [integral_poissonRetainedIndicator_mul_eq_setIntegral
      (A := M2 / T) (B := B) (fun u' => m2' * u' - m2 * u) hyMeas
      (fun u' => T * f u') j]
    rw [retainedIndicatorSet_eq_strictLocalizationSet hM2 hT B m2 m2' u j]
  simp_rw [hterm]
  exact tsum_poissonStrictLocalizedIntegral_le_sourceAffineSmoothing
    hm2' hT psi f hf0 hpsi0 hpsi_major hlocal hsmooth hsum

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.measurable_poissonRetainedIndicator_comp
#print axioms GuthMaynardJIteration.integral_poissonRetainedIndicator_mul_eq_setIntegral
#print axioms GuthMaynardJIteration.retainedIndicatorSet_eq_strictLocalizationSet
#print axioms GuthMaynardJIteration.tsum_poissonStrictLocalizedIntegral_le_sourceAffineSmoothing
#print axioms GuthMaynardJIteration.integral_tsum_retainedIndicator_affine_le_smoothing
