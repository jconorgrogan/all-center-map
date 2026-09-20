import GuthMaynardWholeFrequencyThreeScaleSource
import GuthMaynardJIterationPlancherelWeld

/-!
# Whole-support bump domination before Plancherel

The source bump is one on `|m₃| ≤ M₃` but supported through `2M₃`.
Consequently the unweighted affine energy on the plateau is not equal to the
full-support source function.  For nonnegative profiles it is, however,
pointwise dominated by that function.  This is the correct weld to the literal
first-Poisson truncation used by the whole-frequency theorem.
-/

open scoped BigOperators Real FourierTransform SchwartzMap
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The source plateau range is contained in the literal support window. -/
theorem sourceCenteredRange_subset_centeredTwoScale (M3 : ℕ) :
    sourceCenteredRange M3 ⊆ sourceIntegerWindow 0 (2 * (M3 : ℝ)) := by
  intro m3 hm3
  apply mem_sourceIntegerWindow_zero_of_abs_le
  have h := sourceCenteredRange_abs_le hm3
  have hM3zero : 0 ≤ (M3 : ℝ) := Nat.cast_nonneg M3
  linarith

/-- Physical-space squared norm of a finite source function with a Schwartz
profile is integrable. -/
theorem integrable_norm_sq_sourceGFinite_of_schwartz
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : 𝓢(ℝ, ℂ)) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    Integrable (fun u : ℝ =>
      ‖sourceGFinite m1Range m2Range m3Range psi1
        (fun x => f x) M3 u‖ ^ 2) := by
  let G : 𝓢(ℝ, ℂ) :=
    sourceGSchwartzFinite m1Range m2Range m3Range psi1 f M3 hm1 hm2
  have hG : (fun u : ℝ => G u) =
      sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3 := by
    funext u
    exact sourceGSchwartzFinite_apply
      m1Range m2Range m3Range psi1 f M3 hm1 hm2 u
  rw [← hG]
  exact integrable_norm_sq_schwartzMap G

/-- Pointwise source fact: for a nonnegative real profile, the affine sum on
the unit plateau is dominated after squaring by the source function retaining
the complete radius-two bump support. -/
theorem sourceFiniteAffineSum_sq_le_norm_sq_wholeSupport
    (f : ℝ → ℝ) (hf0 : ∀ u, 0 ≤ f u)
    {M1 M2 M3 : ℕ} (hM3 : 0 < M3) (u : ℝ) :
    (sourceFiniteAffineSum (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f u) ^ 2 ≤
      ‖sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 := by
  let B : ℝ :=
    ∑ m1 ∈ sourceSignedDyadicRange M1,
      ∑ m2 ∈ sourcePositiveDyadicRange M2,
        ∑ m3 ∈ sourceIntegerWindow 0 (2 * (M3 : ℝ)),
          sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) *
            f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro m3 hm3
    exact mul_nonneg (sourceBump_nonneg 1 zero_lt_one _)
      (hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
  have hA0 : 0 ≤ sourceFiniteAffineSum (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f u := by
    unfold sourceFiniteAffineSum
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro m3 hm3
    exact hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))
  have hAB : sourceFiniteAffineSum (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f u ≤ B := by
    dsimp only [B]
    unfold sourceFiniteAffineSum
    apply Finset.sum_le_sum
    intro m1 hm1
    apply Finset.sum_le_sum
    intro m2 hm2
    calc
      (∑ m3 ∈ sourceCenteredRange M3,
          f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))) =
        ∑ m3 ∈ sourceCenteredRange M3,
          sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) *
            f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m3 hm3
          have hratio := sourceCenteredRange_ratio_abs_le_one hM3 hm3
          rw [sourceBump_eq_one_of_abs_le 1 zero_lt_one hratio]
          ring
      _ ≤ ∑ m3 ∈ sourceIntegerWindow 0 (2 * (M3 : ℝ)),
          sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) *
            f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (sourceCenteredRange_subset_centeredTwoScale M3)
          intro m3 hm3 hnot
          exact mul_nonneg (sourceBump_nonneg 1 zero_lt_one _)
            (hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
  have hG : sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u = (B : ℂ) := by
    dsimp only [B]
    unfold sourceGFinite sourceGSummand
    push_cast
    rfl
  rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
  exact pow_le_pow_left₀ hA0 hAB 2

/-- The full-support weighted source field is in turn bounded by the
unweighted affine sum over that same finite support window. -/
theorem norm_sq_wholeSupport_le_sourceFiniteAffineSum_sq
    (f : ℝ → ℝ) (hf0 : ∀ u, 0 ≤ f u)
    {M1 M2 M3 : ℕ} (u : ℝ) :
    ‖sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 ≤
      (sourceFiniteAffineSum (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ))) f u) ^ 2 := by
  let B : ℝ :=
    ∑ m1 ∈ sourceSignedDyadicRange M1,
      ∑ m2 ∈ sourcePositiveDyadicRange M2,
        ∑ m3 ∈ sourceIntegerWindow 0 (2 * (M3 : ℝ)),
          sourceBump 1 zero_lt_one ((m3 : ℝ) / (M3 : ℝ)) *
            f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro m3 hm3
    exact mul_nonneg (sourceBump_nonneg 1 zero_lt_one _)
      (hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
  have hC0 : 0 ≤ sourceFiniteAffineSum (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2)
      (sourceIntegerWindow 0 (2 * (M3 : ℝ))) f u := by
    unfold sourceFiniteAffineSum
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro m3 hm3
    exact hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))
  have hBC : B ≤ sourceFiniteAffineSum (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M2)
      (sourceIntegerWindow 0 (2 * (M3 : ℝ))) f u := by
    dsimp only [B]
    unfold sourceFiniteAffineSum
    apply Finset.sum_le_sum
    intro m1 hm1
    apply Finset.sum_le_sum
    intro m2 hm2
    apply Finset.sum_le_sum
    intro m3 hm3
    exact mul_le_of_le_one_left
      (hf0 (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
      (sourceBump_le_one 1 zero_lt_one _)
  have hG : sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u = (B : ℂ) := by
    dsimp only [B]
    unfold sourceGFinite sourceGSummand
    push_cast
    rfl
  rw [hG, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
  exact pow_le_pow_left₀ hB0 hBC 2

/-- The physical squared norm of the literal whole-support field is
integrable for every admissible source profile. -/
theorem integrable_norm_sq_wholeSupport_of_sourceProfile
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) :
    Integrable (fun u : ℝ =>
      ‖sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2) := by
  have hm1 : ∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0 :=
    fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm
  have hm2 : ∀ m2 ∈ sourcePositiveDyadicRange M2, m2 ≠ 0 :=
    fun _ hm => sourcePositiveDyadicRange_ne_zero hM2 hm
  have hmajor := integrable_sq_sourceFiniteAffineSum
    (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
    (sourceIntegerWindow 0 (2 * (M3 : ℝ))) f hf.continuous
    hf.squareIntegrable hm1 hm2
  apply hmajor.mono'
  · exact (continuous_sourceGFinite
      (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
      (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
      (fun x : ℝ => (f x : ℂ))
      (Complex.continuous_ofReal.comp hf.continuous) (M3 : ℝ)).norm.pow 2
        |>.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact norm_sq_wholeSupport_le_sourceFiniteAffineSum_sq f hf.nonneg u

/-- Source-profile version of the corrected Plancherel weld.  This is the
form needed by the Proposition 9.1 smoothing orbit; it introduces no
Schwartz strengthening. -/
theorem sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
    {T S F eta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f) (heta : 0 < eta) (hT : 0 ≤ T)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3) :
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤
      ∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2 := by
  have hm1 : ∀ m1 ∈ sourceSignedDyadicRange M1, m1 ≠ 0 :=
    fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm
  have hm2 : ∀ m2 ∈ sourcePositiveDyadicRange M2, m2 ≠ 0 :=
    fun _ hm => sourcePositiveDyadicRange_ne_zero hM2 hm
  have hm3 : ∀ m3 ∈ sourceCenteredRange M3,
      |(m3 : ℝ) / (M3 : ℝ)| ≤ (1 : ℝ) :=
    fun _ hm => sourceCenteredRange_ratio_abs_le_one hM3 hm
  have hcard1 := card_sourceSignedDyadicRange_cast_le M1
  have hcard2 := card_sourcePositiveDyadicRange_cast_le M2
  have hcard3 := card_centeredTwoScale_cast_le M3
  have hratio := sourceDyadic_wholeFrequency_rangeFacts hM1 hM2
  rcases hratio with ⟨_, _, _, _, hratioLo, hratioHi⟩
  have hplanch := integral_norm_sq_fourier_sourceGFinite_of_sourceProfile
    (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
    (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
    (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (M3 := (M3 : ℝ)) hf heta hT
    (show 0 < sourceDyadicRlo M1 M2 by unfold sourceDyadicRlo; positivity)
    (show 0 ≤ sourceDyadicN1 M1 by unfold sourceDyadicN1; positivity)
    (show 0 ≤ sourceDyadicN2 M2 by unfold sourceDyadicN2; positivity)
    (show 0 ≤ sourceDyadicN3 M3 by unfold sourceDyadicN3; positivity)
    (show 0 ≤ (1 : ℝ) by norm_num)
    (show 0 ≤ sourceDyadicRhi M1 M2 by unfold sourceDyadicRhi; positivity)
    (by simpa [sourceDyadicN1] using hcard1)
    (by simpa [sourceDyadicN2] using hcard2)
    (by simpa [sourceDyadicN3] using hcard3)
    hm1 hm2 (by
      intro m3 hm3
      exact norm_sourceBump_unit_le_one ((m3 : ℝ) / (M3 : ℝ)))
    hratioLo hratioHi
  have hfullInt := integrable_norm_sq_wholeSupport_of_sourceProfile
    hf hM1 hM2 (M3 := M3)
  calc
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f =
      ∫ u : ℝ, ‖sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3)
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 :=
      sourceFiniteAffineEnergy_eq_integral_norm_sourceGFinite_sourceBump
        _ _ _ f zero_lt_one hm3
    _ ≤ ∫ u : ℝ, ‖sourceGFinite (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2)
        (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => sq_nonneg _) hfullInt
      exact Filter.Eventually.of_forall fun u => by
        change ‖sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) (sourceCenteredRange M3)
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2 ≤
          ‖sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2
        rw [sourceGFinite_sourceBump_eq_ofReal_sourceFiniteAffineSum
          (sourceSignedDyadicRange M1) (sourcePositiveDyadicRange M2)
          (sourceCenteredRange M3) f zero_lt_one hm3 u]
        rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        exact sourceFiniteAffineSum_sq_le_norm_sq_wholeSupport
          f hf.nonneg (M1 := M1) (M2 := M2) hM3 u
    _ = ∫ xi : ℝ, ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2)
          (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2 := hplanch.symm

/-- Generic consumer seam: once any source theorem bounds the literal
radius-two whole-support Fourier energy by `B`, the unit-plateau affine energy
is bounded by the same `B`. -/
theorem sourceCenteredAffineEnergy_le_of_wholeSupport_fourier_le_of_sourceProfile
    {T S F eta B : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f) (heta : 0 < eta) (hT : 0 ≤ T)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3)
    (hFourier :
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2) ≤ B) :
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤ B := by
  exact le_trans
    (sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
      hf heta hT hM1 hM2 hM3)
    hFourier

/-- Correct Plancherel weld for the literal radius-two source support.  It
bounds the unit-plateau affine energy by the Fourier energy controlled by the
whole-frequency theorem. -/
theorem sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral
    (f : ℝ → ℝ) (fSchwartz : 𝓢(ℝ, ℂ))
    (hfcoe : ∀ u : ℝ, fSchwartz u = (f u : ℂ))
    (hf0 : ∀ u, 0 ≤ f u)
    {M1 M2 M3 : ℕ} (hM1 : 0 < M1) (hM2 : 0 < M2) (hM3 : 0 < M3) :
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M2) (sourceCenteredRange M3) f ≤
      ∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite (sourceSignedDyadicRange M1)
            (sourcePositiveDyadicRange M2)
            (sourceIntegerWindow 0 (2 * (M3 : ℝ)))
            (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
            (fun u : ℝ => (f u : ℂ)) (M3 : ℝ)) xi‖ ^ 2 := by
  let R1 := sourceSignedDyadicRange M1
  let R2 := sourcePositiveDyadicRange M2
  let R3 := sourceCenteredRange M3
  let R3full := sourceIntegerWindow 0 (2 * (M3 : ℝ))
  let psi1 : ℝ → ℂ := fun x => (sourceBump 1 zero_lt_one x : ℂ)
  have hm1 : ∀ m1 ∈ R1, m1 ≠ 0 :=
    fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm
  have hm2 : ∀ m2 ∈ R2, m2 ≠ 0 :=
    fun _ hm => sourcePositiveDyadicRange_ne_zero hM2 hm
  have hm3 : ∀ m3 ∈ R3, |(m3 : ℝ) / (M3 : ℝ)| ≤ (1 : ℝ) :=
    fun _ hm => sourceCenteredRange_ratio_abs_le_one hM3 hm
  have hcenterInt := integrable_norm_sq_sourceGFinite_of_schwartz
    R1 R2 R3 psi1 fSchwartz (M3 : ℝ) hm1 hm2
  have hfullInt := integrable_norm_sq_sourceGFinite_of_schwartz
    R1 R2 R3full psi1 fSchwartz (M3 : ℝ) hm1 hm2
  have hcoe : (fun u : ℝ => fSchwartz u) = (fun u : ℝ => (f u : ℂ)) :=
    funext hfcoe
  rw [sourceFiniteAffineEnergy_eq_integral_norm_sourceGFinite_sourceBump
    R1 R2 R3 f zero_lt_one hm3]
  change (∫ u : ℝ, ‖sourceGFinite R1 R2 R3 psi1
      (fun x : ℝ => (f x : ℂ)) (M3 : ℝ) u‖ ^ 2) ≤
    ∫ xi : ℝ, ‖FourierTransform.fourier
      (sourceGFinite R1 R2 R3full psi1
        (fun x : ℝ => (f x : ℂ)) (M3 : ℝ)) xi‖ ^ 2
  rw [← hcoe]
  rw [integral_norm_sq_fourier_sourceGFinite
    R1 R2 R3full psi1 fSchwartz (M3 : ℝ) hm1 hm2]
  apply integral_mono hcenterInt hfullInt
  intro u
  simp_rw [hfcoe]
  rw [sourceGFinite_sourceBump_eq_ofReal_sourceFiniteAffineSum
    R1 R2 R3 f zero_lt_one hm3 u]
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  exact sourceFiniteAffineSum_sq_le_norm_sq_wholeSupport f hf0 hM3 u

#print axioms GuthMaynardJIteration.sourceCenteredRange_subset_centeredTwoScale
#print axioms GuthMaynardJIteration.integrable_norm_sq_sourceGFinite_of_schwartz
#print axioms GuthMaynardJIteration.sourceFiniteAffineSum_sq_le_norm_sq_wholeSupport
#print axioms GuthMaynardJIteration.norm_sq_wholeSupport_le_sourceFiniteAffineSum_sq
#print axioms GuthMaynardJIteration.integrable_norm_sq_wholeSupport_of_sourceProfile
#print axioms GuthMaynardJIteration.sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral_of_sourceProfile
#print axioms GuthMaynardJIteration.sourceCenteredAffineEnergy_le_of_wholeSupport_fourier_le_of_sourceProfile
#print axioms GuthMaynardJIteration.sourceCenteredAffineEnergy_le_wholeSupport_fourierIntegral

end GuthMaynardJIteration
