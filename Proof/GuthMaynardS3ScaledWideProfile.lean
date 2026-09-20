import GuthMaynardS3WideProfile
import GuthMaynardS3WideFourierTail

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3ScaledWideProfile

open GuthMaynardJIteration
open GuthMaynardS3WideProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardS3WideTail

/-- Dilation by four shrinks the wide profile's support radius from `7` to
`7/4`, leaving the height and profile mass parameters unchanged. -/
def scaledWideProfile (B : ℝ) (W : Finset ℝ) : ℝ → ℝ :=
  fun u => wideProfile B W (4 * u)

theorem scaledWideProfile_eq (B : ℝ) (W : Finset ℝ) (u : ℝ) :
    scaledWideProfile B W u = wideProfile B W (4 * u) := rfl

theorem scaledWideProfile_nonneg
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    0 ≤ scaledWideProfile B W u := by
  exact wideProfile_nonneg hB W _

theorem scaledWideProfile_bounded
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    scaledWideProfile B W u ≤ 4 * (W.card : ℝ) ^ 2 := by
  exact wideProfile_bounded hB W _

theorem scaledWideProfile_supported
    {B : ℝ} (hB4 : (4 : ℝ) ≤ B) (W : Finset ℝ)
    {u : ℝ} (hu : scaledWideProfile B W u ≠ 0) :
    |u| ≤ (7 : ℝ) / 4 := by
  have hu4 : |4 * u| ≤ (7 : ℝ) :=
    wideProfile_supported hB4 W (by simpa [scaledWideProfile] using hu)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)] at hu4
  nlinarith

theorem scaledWideProfile_continuous
    {B T : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) :
    Continuous (scaledWideProfile B W) := by
  exact (wideProfile_sourceAdmissibleProfile
    (T := T) hT hB4 hBT W).continuous.comp
      (continuous_const.mul continuous_id)

/-- Fourier dilation for the real source profile. -/
theorem fourier_comp_mul_real
    (f : ℝ → ℝ) (a xi : ℝ) (ha : a ≠ 0) :
    FourierTransform.fourier (fun u : ℝ => (f (a * u) : ℂ)) xi =
      (|a⁻¹| : ℝ) • FourierTransform.fourier
        (fun u : ℝ => (f u : ℂ)) (xi / a) := by
  simp_rw [Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun t =>
    Complex.exp ((-2 * Real.pi * (t / a) * xi : ℝ) * Complex.I) *
      (f t : ℂ)
  have hpoint : ∀ u : ℝ,
      Complex.exp ((-2 * Real.pi * u * xi : ℝ) * Complex.I) *
          (f (a * u) : ℂ) = g (a * u) := by
    intro u
    dsimp [g]
    congr 2
    push_cast
    field_simp [ha]
  calc
    _ = ∫ u : ℝ, g (a * u) := integral_congr_ae
      (Filter.Eventually.of_forall hpoint)
    _ = |a⁻¹| • ∫ t : ℝ, g t := Measure.integral_comp_mul_left g a
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [g]
      congr 2
      push_cast
      field_simp [ha]

theorem scaledWideProfile_fourier_bound
    {B T : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) (q : ℕ) {eta : ℝ} (heta : 0 < eta)
    {z : ℝ} (hz : z ≠ 0) :
    ‖FourierTransform.fourier
      (fun u : ℝ => (scaledWideProfile B W u : ℂ)) z‖ ≤
      (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q * T ^ eta *
        (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hzdiv : z / 4 ≠ 0 := div_ne_zero hz (by norm_num)
  have hwide := (wideProfile_fourier_decay_explicit hB hT hBT W q heta)
    (z / 4) hzdiv
  have hzabs : 0 < |z| := abs_pos.mpr hz
  have hscale : T / |z / 4| = 4 * (T / |z|) := by
    rw [abs_div]
    norm_num
    field_simp [hzabs.ne']
  have hfourier : FourierTransform.fourier
      (fun u : ℝ => (scaledWideProfile B W u : ℂ)) z =
      (|(4 : ℝ)⁻¹| : ℝ) • FourierTransform.fourier
        (fun u : ℝ => (wideProfile B W u : ℂ)) (z / 4) := by
    simpa [scaledWideProfile] using
      (fourier_comp_mul_real (fun u : ℝ => wideProfile B W u)
        4 z (by norm_num))
  rw [hfourier, norm_smul]
  norm_num [Real.norm_eq_abs, abs_of_nonneg]
  calc
    (1 / 4 : ℝ) *
        ‖FourierTransform.fourier
          (fun u : ℝ => (wideProfile B W u : ℂ)) (z / 4)‖ ≤
      (1 / 4 : ℝ) *
        (lemma84SmoothingFourierConstant q * T ^ eta *
          (T / |z / 4|) ^ q * (4 * (W.card : ℝ) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hwide (by positivity)
    _ = (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q * T ^ eta *
          (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) / 4 := by
      rw [hscale, mul_pow]
      ring
    _ ≤ (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q * T ^ eta *
          (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
      have hC : 0 ≤ lemma84SmoothingFourierConstant q :=
        lemma84SmoothingFourierConstant_nonneg q
      have hnonneg : 0 ≤ (4 : ℝ) ^ q * lemma84SmoothingFourierConstant q *
          T ^ eta * (T / |z|) ^ q * (4 * (W.card : ℝ) ^ 2) := by
        positivity
      nlinarith

theorem scaledWideProfile_sourceAdmissibleProfile
    {B T : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) :
    SourceAdmissibleProfile T (4 * (W.card : ℝ) ^ 2) ((7 : ℝ) / 4)
      (scaledWideProfile B W) := by
  have hB : 0 < B := lt_of_lt_of_le (by norm_num) hB4
  have hwide := wideProfile_sourceAdmissibleProfile hT hB4 hBT W
  have hcont : Continuous (scaledWideProfile B W) := by
    exact hwide.continuous.comp (continuous_const.mul continuous_id)
  have hInt : Integrable (scaledWideProfile B W) := by
    convert hwide.integrable.comp_mul_left' (by norm_num : (4 : ℝ) ≠ 0) using 1
  have hsq : Integrable (fun u : ℝ => scaledWideProfile B W u ^ 2) := by
    convert hwide.squareIntegrable.comp_mul_left' (by norm_num : (4 : ℝ) ≠ 0) using 1
  have hdec : SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun u : ℝ => (scaledWideProfile B W u : ℂ))) T
      (4 * (W.card : ℝ) ^ 2) := by
    intro eta heta q
    refine ⟨(4 : ℝ) ^ q * lemma84SmoothingFourierConstant q, ?_, ?_⟩
    · exact mul_nonneg (pow_nonneg (by norm_num) _) 
        (lemma84SmoothingFourierConstant_nonneg q)
    · intro z hz
      exact scaledWideProfile_fourier_bound hT hB4 hBT W q heta hz
  exact
    { nonneg := scaledWideProfile_nonneg hB W
      bounded := scaledWideProfile_bounded hB W
      supported := fun u hu => scaledWideProfile_supported hB4 W hu
      integrable := hInt
      squareIntegrable := hsq
      continuous := hcont
      rapidDecay := hdec }

theorem scaledWideProfile_L1_eq_quarter
    {B T : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) :
    (∫ u : ℝ, |scaledWideProfile B W u|) =
      (1 / 4 : ℝ) * ∫ u : ℝ, |wideProfile B W u| := by
  have hchange := Measure.integral_comp_mul_left
    (fun u : ℝ => |wideProfile B W u|) (4 : ℝ)
  have hnonneg : ∀ u, 0 ≤ wideProfile B W u :=
    wideProfile_nonneg (lt_of_lt_of_le (by norm_num) hB4) W
  calc
    (∫ u : ℝ, |scaledWideProfile B W u|) =
        ∫ u : ℝ, wideProfile B W (4 * u) := by
      apply integral_congr_ae
      filter_upwards [] with u
      rw [scaledWideProfile, abs_of_nonneg]
      exact hnonneg _
    _ = (1 / 4 : ℝ) * ∫ u : ℝ, |wideProfile B W u| := by
      simpa [abs_of_nonneg (hnonneg _)] using hchange

theorem scaledWideProfile_L2_sq_eq_quarter
    {B T : ℝ} (hT : 1 ≤ T) (hB4 : (4 : ℝ) ≤ B) (hBT : B ≤ T)
    (W : Finset ℝ) :
    (∫ u : ℝ, scaledWideProfile B W u ^ 2) =
      (1 / 4 : ℝ) * ∫ u : ℝ, wideProfile B W u ^ 2 := by
  have hchange := Measure.integral_comp_mul_left
    (fun u : ℝ => wideProfile B W u ^ 2) (4 : ℝ)
  simpa [scaledWideProfile] using hchange

end GuthMaynardS3ScaledWideProfile

#print axioms GuthMaynardS3ScaledWideProfile.scaledWideProfile_sourceAdmissibleProfile
#print axioms GuthMaynardS3ScaledWideProfile.scaledWideProfile_fourier_bound
#print axioms GuthMaynardS3ScaledWideProfile.scaledWideProfile_L1_eq_quarter
#print axioms GuthMaynardS3ScaledWideProfile.scaledWideProfile_L2_sq_eq_quarter
