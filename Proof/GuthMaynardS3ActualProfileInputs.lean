import GuthMaynardS3MediumConcreteWeld
import GuthMaynardS3ZeroEllProfile
import GuthMaynardSourceGGeneralPlancherel

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Metric

noncomputable section
namespace GuthMaynardS3ActualProfileInputs

open GuthMaynardJIteration
open GuthMaynardS3MediumConcreteWeld
open GuthMaynardS3LiteralLemma84Outer
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface
open GuthMaynardS3ZeroEllProfile

/-! The literal corrected Fourier inner is controlled directly by the profile
L¹ mass.  The constant `6` is the exact product of the positive-dyadic count
`3 M₂` and the coefficient cap `2 M₂/M₁`. -/
theorem actual_profile_corrected_inner_le_L1
    {B0 T : ℝ} (hB4 : (4 : ℝ) ≤ B0) (hT : (1 : ℝ) ≤ T)
    (hB0T : B0 ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T)
    {M1 M2 : ℕ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2)
    {m1 : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (xi : ℝ) :
    ‖sourceCorrectedM2FourierInner (sourcePositiveDyadicRange M2)
      (FourierTransform.fourier
        (fun u : ℝ => (lemma84Profile B0 W u : ℂ))) m1 xi‖ ≤
      6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
        (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) := by
  have hBpos : 0 < B0 := lt_of_lt_of_le (by norm_num) hB4
  have hf := lemma84Profile_sourceAdmissibleProfile_raw hB4 hT hB0T W hW
  have hL1 : 0 ≤ ∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖ := by positivity
  have hm1ne : m1 ≠ 0 := sourceSignedDyadicRange_ne_zero
    (lt_of_lt_of_le Nat.zero_lt_one hM1) hm1
  have hm1pos : 0 < (M1 : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hm2card : ((sourcePositiveDyadicRange M2).card : ℝ) ≤ 3 * (M2 : ℝ) :=
    card_sourcePositiveDyadicRange_cast_le_three_mul hM2
  have hfourier : ∀ z : ℝ,
      ‖FourierTransform.fourier
        (fun u : ℝ => (lemma84Profile B0 W u : ℂ)) z‖ ≤
        ∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖ := by
    exact profile_fourier_l1_bound hf
  unfold sourceCorrectedM2FourierInner
  calc
    ‖∑ m2 ∈ sourcePositiveDyadicRange M2,
        ((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          FourierTransform.fourier
            (fun u : ℝ => (lemma84Profile B0 W u : ℂ))
            (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ ≤
      ∑ m2 ∈ sourcePositiveDyadicRange M2,
        ‖((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
          FourierTransform.fourier
            (fun u : ℝ => (lemma84Profile B0 W u : ℂ))
            (((m2 : ℝ) / (m1 : ℝ)) * xi)‖ := norm_sum_le _ _
    _ ≤ ∑ _m2 ∈ sourcePositiveDyadicRange M2,
        ((2 * (M2 : ℝ)) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) := by
      apply Finset.sum_le_sum
      intro m2 hm2
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (abs_nonneg _)]
      have hcoef := (sourceDyadic_ratio_bounds
        (lt_of_lt_of_le Nat.zero_lt_one hM1)
        (lt_of_lt_of_le Nat.zero_lt_one hM2) hm1 hm2).2
      exact mul_le_mul hcoef (hfourier _) (norm_nonneg _)
        (by positivity : 0 ≤ (2 * (M2 : ℝ)) / (M1 : ℝ))
    _ = ((sourcePositiveDyadicRange M2).card : ℝ) *
        (((2 * (M2 : ℝ)) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖)) := by simp
    _ ≤ (3 * (M2 : ℝ)) *
        (((2 * (M2 : ℝ)) / (M1 : ℝ)) *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖)) := by
      exact mul_le_mul_of_nonneg_right hm2card
        (mul_nonneg (by positivity) hL1)
    _ = 6 * (M2 : ℝ) ^ 2 / (M1 : ℝ) *
        (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) := by ring

theorem actual_profile_fourier_continuous
    {B0 T : ℝ} (hB4 : (4 : ℝ) ≤ B0) (hT : (1 : ℝ) ≤ T)
    (hB0T : B0 ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T) :
    Continuous (FourierTransform.fourier
      (fun u : ℝ => (lemma84Profile B0 W u : ℂ))) := by
  have hf := lemma84Profile_sourceAdmissibleProfile_raw hB4 hT hB0T W hW
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf.integrable.ofReal

/-! The full Fourier square is obtained from the literal finite source and the
actual profile's admissible rapid decay, then restricted to the medium set. -/
theorem actual_profile_medium_fourier_integrableOn
    {B0 T : ℝ} (hB4 : (4 : ℝ) ≤ B0) (hT : (1 : ℝ) ≤ T)
    (hB0T : B0 ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T)
    {M1 M2 M3 : ℕ} (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hM3 : 1 ≤ M3)
    (m3Range : Finset ℤ)
    (hM1T : (M1 : ℝ) ≤ T) (hM3T : (M3 : ℝ) ≤ T)
    {eta : ℝ} (heta : 0 < eta) :
    IntegrableOn (fun xi =>
      ‖FourierTransform.fourier
        (sourceGFinite (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M2) m3Range
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
          (fun x : ℝ => (lemma84Profile B0 W x : ℂ)) (M3 : ℝ)) xi‖ ^ 2)
      (mediumFrequencyRegion
        (sourceLowFrequencyCutoff T eta (M1 : ℝ) (M3 : ℝ))
        (sourceHighFrequencyCutoff T)) := by
  have hf := lemma84Profile_sourceAdmissibleProfile_raw hB4 hT hB0T W hW
  have hM1pos : 0 < M1 := lt_of_lt_of_le Nat.zero_lt_one hM1
  have hM2pos : 0 < M2 := lt_of_lt_of_le Nat.zero_lt_one hM2
  have hM3pos : 0 < M3 := lt_of_lt_of_le Nat.zero_lt_one hM3
  have hglobal := integrable_norm_sq_fourier_sourceGFinite_of_sourceProfile
    (m1Range := sourceSignedDyadicRange M1)
    (m2Range := sourcePositiveDyadicRange M2) (m3Range := m3Range)
    (psi1 := fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))
    (fReal := lemma84Profile B0 W) (T := T)
    (S := lemma84ProfileScale W) (F := (6 : ℝ)) (M3 := (M3 : ℝ))
    (eta := (1 : ℝ)) (Rlo := (M2 : ℝ) / (2 * (M1 : ℝ)))
    (N1 := ((sourceSignedDyadicRange M1).card : ℝ))
    (N2 := ((sourcePositiveDyadicRange M2).card : ℝ))
    (N3 := (m3Range.card : ℝ)) (P1 := (1 : ℝ))
    (Rhi := 2 * (M2 : ℝ) / (M1 : ℝ))
    (hf := hf) (heta := by norm_num) (hT := le_trans zero_le_one hT)
    (hRlo := by positivity) (hN1 := by positivity) (hN2 := by positivity)
    (hN3 := by positivity) (hP1 := by positivity) (hRhi := by positivity)
    (hcard1 := le_rfl) (hcard2 := le_rfl) (hcard3 := le_rfl)
    (hm1 := fun _ hm => sourceSignedDyadicRange_ne_zero hM1 hm)
    (hm2 := fun _ hm => sourcePositiveDyadicRange_ne_zero hM2 hm)
    (hpsi := fun _ _ => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (sourceBump_nonneg 1 zero_lt_one _)]
      exact sourceBump_le_one 1 zero_lt_one _)
    (hratioLo := fun m1 hm1 m2 hm2 =>
      (sourceDyadic_ratio_bounds hM1pos hM2pos hm1 hm2).1)
    (hratioHi := fun m1 hm1 m2 hm2 =>
      (sourceDyadic_ratio_bounds hM1pos hM2pos hm1 hm2).2)
  exact hglobal.integrableOn

end GuthMaynardS3ActualProfileInputs

#print axioms GuthMaynardS3ActualProfileInputs.actual_profile_corrected_inner_le_L1
#print axioms GuthMaynardS3ActualProfileInputs.actual_profile_fourier_continuous
#print axioms GuthMaynardS3ActualProfileInputs.actual_profile_medium_fourier_integrableOn
