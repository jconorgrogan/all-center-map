import GuthMaynardS3LiteralLemma84Outer

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section

namespace GuthMaynardS3LiteralLemma84Outer

open GuthMaynardJIteration GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier
open GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity

/-! # Proposition 9.1 starting profile package

The literal outer profile has height at most `4*|W|²`: the ratio profile is
bounded by `|W|²`, while the raw unit bump used in its affine smoothing has
mass at most four.  This file packages that exact height, and separately
normalizes by it when `W` is nonempty. -/

def lemma84ProfileScale (W : Finset ℝ) : ℝ :=
  4 * (W.card : ℝ) ^ 2

def lemma84ProfileNormalized (B : ℝ) (W : Finset ℝ) : ℝ → ℝ :=
  fun u => lemma84Profile B W u / lemma84ProfileScale W

theorem lemma84Profile_pointwise_le_scale
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (u : ℝ) :
    lemma84Profile B W u ≤ lemma84ProfileScale W := by
  have hsm := affineSmoothing_le_mass_mul (T := B)
    hB (fun z => sourceBump 1 zero_lt_one z) (ratioProfile W)
    (sourceBump_nonneg 1 zero_lt_one)
    (show 0 ≤ (W.card : ℝ) ^ 2 by positivity)
    (ratioProfile_nonneg W) (ratioProfile_le_card_sq W)
    (integral_sourceBump_le_four_mul zero_lt_one)
    (sourceBump 1 zero_lt_one).integrable (ratioProfile_continuous W) u
  exact (lemma84Profile_le_smoothedRatioSquare hB W u).trans
    (by simpa [lemma84ProfileScale] using hsm)

theorem lemma84ProfileScale_nonneg (W : Finset ℝ) :
    0 ≤ lemma84ProfileScale W := by
  unfold lemma84ProfileScale
  positivity

theorem lemma84Profile_sourceAdmissibleProfile_raw
    {B T : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T) :
    SourceAdmissibleProfile T (lemma84ProfileScale W) 6
      (lemma84Profile B W) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hbound : ∀ u, lemma84Profile B W u ≤ lemma84ProfileScale W :=
    lemma84Profile_pointwise_le_scale hBpos W
  have hcont : Continuous (lemma84Profile B W) :=
    lemma84Profile_continuous hBpos W
  have hsquare : HasCompactSupport (fun u => lemma84Profile B W u ^ 2) := by
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (-6 : ℝ) 6))
    intro u hu
    by_contra hne
    have hprof : lemma84Profile B W u ≠ 0 := by
      intro hzero
      apply hne
      simp [hzero]
    exact hu (abs_le.mp (lemma84Profile_supported W hprof))
  refine
    { nonneg := lemma84Profile_nonneg hBpos W
      bounded := hbound
      supported := fun u hu => lemma84Profile_supported W hu
      integrable := lemma84Profile_integrable hBpos W
      squareIntegrable :=
        (hcont.pow 2).integrable_of_hasCompactSupport hsquare
      continuous := hcont
      rapidDecay := ?_ }
  exact lemma84Profile_sourceFourierRapidDecay hB hT hBT W hW hbound
    (lemma84ProfileScale_nonneg W)

theorem lemma84Profile_empty
    {B : ℝ} (Wempty : W = ∅) :
    lemma84Profile B W = fun _ => 0 := by
  subst W
  have hratio : ratioProfile (∅ : Finset ℝ) = fun _ => 0 := by
    funext u
    simp [ratioProfile, GuthMaynardRatioKernelIdentity.ratioDirichletKernel]
  funext u
  simp [lemma84Profile, smoothedRatioSquare, hratio, affineSmoothing]

theorem lemma84Profile_sourceAdmissibleProfile_empty
    {B T : ℝ} (hB : 0 < B) (hT : 0 < T) :
    SourceAdmissibleProfile T 0 6 (lemma84Profile B (∅ : Finset ℝ)) := by
  have hzero := lemma84Profile_empty (B := B) (W := (∅ : Finset ℝ)) rfl
  rw [hzero]
  refine
    { nonneg := fun u => by simp
      bounded := fun u => by simp
      supported := fun u hu => (hu rfl).elim
      integrable := MeasureTheory.integrable_zero ℝ ℝ volume
      squareIntegrable := by
        simpa using (MeasureTheory.integrable_zero ℝ ℝ volume)
      continuous := continuous_zero
      rapidDecay := ?_ }
  intro eta heta j
  refine ⟨0, by positivity, ?_⟩
  intro z hz
  simp [Real.fourier_real_eq_integral_exp_smul]

theorem lemma84ProfileScale_pos_of_nonempty
    (W : Finset ℝ) (hWne : W.Nonempty) :
    0 < lemma84ProfileScale W := by
  have hc : 0 < (W.card : ℝ) := by
    exact_mod_cast (Finset.card_pos.mpr hWne)
  unfold lemma84ProfileScale
  nlinarith

theorem lemma84ProfileNormalized_pointwise_nonneg
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty) (u : ℝ) :
    0 ≤ lemma84ProfileNormalized B W u := by
  unfold lemma84ProfileNormalized
  exact div_nonneg (lemma84Profile_nonneg hB W u)
    (lemma84ProfileScale_nonneg W)

theorem lemma84ProfileNormalized_pointwise_le_one
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty) (u : ℝ) :
    lemma84ProfileNormalized B W u ≤ 1 := by
  unfold lemma84ProfileNormalized
  apply (div_le_iff₀ (lemma84ProfileScale_pos_of_nonempty W hWne)).2
  simpa using lemma84Profile_pointwise_le_scale hB W u

theorem lemma84ProfileNormalized_supported
    {B : ℝ} (W : Finset ℝ) (hWne : W.Nonempty) {u : ℝ}
    (hu : lemma84ProfileNormalized B W u ≠ 0) : |u| ≤ 6 := by
  apply lemma84Profile_supported W
  intro hzero
  apply hu
  unfold lemma84ProfileNormalized
  rw [hzero]
  simp

theorem lemma84ProfileNormalized_integrable
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty) :
    Integrable (lemma84ProfileNormalized B W) := by
  have h := (lemma84Profile_integrable hB W).const_mul
    (lemma84ProfileScale W)⁻¹
  convert h using 1
  funext u
  unfold lemma84ProfileNormalized
  ring

theorem lemma84ProfileNormalized_continuous
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty) :
    Continuous (lemma84ProfileNormalized B W) := by
  unfold lemma84ProfileNormalized
  exact (lemma84Profile_continuous hB W).div_const (lemma84ProfileScale W)

theorem lemma84ProfileNormalized_squareIntegrable
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty) :
    Integrable (fun u => lemma84ProfileNormalized B W u ^ 2) := by
  have hcont := lemma84ProfileNormalized_continuous hB W hWne
  have hsquare : HasCompactSupport
      (fun u => lemma84ProfileNormalized B W u ^ 2) := by
    apply HasCompactSupport.intro
      (isCompact_Icc : IsCompact (Set.Icc (-6 : ℝ) 6))
    intro u hu
    by_contra hne
    have hprof : lemma84ProfileNormalized B W u ≠ 0 := by
      intro hzero
      apply hne
      simp [hzero]
    exact hu (abs_le.mp (lemma84ProfileNormalized_supported W hWne hprof))
  exact (hcont.pow 2).integrable_of_hasCompactSupport hsquare

theorem lemma84ProfileNormalized_sourceFourierRapidDecay
    {B T : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T) (hWne : W.Nonempty) :
    SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun u : ℝ => (lemma84ProfileNormalized B W u : ℂ))) T 1 := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hS : 0 < lemma84ProfileScale W :=
    lemma84ProfileScale_pos_of_nonempty W hWne
  have hraw := lemma84Profile_sourceFourierRapidDecay hB hT hBT W hW
    (lemma84Profile_pointwise_le_scale hBpos W)
    (lemma84ProfileScale_nonneg W)
  have hfun :
      (fun u : ℝ => (lemma84ProfileNormalized B W u : ℂ)) =
        (fun u : ℝ => ((lemma84ProfileScale W)⁻¹ : ℂ) *
          (lemma84ProfileC B W u)) := by
    funext u
    simp [lemma84ProfileNormalized, lemma84ProfileC]
    push_cast
    field_simp
  intro eta heta j
  obtain ⟨C, hC, hbound⟩ := hraw eta heta j
  refine ⟨C, hC, ?_⟩
  intro z hz
  have hnorm :
      ‖FourierTransform.fourier
          (fun u : ℝ => (lemma84ProfileNormalized B W u : ℂ)) z‖ =
        (lemma84ProfileScale W)⁻¹ *
          ‖FourierTransform.fourier (lemma84ProfileC B W) z‖ := by
    rw [hfun, source_fourier_const_mul, norm_mul]
    simp [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hS]
  rw [hnorm]
  calc
    (lemma84ProfileScale W)⁻¹ *
          ‖FourierTransform.fourier (lemma84ProfileC B W) z‖ ≤
        (lemma84ProfileScale W)⁻¹ *
          (C * T ^ eta * (T / |z|) ^ j * lemma84ProfileScale W) := by
      exact mul_le_mul_of_nonneg_left (hbound z hz) (le_of_lt (inv_pos.mpr hS))
    _ = C * T ^ eta * (T / |z|) ^ j * 1 := by
      field_simp

theorem lemma84Profile_sourceAdmissibleProfile_normalized
    {B T : ℝ} (hB : (4 : ℝ) ≤ B) (hT : (1 : ℝ) ≤ T)
    (hBT : B ≤ T) (W : Finset ℝ)
    (hW : ContainedInIntervalOfLength W T) (hWne : W.Nonempty) :
    SourceAdmissibleProfile T 1 6 (lemma84ProfileNormalized B W) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hB
  refine
    { nonneg := fun u => lemma84ProfileNormalized_pointwise_nonneg hBpos W hWne u
      bounded := fun u => lemma84ProfileNormalized_pointwise_le_one hBpos W hWne u
      supported := fun u hu => lemma84ProfileNormalized_supported W hWne hu
      integrable := lemma84ProfileNormalized_integrable hBpos W hWne
      squareIntegrable := lemma84ProfileNormalized_squareIntegrable hBpos W hWne
      continuous := lemma84ProfileNormalized_continuous hBpos W hWne
      rapidDecay := ?_ }
  exact lemma84ProfileNormalized_sourceFourierRapidDecay hB hT hBT W hW hWne

/-! ## Exact homogeneity of the affine energy and its common `Jcoll` supremum -/

theorem sourceFiniteAffineEnergy_eq_scale_of_affine_scale
    {T c : ℝ} (m1Range m2Range jRange : Finset ℤ)
    (g h psi : ℝ → ℝ)
    (hscale : ∀ x : ℝ, affineSmoothing T psi g x =
      c * affineSmoothing T psi h x) :
    sourceFiniteAffineEnergy m1Range m2Range jRange
        (affineSmoothing T psi g) =
      c ^ 2 * sourceFiniteAffineEnergy m1Range m2Range jRange
        (affineSmoothing T psi h) := by
  have hsum : ∀ u : ℝ,
      sourceFiniteAffineSum m1Range m2Range jRange
          (affineSmoothing T psi g) u =
        c * sourceFiniteAffineSum m1Range m2Range jRange
          (affineSmoothing T psi h) u := by
    intro u
    unfold sourceFiniteAffineSum
    simp_rw [hscale]
    simp only [← Finset.mul_sum]
  unfold sourceFiniteAffineEnergy
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [hsum]
  ring

theorem sourceAffineJ_eq_scale_of_affine_scale
    {T c : ℝ} (hc : 0 < c)
    (mUniverse jUniverse : Finset ℤ) (g h psi : ℝ → ℝ)
    (hscale : ∀ x : ℝ, affineSmoothing T psi g x =
      c * affineSmoothing T psi h x) :
    sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
        (affineSmoothing T psi g) =
      c ^ 2 * sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
        (affineSmoothing T psi h) := by
  let configs := sourceAffineConfigs mUniverse jUniverse
  let raw := affineSmoothing T psi g
  let norm := affineSmoothing T psi h
  have hE (cfg : Finset ℤ × Finset ℤ × Finset ℤ) :
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw =
        c ^ 2 * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm := by
    exact sourceFiniteAffineEnergy_eq_scale_of_affine_scale
      cfg.1 cfg.2.1 cfg.2.2 g h psi hscale
  have hraw_le : sourceAffineJ configs raw ≤
      c ^ 2 * sourceAffineJ configs norm := by
    apply sourceAffineJ_le_of_forall_config mUniverse jUniverse raw
      (c ^ 2 * sourceAffineJ configs norm)
    intro cfg hcfg
    calc
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw =
          c ^ 2 * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm := hE cfg
      _ ≤ c ^ 2 * sourceAffineJ configs norm := by
        exact mul_le_mul_of_nonneg_left
          (sourceFiniteAffineEnergy_le_sourceAffineJ configs norm
            (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse norm)
            hcfg)
          (sq_nonneg _)
  apply le_antisymm hraw_le
  have hnorm_le : sourceAffineJ configs norm ≤
      (c ^ 2)⁻¹ * sourceAffineJ configs raw := by
    apply sourceAffineJ_le_of_forall_config mUniverse jUniverse norm
      ((c ^ 2)⁻¹ * sourceAffineJ configs raw)
    intro cfg hcfg
    calc
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm =
          (c ^ 2)⁻¹ * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw := by
        rw [hE cfg]
        field_simp
      _ ≤ (c ^ 2)⁻¹ * sourceAffineJ configs raw := by
        exact mul_le_mul_of_nonneg_left
          (sourceFiniteAffineEnergy_le_sourceAffineJ configs raw
            (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse raw)
            hcfg)
          (inv_nonneg.mpr (sq_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hnorm_le (sq_nonneg c)
  calc
    c ^ 2 * sourceAffineJ configs norm ≤
        c ^ 2 * ((c ^ 2)⁻¹ * sourceAffineJ configs raw) := hmul
    _ = sourceAffineJ configs raw := by
      field_simp

theorem sourceAffineJ_lemma84Profile_eq_scale_normalized
    {B T : ℝ} (hB : 0 < B) (W : Finset ℝ) (hWne : W.Nonempty)
    (mUniverse jUniverse : Finset ℤ) (psi f : ℝ → ℝ) :
    sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
        (affineSmoothing T psi
          (fun u => lemma84Profile B W u * f u)) =
      lemma84ProfileScale W ^ 2 *
        sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
          (affineSmoothing T psi
            (fun u => lemma84ProfileNormalized B W u * f u)) := by
  have hscale :
      affineSmoothing T psi (fun u => lemma84Profile B W u * f u) =
        (fun x => lemma84ProfileScale W *
          (affineSmoothing T psi
            (fun u => lemma84ProfileNormalized B W u * f u) x)) := by
    funext x
    unfold affineSmoothing lemma84ProfileNormalized
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    field_simp [(lemma84ProfileScale_pos_of_nonempty W hWne).ne']
  apply sourceAffineJ_eq_scale_of_affine_scale
    (lemma84ProfileScale_pos_of_nonempty W hWne)
    mUniverse jUniverse
    (fun u => lemma84Profile B W u * f u)
    (fun u => lemma84ProfileNormalized B W u * f u) psi
    (fun x => congrFun hscale x)

end GuthMaynardS3LiteralLemma84Outer

#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_sourceAdmissibleProfile_raw
#print axioms GuthMaynardS3LiteralLemma84Outer.lemma84Profile_sourceAdmissibleProfile_normalized
#print axioms GuthMaynardS3LiteralLemma84Outer.sourceAffineJ_lemma84Profile_eq_scale_normalized
