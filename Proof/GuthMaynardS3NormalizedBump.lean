import GuthMaynardLemma92ConcreteBump

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Normalized smoothing adapter for the concrete plateau bump

`sourceBump` is the literal majorant used by the concrete Sigma-II
producer.  Its mass is of size `B`, so it is not a `SourceSmoothingKernel`
when `B` is large.  The following adapter keeps that raw bump for the
majorization argument and exposes the normalized kernel separately.  Every
conversion back to the raw smoothing records the exact factor `4*B`.
-/

def sourceBumpNormalized (B : ℝ) (hB : 0 < B) : ℝ → ℝ :=
  fun z => sourceBump B hB z / (4 * B)

theorem sourceBumpNormalized_nonneg
    {B : ℝ} (hB : 0 < B) (z : ℝ) :
    0 ≤ sourceBumpNormalized B hB z := by
  exact div_nonneg (sourceBump_nonneg B hB z) (by positivity)

theorem sourceBumpNormalized_le_one
    {B : ℝ} (hB : 0 < B) (hB1 : 1 ≤ B) (z : ℝ) :
    sourceBumpNormalized B hB z ≤ 1 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * B)).2
  exact (sourceBump_le_one B hB z).trans (by nlinarith)

theorem sourceBumpNormalized_supported
    {B : ℝ} (hB : 0 < B) {z : ℝ}
    (hz : sourceBumpNormalized B hB z ≠ 0) : |z| ≤ 2 * B := by
  exact sourceBump_supported_two_mul hB (by
    intro hzero
    apply hz
    simp [sourceBumpNormalized, hzero])

theorem sourceBumpNormalized_integrable
    {B : ℝ} (hB : 0 < B) :
    Integrable (sourceBumpNormalized B hB) := by
  have h : Integrable (fun z : ℝ => (4 * B)⁻¹ * sourceBump B hB z) :=
    (sourceBump B hB).integrable.const_mul (4 * B)⁻¹
  convert h using 1
  funext z
  dsimp [sourceBumpNormalized]
  field_simp

theorem sourceBumpNormalized_continuous
    {B : ℝ} (hB : 0 < B) :
    Continuous (sourceBumpNormalized B hB) := by
  exact (sourceBump_contDiff B hB).continuous.div_const (4 * B)

theorem sourceBumpNormalized_mass_le_one
    {B : ℝ} (hB : 0 < B) :
    ∫ z : ℝ, sourceBumpNormalized B hB z ≤ 1 := by
  have hmass := integral_sourceBump_le_four_mul hB
  rw [show (fun z : ℝ => sourceBumpNormalized B hB z) =
      (fun z : ℝ => (4 * B)⁻¹ * sourceBump B hB z) by
    funext z
    dsimp [sourceBumpNormalized]
    field_simp]
  rw [integral_const_mul]
  calc
    (4 * B)⁻¹ * ∫ z : ℝ, sourceBump B hB z ≤
        (4 * B)⁻¹ * (4 * B) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = 1 := by field_simp

theorem sourceBumpNormalized_sourceSmoothingKernel
    {B : ℝ} (hB : 0 < B) (hB1 : 1 ≤ B) :
    SourceSmoothingKernel (2 * B) (sourceBumpNormalized B hB) := by
  refine
    { nonneg := sourceBumpNormalized_nonneg hB
      bounded := sourceBumpNormalized_le_one hB hB1
      supported := fun z hz => sourceBumpNormalized_supported hB hz
      integrable := sourceBumpNormalized_integrable hB
      continuous := sourceBumpNormalized_continuous hB
      mass_le_one := sourceBumpNormalized_mass_le_one hB }

theorem integral_sourceBump_ge_two_mul
    {B : ℝ} (hB : 0 < B) :
    2 * B ≤ ∫ z : ℝ, sourceBump B hB z := by
  have hset : (∫ z : ℝ in Set.Icc (-B) B, (1 : ℝ)) = 2 * B := by
    rw [MeasureTheory.setIntegral_const]
    rw [smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [← hset]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply MeasureTheory.integral_mono_ae
  · exact (MeasureTheory.integrableOn_const (C := (1 : ℝ))
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  · exact (sourceBump B hB).integrable
  · filter_upwards with z
    by_cases hz : z ∈ Set.Icc (-B) B
    · rw [Set.indicator_of_mem hz]
      exact sourceBump_one_le_of_abs_le B hB (by
        rw [Set.mem_Icc] at hz
        exact abs_le.2 ⟨by linarith, by linarith⟩)
    · rw [Set.indicator_of_notMem hz]
      exact sourceBump_nonneg B hB z

theorem sourceBump_not_sourceSmoothingKernel_of_one_le
    {B : ℝ} (hB : 0 < B) (hB1 : 1 ≤ B) :
    ¬ SourceSmoothingKernel (2 * B) (fun z => sourceBump B hB z) := by
  intro hkernel
  have hlow := integral_sourceBump_ge_two_mul hB
  have hupp := hkernel.mass_le_one
  nlinarith

theorem affineSmoothing_sourceBump_eq_scale_normalized
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B) (f : ℝ → ℝ) (x : ℝ) :
    affineSmoothing T (fun z => sourceBump B hB z) f x =
      (4 * B) * affineSmoothing T (sourceBumpNormalized B hB) f x := by
  unfold affineSmoothing sourceBumpNormalized
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  field_simp

theorem sourceFiniteAffineEnergy_sourceBump_eq_scale_normalized
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (m1Range m2Range jRange : Finset ℤ) (f : ℝ → ℝ) :
    sourceFiniteAffineEnergy m1Range m2Range jRange
        (affineSmoothing T (fun z => sourceBump B hB z) f) =
      (4 * B) ^ 2 * sourceFiniteAffineEnergy m1Range m2Range jRange
        (affineSmoothing T (sourceBumpNormalized B hB) f) := by
  have hscale : ∀ x : ℝ,
      affineSmoothing T (fun z => sourceBump B hB z) f x =
        (4 * B) * affineSmoothing T (sourceBumpNormalized B hB) f x := by
    intro x
    exact affineSmoothing_sourceBump_eq_scale_normalized
      hT hB f x
  have hsum : ∀ u : ℝ,
      sourceFiniteAffineSum m1Range m2Range jRange
          (affineSmoothing T (fun z => sourceBump B hB z) f) u =
        (4 * B) * sourceFiniteAffineSum m1Range m2Range jRange
          (affineSmoothing T (sourceBumpNormalized B hB) f) u := by
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

theorem sourceAffineJ_sourceBump_eq_scale_normalized
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (mUniverse jUniverse : Finset ℤ) (f : ℝ → ℝ) :
    sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
        (affineSmoothing T (fun z => sourceBump B hB z) f) =
      (4 * B) ^ 2 * sourceAffineJ (sourceAffineConfigs mUniverse jUniverse)
        (affineSmoothing T (sourceBumpNormalized B hB) f) := by
  let configs := sourceAffineConfigs mUniverse jUniverse
  let raw := affineSmoothing T (fun z => sourceBump B hB z) f
  let norm := affineSmoothing T (sourceBumpNormalized B hB) f
  have hE (cfg : Finset ℤ × Finset ℤ × Finset ℤ) :
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw =
        (4 * B) ^ 2 * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm := by
    exact sourceFiniteAffineEnergy_sourceBump_eq_scale_normalized hT hB
      cfg.1 cfg.2.1 cfg.2.2 f
  have hraw_le : sourceAffineJ configs raw ≤
      (4 * B) ^ 2 * sourceAffineJ configs norm := by
    apply sourceAffineJ_le_of_forall_config mUniverse jUniverse raw
      ((4 * B) ^ 2 * sourceAffineJ configs norm)
    intro cfg hcfg
    calc
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw =
          (4 * B) ^ 2 * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm := hE cfg
      _ ≤ (4 * B) ^ 2 * sourceAffineJ configs norm := by
        exact mul_le_mul_of_nonneg_left
          (sourceFiniteAffineEnergy_le_sourceAffineJ configs norm
            (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse norm)
            hcfg)
          (sq_nonneg _)
  apply le_antisymm hraw_le
  have hnorm_le : sourceAffineJ configs norm ≤
      ((4 * B) ^ 2)⁻¹ * sourceAffineJ configs raw := by
    apply sourceAffineJ_le_of_forall_config mUniverse jUniverse norm
      (((4 * B) ^ 2)⁻¹ * sourceAffineJ configs raw)
    intro cfg hcfg
    calc
      sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 norm =
          ((4 * B) ^ 2)⁻¹ * sourceFiniteAffineEnergy cfg.1 cfg.2.1 cfg.2.2 raw := by
        rw [hE cfg]
        field_simp
      _ ≤ ((4 * B) ^ 2)⁻¹ * sourceAffineJ configs raw := by
        exact mul_le_mul_of_nonneg_left
          (sourceFiniteAffineEnergy_le_sourceAffineJ configs raw
            (bddAbove_sourceAffineConfigEnergies mUniverse jUniverse raw)
            hcfg)
          (inv_nonneg.mpr (sq_nonneg _))
  have hmul := mul_le_mul_of_nonneg_left hnorm_le (sq_nonneg (4 * B))
  calc
    (4 * B) ^ 2 * sourceAffineJ configs norm ≤
        (4 * B) ^ 2 * (((4 * B) ^ 2)⁻¹ * sourceAffineJ configs raw) := hmul
    _ = sourceAffineJ configs raw := by
      field_simp

theorem sourceSigmaII_raw_bound_to_normalizedJcoll
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B) (f : ℝ → ℝ)
    (ellRange mRange jRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (M2 M3 Ctau A E : ℝ)
    (hraw :
      sigmaIIFinite ellRange mRange psi2
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          M2 T M3 Ctau ≤
        A * Real.sqrt ((∫ u : ℝ, f u ^ 2) *
          sourceAffineJ (sourceAffineConfigs mRange jRange)
            (affineSmoothing T (fun z => sourceBump B hB z) f)) + E) :
    sigmaIIFinite ellRange mRange psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      A * Real.sqrt ((∫ u : ℝ, f u ^ 2) *
        ((4 * B) ^ 2 * sourceAffineJ (sourceAffineConfigs mRange jRange)
          (affineSmoothing T (sourceBumpNormalized B hB) f))) + E := by
  have hJ := sourceAffineJ_sourceBump_eq_scale_normalized hT hB
    mRange jRange f
  rw [hJ] at hraw
  exact hraw

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceBumpNormalized_sourceSmoothingKernel
#print axioms GuthMaynardJIteration.integral_sourceBump_ge_two_mul
#print axioms GuthMaynardJIteration.sourceBump_not_sourceSmoothingKernel_of_one_le
#print axioms GuthMaynardJIteration.affineSmoothing_sourceBump_eq_scale_normalized
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_sourceBump_eq_scale_normalized
#print axioms GuthMaynardJIteration.sourceAffineJ_sourceBump_eq_scale_normalized
#print axioms GuthMaynardJIteration.sourceSigmaII_raw_bound_to_normalizedJcoll
