import GuthMaynardS3WideProfile

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3AffineCauchy

open GuthMaynardJIteration
open GuthMaynardS3LiteralProfile
open GuthMaynardRatioKernelIdentity
open GuthMaynardS3LiteralAffineReduction

/-- Literal Cauchy--Schwarz on the frequency interval.  The hypotheses expose
only the two continuity facts needed for the compact interval integrability;
no cutoff or pointwise domination is inserted. -/
theorem affineProfileIntegral_sq_le_restricted_energy
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (m1 m2 m3 : ℤ)
    (hRcont : ContinuousOn
      (fun v : ℝ => ‖ratioDirichletKernel W v‖)
      (Set.Icc (1 / 2 : ℝ) 2))
    (hQcont : ContinuousOn
      (fun v : ℝ =>
        smoothedRatio B W (affineCenter m1 m2 m3 v / v) *
          smoothedRatio B W (affineCenter m1 m2 m3 v))
      (Set.Icc (1 / 2 : ℝ) 2)) :
    (affineProfileIntegral B W m1 m2 m3) ^ 2 ≤
      (∫ v : ℝ in Set.Icc (1 / 2 : ℝ) 2,
        ‖ratioDirichletKernel W v‖ ^ 2) *
      (∫ v : ℝ in Set.Icc (1 / 2 : ℝ) 2,
        (smoothedRatio B W (affineCenter m1 m2 m3 v / v) *
          smoothedRatio B W (affineCenter m1 m2 m3 v)) ^ 2) := by
  let I : Set ℝ := Set.Icc (1 / 2 : ℝ) 2
  let μ : Measure ℝ := volume.restrict I
  let f : ℝ → ℝ := fun v => ‖ratioDirichletKernel W v‖
  let g : ℝ → ℝ := fun v =>
    smoothedRatio B W (affineCenter m1 m2 m3 v / v) *
      smoothedRatio B W (affineCenter m1 m2 m3 v)
  have hI : MeasurableSet I := by
    exact measurableSet_Icc
  have hfmeas : AEStronglyMeasurable f μ := by
    dsimp [f, μ, I]
    exact hRcont.aestronglyMeasurable measurableSet_Icc
  have hgmeas : AEStronglyMeasurable g μ := by
    dsimp [g, μ, I]
    exact hQcont.aestronglyMeasurable measurableSet_Icc
  have hf2 : Integrable (fun v => f v ^ (2 : ℕ)) μ := by
    dsimp [μ, I]
    exact (hRcont.pow 2).integrableOn_compact isCompact_Icc
  have hg2 : Integrable (fun v => g v ^ (2 : ℕ)) μ := by
    dsimp [μ, I]
    exact (hQcont.pow 2).integrableOn_compact isCompact_Icc
  have hfm : MemLp f 2 μ := by
    exact (memLp_two_iff_integrable_sq hfmeas).2 hf2
  have hgm : MemLp g 2 μ := by
    exact (memLp_two_iff_integrable_sq hgmeas).2 hg2
  have hpq : Real.HolderConjugate 2 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hh := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (f := f) (g := g) hpq
    (Filter.Eventually.of_forall (fun v => norm_nonneg (ratioDirichletKernel W v)))
    (Filter.Eventually.of_forall (fun v => by
      dsimp [g]
      simpa [g] using (mul_nonneg (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v / v)))
        (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v))))))
    (by simpa using hfm) (by simpa using hgm)
  have hnonnegA : 0 ≤ ∫ v : ℝ, f v ^ (2 : ℝ) ∂μ :=
    integral_nonneg (fun v => by positivity)
  have hnonnegB : 0 ≤ ∫ v : ℝ, g v ^ (2 : ℝ) ∂μ :=
    integral_nonneg (fun v => by
      apply Real.rpow_nonneg
      simpa [g] using (mul_nonneg (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v / v)))
        (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v)))))
  have hAroot : (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) := by
    rw [Real.sqrt_eq_rpow]
  have hBroot : (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) =
      Real.sqrt (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ) := by
    rw [Real.sqrt_eq_rpow]
  have hh' := hh
  rw [hAroot, hBroot] at hh'
  have hmain : (∫ v : ℝ, f v * g v ∂μ) ^ 2 ≤
      (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) *
        (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ) := by
    have hsA := Real.sq_sqrt hnonnegA
    have hsB := Real.sq_sqrt hnonnegB
    have hnonnegX : 0 ≤ ∫ v : ℝ, f v * g v ∂μ :=
      integral_nonneg (fun v => mul_nonneg (norm_nonneg _) (by
        simpa [g] using (mul_nonneg (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v / v)))
          (Real.sqrt_nonneg (smoothedRatioSquare B W (affineCenter m1 m2 m3 v))))))
    have hprod : 0 ≤ Real.sqrt (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) *
        Real.sqrt (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsq := (sq_le_sq₀ hnonnegX hprod).2 hh'
    calc
      (∫ v : ℝ, f v * g v ∂μ) ^ 2 ≤
          (Real.sqrt (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) *
            Real.sqrt (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ)) ^ 2 := hsq
      _ = (∫ v : ℝ, f v ^ (2 : ℝ) ∂μ) *
          (∫ v : ℝ, g v ^ (2 : ℝ) ∂μ) := by rw [mul_pow, hsA, hsB]
  simpa [μ, I, f, g, affineProfileIntegral, mul_assoc, Real.rpow_two] using hmain

/-- The continuity premises are automatic for the literal kernel and smoothed
ratio on the interval, whose points are bounded away from the pole at zero. -/
theorem affineProfileIntegral_sq_le_restricted_energy_literal
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    (affineProfileIntegral B W m1 m2 m3) ^ 2 ≤
      (∫ v : ℝ in Set.Icc (1 / 2 : ℝ) 2,
        ‖ratioDirichletKernel W v‖ ^ 2) *
      (∫ v : ℝ in Set.Icc (1 / 2 : ℝ) 2,
        (smoothedRatio B W (affineCenter m1 m2 m3 v / v) *
          smoothedRatio B W (affineCenter m1 m2 m3 v)) ^ 2) := by
  apply affineProfileIntegral_sq_le_restricted_energy hB W m1 m2 m3
  · intro v hv
    have hvne : v ≠ 0 := by linarith [hv.1]
    exact (continuousAt_ratioDirichletKernel W hvne).norm.continuousWithinAt
  · intro v hv
    have hvne : v ≠ 0 := by linarith [hv.1]
    have hc : Continuous (affineCenter m1 m2 m3) := by
      unfold affineCenter
      fun_prop
    have hsm := smoothedRatio_continuous hB W
    exact ((hsm.continuousAt.comp (f := fun u => affineCenter m1 m2 m3 u / u)
        (hc.continuousAt.div continuousAt_id hvne)).mul
      (hsm.continuousAt.comp hc.continuousAt)).continuousWithinAt

end GuthMaynardS3AffineCauchy

#print axioms GuthMaynardS3AffineCauchy.affineProfileIntegral_sq_le_restricted_energy
