import GuthMaynardS3LiteralAffineReduction

/-! # One common smoothing profile for a literal dyadic frequency block -/

namespace GuthMaynardS3LiteralScaleComparison

open MeasureTheory
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralAffineReduction
open GuthMaynardJIteration GuthMaynardRatioKernelIdentity

noncomputable section

/-- The comparison uses only the plateau and support of the concrete bump,
not an unproved monotonicity of its shape. -/
theorem smoothedRatioSquare_le_four {B B0 : ℝ} (hB0 : 0<B0)
    (hlo : 2*B0 ≤ B) (hhi : B ≤ 4*B0) (W : Finset ℝ) (c : ℝ) :
    smoothedRatioSquare B W c ≤ 4*smoothedRatioSquare B0 W c := by
  have hB : 0<B := by linarith
  have hfBound : ∀ u,|ratioProfile W u| ≤ (W.card : ℝ)^2 := by
    intro u
    rw [abs_of_nonneg (ratioProfile_nonneg W u)]
    exact ratioProfile_le_card_sq W u
  have hi (D : ℝ) (hD : 0<D) : Integrable (fun u =>
      D*sourceBump 1 zero_lt_one (D*(c-u))*ratioProfile W u) :=
    integrable_affineSmoothing_section hD _ _ (sourceBump 1 zero_lt_one).integrable
      (ratioProfile_continuous W) (sq_nonneg _) hfBound c
  unfold smoothedRatioSquare affineSmoothing
  rw [← integral_const_mul]
  apply integral_mono (hi B hB) ((hi B0 hB0).const_mul 4)
  intro u
  dsimp only
  by_cases hz : sourceBump 1 zero_lt_one (B*(c-u))=0
  · rw [hz,mul_zero,zero_mul]
    exact mul_nonneg (by norm_num) (mul_nonneg
      (mul_nonneg hB0.le (sourceBump_nonneg _ _ _)) (ratioProfile_nonneg W u))
  · have hs := sourceBump_supported_two_mul zero_lt_one hz
    have hs' : B*|c-u| ≤ 2 := by simpa only [abs_mul,abs_of_pos hB,mul_one] using hs
    have hlo' := mul_le_mul_of_nonneg_right hlo (abs_nonneg (c-u))
    have hplateau : |B0*(c-u)| ≤ 1 := by rw [abs_mul,abs_of_pos hB0]; nlinarith only [hs',hlo']
    rw [sourceBump_eq_one_of_abs_le 1 zero_lt_one hplateau,mul_one]
    have hh := mul_le_mul_of_nonneg_left (sourceBump_le_one 1 zero_lt_one (B*(c-u))) hB.le
    have hc : B*sourceBump 1 zero_lt_one (B*(c-u)) ≤ 4*B0 := by linarith
    have hf := mul_le_mul_of_nonneg_right hc (ratioProfile_nonneg W u)
    nlinarith only [hf]

theorem smoothedRatio_le_two {B B0 : ℝ} (hB0 : 0<B0)
    (hlo : 2*B0 ≤ B) (hhi : B ≤ 4*B0) (W : Finset ℝ) (c : ℝ) :
    smoothedRatio B W c ≤ 2*smoothedRatio B0 W c := by
  have hB : 0<B := by linarith
  have hs := smoothedRatioSquare_le_four hB0 hlo hhi W c
  have hsq1 := smoothedRatio_sq hB W c
  have hsq0 := smoothedRatio_sq hB0 W c
  have h0 : 0 ≤ 2*smoothedRatio B0 W c := by unfold smoothedRatio; positivity
  have hsq : (smoothedRatio B W c)^2 ≤ (2*smoothedRatio B0 W c)^2 := by nlinarith only [hs,hsq1,hsq0]
  exact (sq_le_sq₀ (Real.sqrt_nonneg _) h0).mp hsq

theorem affineProfileIntegral_le_four {B B0 : ℝ} (hB0 : 0<B0)
    (hlo : 2*B0 ≤ B) (hhi : B ≤ 4*B0) (W : Finset ℝ) (m1 m2 m3 : ℤ) :
    affineProfileIntegral B W m1 m2 m3 ≤ 4*affineProfileIntegral B0 W m1 m2 m3 := by
  have hB : 0<B := by linarith
  have hi (D : ℝ) (hD : 0<D) : IntegrableOn (fun v => ‖ratioDirichletKernel W v‖ *
      smoothedRatio D W (affineCenter m1 m2 m3 v/v) *
      smoothedRatio D W (affineCenter m1 m2 m3 v)) (Set.Icc (1/2 : ℝ) 2) := by
    apply ContinuousOn.integrableOn_compact (μ := volume) isCompact_Icc
    intro v hv
    have hvne : v≠0 := by linarith [hv.1]
    have hc : Continuous (affineCenter m1 m2 m3) := by unfold affineCenter; fun_prop
    have hsm := smoothedRatio_continuous hD W
    exact (((continuousAt_ratioDirichletKernel W hvne).norm.mul
      (hsm.continuousAt.comp (f := fun u => affineCenter m1 m2 m3 u/u)
        (hc.continuousAt.div continuousAt_id hvne))).mul
      (hsm.continuousAt.comp hc.continuousAt)).continuousWithinAt
  unfold affineProfileIntegral
  rw [← integral_const_mul]
  apply integral_mono_ae (hi B hB) ((hi B0 hB0).const_mul 4)
  filter_upwards with v
  have h1 := smoothedRatio_le_two hB0 hlo hhi W (affineCenter m1 m2 m3 v/v)
  have h2 := smoothedRatio_le_two hB0 hlo hhi W (affineCenter m1 m2 m3 v)
  have hm := mul_le_mul h1 h2 (Real.sqrt_nonneg _)
    (show 0 ≤ 2*smoothedRatio B0 W (affineCenter m1 m2 m3 v/v) by unfold smoothedRatio; positivity)
  have hs := mul_le_mul_of_nonneg_left hm (norm_nonneg (ratioDirichletKernel W v))
  nlinarith only [hs]

end
end GuthMaynardS3LiteralScaleComparison

#print axioms GuthMaynardS3LiteralScaleComparison.affineProfileIntegral_le_four
