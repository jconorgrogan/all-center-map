import GuthMaynardS3LiteralLocalization
import GuthMaynardS3LiteralAffineFiber

/-!
# Literal localized affine reduction of each S3 frequency

This is the per-frequency analytic content of Proposition 7.2. The two
profile arguments are (m1*v+m3)/(-m2*v) and (m1*v+m3)/(-m2), and the
smoothing scale is N*|m2|/(2*rho). Thus rho=T^eta remains an explicit
subpower enlargement of the source profile. The tail is not absorbed here.
-/

namespace GuthMaynardS3LiteralAffineReduction

open MeasureTheory
open scoped BigOperators
open GuthMaynardS3LiteralLocalization GuthMaynardS3LiteralAffineFiber
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralRadial
open GuthMaynardS3LiteralRadialDecay GuthMaynardRatioKernelIdentity GuthMaynardJIteration

noncomputable section

def affineCenter (m1 m2 m3 : ℤ) (v : ℝ) : ℝ := -((m1 : ℝ)*v+(m3 : ℝ))/(m2 : ℝ)

def affineProfileIntegral (B : ℝ) (W : Finset ℝ) (m1 m2 m3 : ℤ) : ℝ :=
  ∫ v : ℝ in Set.Icc (1/2 : ℝ) 2,
    ‖ratioDirichletKernel W v‖ *
      smoothedRatio B W (affineCenter m1 m2 m3 v/v) *
      smoothedRatio B W (affineCenter m1 m2 m3 v)

theorem ratioKernel_inv_conj (W : Finset ℝ) (u : ℝ) :
    ratioDirichletKernel W (1/u) = star (ratioDirichletKernel W u) := by
  unfold ratioDirichletKernel
  change _ = (starRingEnd ℂ) (∑ t ∈ W,_)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [one_div,abs_inv,Real.log_inv,← Complex.exp_conj]
  congr 1
  rw [map_mul,Complex.conj_I,Complex.conj_ofReal]
  push_cast
  ring

theorem norm_ratioKernel_inv (W : Finset ℝ) (u : ℝ) :
    ‖ratioDirichletKernel W (1/u)‖ = ‖ratioDirichletKernel W u‖ := by
  rw [ratioKernel_inv_conj,norm_star]

theorem smoothedRatio_continuous {B : ℝ} (hB : 0<B) (W : Finset ℝ) :
    Continuous (smoothedRatio B W) := by
  have hb : ∀ z,‖sourceBump 1 zero_lt_one z‖ ≤ (1:ℝ) := by
    intro z
    rw [Real.norm_eq_abs,abs_of_nonneg (sourceBump_nonneg _ _ _)]
    exact sourceBump_le_one _ _ _
  exact Real.continuous_sqrt.comp (continuous_affineSmoothing hB _ _ hb
    (sourceBump_contDiff 1 zero_lt_one).continuous (ratioProfile_integrable W))

theorem affine_strip_iff {N : ℕ} (hN : 0<N) {rho : ℝ} (hrho : 0<rho)
    (m1 m2 m3 : ℤ) (hm2 : m2≠0) (v u : ℝ) :
    |affineFrequency N m1 m2 m3 (v,u)| ≤ rho ↔
      |u-affineCenter m1 m2 m3 v| ≤ 1/(2*((N : ℝ)*|(m2 : ℝ)|/(2*rho))) := by
  have hNR : 0<(N : ℝ) := Nat.cast_pos.mpr hN
  have hmR : (m2 : ℝ)≠0 := Int.cast_ne_zero.mpr hm2
  have hden : 0<(N : ℝ)*|(m2 : ℝ)| := mul_pos hNR (abs_pos.mpr hmR)
  have hfreq : affineFrequency N m1 m2 m3 (v,u) =
      (N : ℝ)*(m2 : ℝ)*(u-affineCenter m1 m2 m3 v) := by
    unfold affineFrequency affineCenter
    field_simp
    ring
  have hwidth : 1/(2*((N : ℝ)*|(m2 : ℝ)|/(2*rho))) = rho/((N : ℝ)*|(m2 : ℝ)|) := by
    field_simp
  rw [hfreq,hwidth,abs_mul,abs_mul,abs_of_pos hNR]
  simpa only [mul_comm] using
    (le_div_iff₀ hden : |u-affineCenter m1 m2 m3 v| ≤ rho/((N : ℝ)*|(m2 : ℝ)|) ↔
      |u-affineCenter m1 m2 m3 v| *((N : ℝ)*|(m2 : ℝ)|) ≤ rho).symm

set_option maxHeartbeats 800000 in
theorem localizedRatioMass_le_affine {N : ℕ} (hN : 0<N) (W : Finset ℝ)
    (m1 m2 m3 : ℤ) (hm2 : m2≠0) {rho : ℝ} (hrho : 0<rho) :
    localizedRatioMass N W m1 m2 m3 rho ≤
      (2/((N : ℝ)*|(m2 : ℝ)|/(2*rho))) *
        affineProfileIntegral ((N : ℝ)*|(m2 : ℝ)|/(2*rho)) W m1 m2 m3 := by
  let B := (N : ℝ)*|(m2 : ℝ)|/(2*rho)
  have hB : 0<B := by dsimp [B]; exact div_pos (mul_pos (Nat.cast_pos.mpr hN)
    (abs_pos.mpr (Int.cast_ne_zero.mpr hm2))) (by positivity)
  let g : ℝ×ℝ → ℝ := fun p => if |affineFrequency N m1 m2 m3 p| ≤ rho then
    ‖radialRatioProduct W p.1 p.2‖ else 0
  have hcond : MeasurableSet {p : ℝ×ℝ | |affineFrequency N m1 m2 m3 p| ≤ rho} := by
    apply isClosed_le _ continuous_const |>.measurableSet
    unfold affineFrequency
    fun_prop
  have hg0 := (ratioProduct_continuousOn W).norm.integrableOn_compact
    (μ := volume) (isCompact_Icc.prod isCompact_Icc)
  have hg : IntegrableOn g ratioBox := hg0.indicator hcond
  have hinner (v : ℝ) : (∫ u : ℝ in Set.Icc (1/2 : ℝ) 2,g (v,u)) =
      ‖ratioDirichletKernel W v‖*affineFiberMass B (affineCenter m1 m2 m3 v) v W := by
    unfold affineFiberMass affineFiberWindow
    have hcv : MeasurableSet {u : ℝ | |u-affineCenter m1 m2 m3 v| ≤ 1/(2*B)} :=
      (isClosed_le (by fun_prop) continuous_const).measurableSet
    have heq : (∫ u : ℝ in Set.Icc (1/2 : ℝ) 2 ∩
        {u : ℝ | |u-affineCenter m1 m2 m3 v| ≤ 1/(2*B)},
          ‖ratioDirichletKernel W (u/v)‖*‖ratioDirichletKernel W u‖) =
      ∫ u : ℝ in Set.Icc (1/2 : ℝ) 2,
        ({u : ℝ | |u-affineCenter m1 m2 m3 v| ≤ 1/(2*B)}).indicator
          (fun u => ‖ratioDirichletKernel W (u/v)‖*‖ratioDirichletKernel W u‖) u := by
      rw [integral_indicator hcv,Measure.restrict_restrict hcv,Set.inter_comm]
    rw [heq,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    have hiff := affine_strip_iff hN hrho m1 m2 m3 hm2 v u
    by_cases hn : |affineFrequency N m1 m2 m3 (v,u)| ≤ rho
    · have hu := hiff.mp hn
      dsimp only [g]
      rw [if_pos hn,Set.indicator_of_mem (show u ∈ {z : ℝ | |z-affineCenter m1 m2 m3 v| ≤ 1/(2*B)} from hu)]
      unfold radialRatioProduct
      rw [norm_mul,norm_mul,norm_ratioKernel_inv]
      ring
    · have hu : ¬|u-affineCenter m1 m2 m3 v| ≤ 1/(2*B) := mt hiff.mpr hn
      dsimp only [g]
      rw [if_neg hn,Set.indicator_of_notMem (show u ∉ {z : ℝ | |z-affineCenter m1 m2 m3 v| ≤ 1/(2*B)} from hu),mul_zero]
  have hgOuter : IntegrableOn (fun v => ∫ u : ℝ in Set.Icc (1/2 : ℝ) 2,g (v,u))
      (Set.Icc (1/2 : ℝ) 2) := by
    have hh : Integrable g ((volume.restrict (Set.Icc (1/2 : ℝ) 2)).prod
        (volume.restrict (Set.Icc (1/2 : ℝ) 2))) := by
      rwa [Measure.prod_restrict]
    exact hh.integral_prod_left
  have hleft : IntegrableOn (fun v => ‖ratioDirichletKernel W v‖*
      affineFiberMass B (affineCenter m1 m2 m3 v) v W) (Set.Icc (1/2 : ℝ) 2) := by
    exact hgOuter.congr (Filter.Eventually.of_forall hinner)
  have hrightCont : ContinuousOn (fun v => ‖ratioDirichletKernel W v‖ *
      smoothedRatio B W (affineCenter m1 m2 m3 v/v) *
      smoothedRatio B W (affineCenter m1 m2 m3 v)) (Set.Icc (1/2 : ℝ) 2) := by
    intro v hv
    have hvne : v≠0 := by linarith [hv.1]
    have hc : Continuous (affineCenter m1 m2 m3) := by unfold affineCenter; fun_prop
    have hsm := smoothedRatio_continuous hB W
    exact (((continuousAt_ratioDirichletKernel W hvne).norm.mul
      (hsm.continuousAt.comp (f := fun u => affineCenter m1 m2 m3 u/u)
        (hc.continuousAt.div continuousAt_id hvne))).mul
      (hsm.continuousAt.comp hc.continuousAt)).continuousWithinAt
  have hright := hrightCont.integrableOn_compact (μ := volume) isCompact_Icc
  change (∫ p : ℝ×ℝ in Set.Icc (1/2 : ℝ) 2 ×ˢ Set.Icc (1/2 : ℝ) 2,
      g p ∂(volume : Measure ℝ).prod volume) ≤ (2/B)*affineProfileIntegral B W m1 m2 m3
  rw [setIntegral_prod _ hg]
  simp_rw [hinner]
  change (∫ v : ℝ in Set.Icc (1/2 : ℝ) 2,_) ≤ (2/B)*affineProfileIntegral B W m1 m2 m3
  unfold affineProfileIntegral
  rw [← integral_const_mul]
  apply integral_mono_ae hleft (hright.const_mul (2/B))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hh := mul_le_mul_of_nonneg_left (affineFiberMass_le hB hv W (c := affineCenter m1 m2 m3 v))
    (norm_nonneg (ratioDirichletKernel W v))
  nlinarith only [hh]


/-- The actual per-frequency Proposition 7.2 bound. Its only hypotheses are
N>0, m2≠0 and rho>0; the smoothed profile is constructed in this import chain.
Taking rho=T^eta gives the source's subpower collar with an explicit tail. -/
theorem norm_sourceIm_le_affine {N : ℕ} (hN : 0<N) (W : Finset ℝ)
    (m1 m2 m3 : ℤ) (hm2 : m2≠0) {rho : ℝ} (hrho : 0<rho) (q : ℕ) :
    ‖GuthMaynardEquation55Split.sourceIm N W m1 m2 m3‖ ≤
      (4*radialDerivativeBudget 0*rho*(N : ℝ)^2/|(m2 : ℝ)|) *
        affineProfileIntegral ((N : ℝ)*|(m2 : ℝ)|/(2*rho)) W m1 m2 m3 +
      (9/4 : ℝ)*(N : ℝ)^3*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q := by
  have hl := localizedRatioMass_le_affine hN W m1 m2 m3 hm2 hrho
  have hc := mul_le_mul_of_nonneg_left hl (radialDerivativeBudget_nonneg 0)
  have ht := norm_sourceIm_le_localized N W m1 m2 m3 hrho q
  have hs := mul_le_mul_of_nonneg_left (add_le_add_right hc
    ((9/4 : ℝ)*radialDerivativeBudget q*(W.card : ℝ)^3/rho^q))
    (show 0 ≤ (N : ℝ)^3 by positivity)
  have hs' := ht.trans (by simpa only [add_comm] using hs)
  apply hs'.trans_eq
  have hNR : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr hN.ne'
  have hmR : (m2 : ℝ)≠0 := Int.cast_ne_zero.mpr hm2
  field_simp [hNR,abs_ne_zero.mpr hmR,hrho.ne']
  ring

end
end GuthMaynardS3LiteralAffineReduction

#print axioms GuthMaynardS3LiteralAffineReduction.localizedRatioMass_le_affine

#print axioms GuthMaynardS3LiteralAffineReduction.norm_sourceIm_le_affine
