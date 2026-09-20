import GuthMaynardS3RectangleSymmetry
import GuthMaynardS3RectangleSignSymmetry
import GuthMaynardS3RestrictedEnergy
import GuthMaynardAffineCrudeBound

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory Set
noncomputable section
namespace GuthMaynardS3BlockIntegralEnergy
open GuthMaynardJIteration GuthMaynardS3WideProfile
open GuthMaynardS3LiteralProfile GuthMaynardS3LiteralAffineReduction
open GuthMaynardS3LiteralBalancedGeometry GuthMaynardS3LiteralTruncation
open GuthMaynardS3BlockRectangle GuthMaynardS3RectangleSymmetry
open GuthMaynardRatioKernelIdentity GuthMaynardS3RestrictedEnergy
open GuthMaynardS3LiteralProfileFourier

/-- The literal diagonal sum on the selected ordered block. -/
def blockDiag (B : ℝ) (W : Finset ℝ) (Mcut i k d : ℕ) (v : ℝ) : ℝ :=
  ∑ p ∈ orderedBalancedBlock Mcut i k d,
    smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v) *
      smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v)

private lemma blockDiag_nonneg (B : ℝ) (W : Finset ℝ)
    (Mcut i k d : ℕ) (v : ℝ) : 0 ≤ blockDiag B W Mcut i k d v := by
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

private lemma blockDiag_continuousOn {B : ℝ} (hB : 0 < B) (W : Finset ℝ)
    (Mcut i k d : ℕ) :
    ContinuousOn (blockDiag B W Mcut i k d) (Icc (1/2 : ℝ) 2) := by
  apply continuousOn_finsetSum
  intro p hp v hv
  have hvne : v ≠ 0 := by linarith [hv.1]
  have hc : Continuous (affineCenter p.1.1 p.1.2 p.2) := by
    unfold affineCenter
    fun_prop
  have hs := smoothedRatio_continuous hB W
  exact ((hs.continuousAt.comp (f:=fun u => affineCenter p.1.1 p.1.2 p.2 u / u)
    (hc.continuousAt.div continuousAt_id hvne)).mul
    (hs.continuousAt.comp hc.continuousAt)).continuousWithinAt

private lemma rectangleRight_continuous {B : ℝ} (hB : 0 < B)
    (W : Finset ℝ) (Mcut k : ℕ) :
    Continuous (rectangleAffineSquareSumRight B W Mcut k) := by
  have hh : rectangleAffineSquareSumRight B W Mcut k =
      sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k)
        (fun u => wideProfile B W (-u)) := by
    funext v
    exact rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum B W Mcut k v
  rw [hh]
  apply continuous_sourceFiniteAffineSum
  exact (smoothedRatioSquare_continuous hB W).comp continuous_neg

private lemma rectangleRight_squareIntegrable {B : ℝ} (hB4 : 4 ≤ B)
    (W : Finset ℝ) (Mcut k : ℕ) :
    Integrable (fun v => rectangleAffineSquareSumRight B W Mcut k v ^ 2) := by
  have hf := wideProfile_sourceAdmissibleProfile (T:=B) (by linarith) hB4 le_rfl W
  have hwhole : rectangleAffineSquareSumRight B W Mcut k =
      sourceFiniteAffineSum (blockCoordinateRange Mcut k)
        (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k)
        (fun u => wideProfile B W (-u)) := by
    funext v
    exact rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum B W Mcut k v
  rw [hwhole]
  apply integrable_sq_sourceFiniteAffineSum
  · exact hf.continuous.comp continuous_neg
  · exact hf.squareIntegrable.comp_neg
  · intro m hm
    exact nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1
  · intro m hm
    exact nonzeroPrefix_ne_zero (Finset.mem_filter.mp hm).1

/-- The literal block diagonal has an integral energy bound with factor two,
without paying the cardinality of any frequency rectangle. -/
theorem integral_blockDiag_sq_le_rectangle_energy
    {B : ℝ} (hB4 : 4 ≤ B) (W : Finset ℝ)
    (Mcut i k d : ℕ) (hd : d < 4) :
    (∫ v in Icc (1/2 : ℝ) 2, blockDiag B W Mcut i k d v ^ 2) ≤
      2 * ∫ v : ℝ, rectangleAffineSquareSumRight B W Mcut k v ^ 2 := by
  have hB : 0 < B := by linarith
  let F := rectangleAffineSquareSumRight B W Mcut k
  have hF : Continuous F := rectangleRight_continuous hB W Mcut k
  have hF0 : ∀ v, 0 ≤ F v := by
    intro v
    apply Finset.sum_nonneg
    intro m1 hm1
    apply Finset.sum_nonneg
    intro m2 hm2
    apply Finset.sum_nonneg
    intro m3 hm3
    exact wideProfile_nonneg hB W _
  have hi : ContinuousOn (fun v : ℝ => v⁻¹) (Icc (1/2 : ℝ) 2) := by
    apply continuousOn_id.inv₀
    intro v hv
    change v ≠ 0
    linarith [hv.1]
  have hprod : IntegrableOn (fun v => F v⁻¹ * F v) (Icc (1/2 : ℝ) 2) :=
    ((hF.comp_continuousOn hi).mul hF.continuousOn).integrableOn_compact isCompact_Icc
  have hD : IntegrableOn (fun v => blockDiag B W Mcut i k d v ^ 2)
      (Icc (1/2 : ℝ) 2) :=
    ((blockDiag_continuousOn hB W Mcut i k d).pow 2).integrableOn_compact isCompact_Icc
  have hpoint : ∀ v ∈ Icc (1/2 : ℝ) 2,
      blockDiag B W Mcut i k d v ^ 2 ≤ F v⁻¹ * F v := by
    intro v hv
    have hvne : v ≠ 0 := by linarith [hv.1]
    have hc := orderedBalancedBlock_diag_sq_le hB W Mcut i k d v
    have hr := block_square_sums_le_rectangles hB W Mcut i k d hd v
    have hb0 : 0 ≤ blockAffineSquareSumRight B W Mcut i k d v := by
      apply Finset.sum_nonneg
      intro p hp
      exact wideProfile_nonneg hB W _
    have hl0 : 0 ≤ rectangleAffineSquareSum B W Mcut k v := by
      rw [rectangleAffineSquareSum_eq_right_inv W Mcut k hvne]
      exact hF0 _
    have hm := mul_le_mul hr.1 hr.2 hb0 hl0
    have hh := hc.trans hm
    rw [rectangleAffineSquareSum_eq_right_inv W Mcut k hvne] at hh
    exact hh
  have hbound := setIntegral_mono_on hD hprod measurableSet_Icc hpoint
  exact hbound.trans (integral_product_inversion_le_two F hF hF0
    (rectangleRight_squareIntegrable hB4 W Mcut k))

/-- Weighted restricted Cauchy bound for the actual finite block. -/
theorem weighted_blockDiag_sq_le_rectangle_energy
    {B : ℝ} (hB4 : 4 ≤ B) (W : Finset ℝ)
    (Mcut i k d : ℕ) (hd : d < 4) :
    (∫ v in Icc (1/2 : ℝ) 2,
      ‖ratioDirichletKernel W v‖ * blockDiag B W Mcut i k d v)^2 ≤
      2 * (∫ v in Icc (1/2 : ℝ) 2, ‖ratioDirichletKernel W v‖^2) *
        (∫ v : ℝ, rectangleAffineSquareSumRight B W Mcut k v ^ 2) := by
  have hB : 0 < B := by linarith
  have hR : ContinuousOn (fun v => ‖ratioDirichletKernel W v‖)
      (Icc (1/2 : ℝ) 2) := by
    intro v hv
    have hvne : v ≠ 0 := by linarith [hv.1]
    exact (continuousAt_ratioDirichletKernel W hvne).norm.continuousWithinAt
  have hc := restricted_cauchy_sq (fun v => ‖ratioDirichletKernel W v‖)
    (blockDiag B W Mcut i k d) hR (blockDiag_continuousOn hB W Mcut i k d)
    (fun v => norm_nonneg _) (blockDiag_nonneg B W Mcut i k d)
  have he := integral_blockDiag_sq_le_rectangle_energy hB4 W Mcut i k d hd
  have hR2 : 0 ≤ ∫ v in Icc (1/2 : ℝ) 2, ‖ratioDirichletKernel W v‖^2 :=
    integral_nonneg (fun v => sq_nonneg _)
  have hh := mul_le_mul_of_nonneg_left he hR2
  exact hc.trans (by simpa only [mul_assoc, mul_left_comm] using hh)


/-- Finite sum and integral interchange for the actual affine block. -/
theorem sum_affineProfileIntegral_eq_weighted_blockDiag
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) (Mcut i k d : ℕ) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
      affineProfileIntegral B W p.1.1 p.1.2 p.2) =
      ∫ v in Icc (1/2 : ℝ) 2,
        ‖ratioDirichletKernel W v‖ * blockDiag B W Mcut i k d v := by
  have hterm : ∀ p ∈ orderedBalancedBlock Mcut i k d,
      IntegrableOn (fun v : ℝ =>
        ‖ratioDirichletKernel W v‖ *
          smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v) *
          smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v))
        (Icc (1/2 : ℝ) 2) := by
    intro p hp
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro v hv
    have hvne : v ≠ 0 := by linarith [hv.1]
    have hc : Continuous (affineCenter p.1.1 p.1.2 p.2) := by
      unfold affineCenter
      fun_prop
    have hs := smoothedRatio_continuous hB W
    have hleft := hs.continuousAt.comp
      (f:=fun u => affineCenter p.1.1 p.1.2 p.2 u / u)
      (hc.continuousAt.div continuousAt_id hvne)
    have hright : ContinuousAt (fun u => smoothedRatio B W
        (affineCenter p.1.1 p.1.2 p.2 u)) v := hs.continuousAt.comp hc.continuousAt
    exact (((continuousAt_ratioDirichletKernel W hvne).norm.mul hleft).mul
      hright).continuousWithinAt
  symm
  calc
    _ = ∫ v in Icc (1/2 : ℝ) 2,
      ∑ p ∈ orderedBalancedBlock Mcut i k d,
        ‖ratioDirichletKernel W v‖ *
          smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v / v) *
          smoothedRatio B W (affineCenter p.1.1 p.1.2 p.2 v) := by
      apply integral_congr_ae
      filter_upwards with v
      simp only [blockDiag, Finset.mul_sum, mul_assoc]
    _ = _ := integral_finsetSum _ hterm

/-- Actual block affine integrals are controlled by the canonical finite
energy of the original wide profile. The middle signed dyadic shell remains
unchanged; there is no frequency-cardinality loss. -/
theorem sum_affineProfileIntegral_sq_le_source_energy
    {B : ℝ} (hB4 : 4 ≤ B) (W : Finset ℝ)
    (Mcut i k d : ℕ) (hd : d < 4) :
    (∑ p ∈ orderedBalancedBlock Mcut i k d,
      affineProfileIntegral B W p.1.1 p.1.2 p.2)^2 ≤
      2 * (∫ v in Icc (1/2 : ℝ) 2, ‖ratioDirichletKernel W v‖^2) *
        sourceFiniteAffineEnergy (blockCoordinateRange Mcut k)
          (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k) (wideProfile B W) := by
  rw [sum_affineProfileIntegral_eq_weighted_blockDiag (by linarith) W Mcut i k d]
  have hh := weighted_blockDiag_sq_le_rectangle_energy hB4 W Mcut i k d hd
  simp_rw [GuthMaynardS3RectangleSignSymmetry.rectangleAffineSquareSumRight_eq_sourceFiniteAffineSum_wide] at hh
  exact hh

open GuthMaynardS3LiteralRadialDecay
/-- The selected balanced affine contribution, with its actual radial scale. -/
theorem orderedBalancedBlockAffine_sq_le_source_energy
    (N : ℕ) (W : Finset ℝ) (rho : ℝ) (Mcut i k d : ℕ) (hd : d < 4)
    (hB4 : 4 ≤ (N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) :
    orderedBalancedBlockAffine N W rho Mcut i k d ^ 2 ≤
      2 * (16 * radialDerivativeBudget 0 * rho * (N : ℝ)^2 / (2^k : ℝ))^2 *
        (∫ v in Icc (1/2 : ℝ) 2, ‖ratioDirichletKernel W v‖^2) *
        sourceFiniteAffineEnergy (blockCoordinateRange Mcut k)
          (blockMiddleRange Mcut k) (blockCoordinateRange Mcut k)
          (wideProfile ((N : ℝ) * (2 ^ k : ℝ) / (4 * rho)) W) := by
  have hh := mul_le_mul_of_nonneg_left
    (sum_affineProfileIntegral_sq_le_source_energy hB4 W Mcut i k d hd)
    (sq_nonneg (16 * radialDerivativeBudget 0 * rho * (N : ℝ)^2 / (2^k : ℝ)))
  unfold orderedBalancedBlockAffine
  rw [mul_pow]
  convert hh using 1 <;> ring

end GuthMaynardS3BlockIntegralEnergy
#print axioms GuthMaynardS3BlockIntegralEnergy.integral_blockDiag_sq_le_rectangle_energy
#print axioms GuthMaynardS3BlockIntegralEnergy.weighted_blockDiag_sq_le_rectangle_energy

#print axioms GuthMaynardS3BlockIntegralEnergy.orderedBalancedBlockAffine_sq_le_source_energy
