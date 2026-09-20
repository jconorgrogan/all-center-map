import MajorArcPublicLiftBridge
import ContinuousKernelMajorArcBridge

/-!
# Final analytic weld for the MAP major arcs

Every MAP-owned bridge is proved here.  The final theorem exposes only the two
source-level analytic inputs that are still external to the current Lean tree:

1. the pointwise MRT/Siegel--Walfisz approximation on reduced rational arcs;
2. the quantitative tail from the truncated Ramanujan series to the public
   Hardy--Littlewood singular series.
-/

namespace MAPMajorArcFinalAnalyticWeld

open AddCircle
open MAPMajorArcWeld MAPMajorArcIntegratedError
  MAPMajorArcPublicLiftBridge MAPContinuousOverlap
  MAPContinuousMajorArcBridge

noncomputable section

/-- The modeled finite rational-arc contribution differs from the exact
Hardy--Littlewood overlap only by the already-proved beta tail and the explicit
Ramanujan-tail discrepancy `T`. -/
theorem norm_modeledPaperMajorContribution_sub_overlapSingular_le
    {X T : ℝ} {B D : ℕ} {h : ℤ}
    (hX : 0 ≤ X) (hh : |(h : ℝ)| ≤ X)
    (hR : 0 < paperArcRadius X D) (hT : 0 ≤ T)
    (hRamanujan :
      ‖truncatedSingularCoefficient (paperDenominatorCutoff X B) h -
        ((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ ≤ T) :
    ‖modeledPaperMajorContribution X B D h -
        (((X - |(h : ℝ)|) *
          PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      (‖((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ + T) *
          (2 / (Real.pi ^ 2 * paperArcRadius X D)) +
        T * X := by
  let A : ℂ := truncatedSingularCoefficient (paperDenominatorCutoff X B) h
  let S : ℂ := ((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)
  let K : ℂ := truncatedContinuousKernel (dyadicContinuousAmplitude X)
    (paperArcRadius X D) h
  let O : ℂ := ((X - |(h : ℝ)| : ℝ) : ℂ)
  have hkernel : ‖K - O‖ ≤ 2 / (Real.pi ^ 2 * paperArcRadius X D) := by
    exact norm_truncatedContinuousKernel_dyadic_sub_overlap_le hX hh hR
  have hA : ‖A‖ ≤ ‖S‖ + T := by
    calc
      ‖A‖ = ‖(A - S) + S‖ := by congr 1; ring
      _ ≤ ‖A - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ T + ‖S‖ := by
        simpa [A, S] using add_le_add_right hRamanujan ‖S‖
      _ = ‖S‖ + T := by ring
  have hO : ‖O‖ ≤ X := by
    dsimp [O]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hh)]
    linarith [abs_nonneg (h : ℝ)]
  rw [modeledPaperMajorContribution_factor]
  have hmodelCast :
      (((X - |(h : ℝ)|) * PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ) =
        O * S := by simp [O, S]
  rw [hmodelCast]
  change ‖A * K - O * S‖ ≤ _
  have hdecomp : A * K - O * S = A * (K - O) + (A - S) * O := by ring
  rw [hdecomp]
  calc
    ‖A * (K - O) + (A - S) * O‖ ≤
        ‖A * (K - O)‖ + ‖(A - S) * O‖ := norm_add_le _ _
    _ = ‖A‖ * ‖K - O‖ + ‖A - S‖ * ‖O‖ := by rw [norm_mul, norm_mul]
    _ ≤ (‖S‖ + T) * (2 / (Real.pi ^ 2 * paperArcRadius X D)) +
        T * X := by
      gcongr

/-- End-to-end source-faithful major-arc theorem.  All normalization, mask,
integration, finite summation, continuous-kernel, and error-propagation steps
are internal Lean proofs.  The two premises named `hpointwise` and
`hRamanujan` are exactly the first remaining source-level analytic leaves. -/
theorem norm_majorCoefficient_sub_overlapSingular_le
    {X E T : ℝ} {B D : ℕ} {h : ℤ}
    (hX : 1 < X) (hE : 0 ≤ E) (hT : 0 ≤ T)
    (hh : |(h : ℝ)| ≤ X)
    (hR : 0 < paperArcRadius X D)
    (hRhalf : paperArcRadius X D < (1 : ℝ) / 2)
    (hgrowth : 2 * (Real.log X) ^ (D + 2 * B) < X)
    (hpointwise : ∀ q a : ℕ, ∀ β : ℝ,
      1 ≤ q → (q : ℝ) ≤ (Real.log X) ^ B →
      a < q → a.Coprime q →
      |β| ≤ paperArcRadius X D →
      ‖PrimePairEndpoints.primeExponentialSum X
          (rationalCenter q a + (β : UnitAddCircle)) -
        primeMajorCoefficient q * dyadicAmplitude X β‖ ≤ E)
    (hRamanujan :
      ‖truncatedSingularCoefficient (paperDenominatorCutoff X B) h -
        ((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ ≤ T) :
    ‖MAPHarmonicEndpoint.majorCoefficient X B D h -
        (((X - |(h : ℝ)|) *
          PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
          (2 * paperArcRadius X D * (E * (2 * X + E))) +
        (‖((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ + T) *
          (2 / (Real.pi ^ 2 * paperArcRadius X D)) +
        T * X := by
  have hprime :=
    norm_majorCoefficient_sub_modeledPaperMajorContribution_le_coarse
      (h := h) hX hE hRhalf hgrowth hpointwise
  have hmodel := norm_modeledPaperMajorContribution_sub_overlapSingular_le
    (by linarith : 0 ≤ X) hh hR hT hRamanujan
  calc
    ‖MAPHarmonicEndpoint.majorCoefficient X B D h -
        (((X - |(h : ℝ)|) *
          PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ ≤
      ‖MAPHarmonicEndpoint.majorCoefficient X B D h -
          modeledPaperMajorContribution X B D h‖ +
        ‖modeledPaperMajorContribution X B D h -
          (((X - |(h : ℝ)|) *
            PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ := by
      rw [show MAPHarmonicEndpoint.majorCoefficient X B D h -
          (((X - |(h : ℝ)|) *
            PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ) =
        (MAPHarmonicEndpoint.majorCoefficient X B D h -
          modeledPaperMajorContribution X B D h) +
        (modeledPaperMajorContribution X B D h -
          (((X - |(h : ℝ)|) *
            PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)) by ring]
      exact norm_add_le _ _
    _ ≤ ((paperDenominatorCutoff X B : ℕ) : ℝ) ^ 2 *
          (2 * paperArcRadius X D * (E * (2 * X + E))) +
        ((‖((PrimePairEndpoints.singularSeriesTotal h : ℝ) : ℂ)‖ + T) *
          (2 / (Real.pi ^ 2 * paperArcRadius X D)) + T * X) :=
      add_le_add hprime hmodel
    _ = _ := by ring

end

end MAPMajorArcFinalAnalyticWeld
