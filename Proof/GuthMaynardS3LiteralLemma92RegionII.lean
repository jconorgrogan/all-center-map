import GuthMaynardJIterationBumpWeld
import GuthMaynardLemma92ProfileRegularity
import GuthMaynardLocalizedPairIntegrability

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3LiteralLemma92RegionII

open GuthMaynardJIteration

/-!
# Literal Region-II coefficient and localized-pair integrability premise

The medium geometry uses the same phase interval `[-B,B]` as the retained and
tail kernels, hence the actual phase parameter is `Ctau = B`.  For the
positive dyadic `m₂,m₂'` range, `|m₂|, |m₂'| ≤ 2*M`, so the coefficient
parameter in the canonical producer is `c = 2`.  The determinant support
calculation supplies the literal window `Y = 4*M*F`; no centered-collar
inclusion is used.
-/

/- The fixed unit-bump Fourier supremum used for `psi₂` in the second Poisson
   step.  This is kept separate from the coefficient comparison so that the
   constant is not replaced by an unspecified norm. -/
theorem sourceRegionII_fixed_psi2_fourier_sup :
    0 ≤ sourceBumpFourierConstant 1 zero_lt_one 0 ∧
      (∀ xi, ‖FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) xi‖ ≤
          sourceBumpFourierConstant 1 zero_lt_one 0) := by
  refine ⟨sourceBumpFourierConstant_nonneg 1 zero_lt_one 0, ?_⟩
  intro xi
  simpa using sourceBump_fourier_decay 1 zero_lt_one 0 xi

/- The only scale arithmetic needed after the exact second-Poisson estimate.
   It is deliberately stated with the actual `Ctau = B` and `c = 2`. -/
theorem sourceRegionII_actual_Ctau_coefficient_le
    {M1 M2 M3 B Ksup : ℝ}
    (hM1 : 1 ≤ M1) (hM2 : 0 < M2) (hM3 : 1 ≤ M3)
    (hB : 0 ≤ B) (hKsup : 0 ≤ Ksup) :
    ((2 * B * Ksup) * (2 : ℝ) ^ 2 * M2) ≤
      (4 * B * Ksup) * M2 * (M1 + M3) := by
  have hsum : (2 : ℝ) ≤ M1 + M3 := by linarith
  have hscale : 0 ≤ (4 * B * Ksup) * M2 := by positivity
  calc
    ((2 * B * Ksup) * (2 : ℝ) ^ 2 * M2) =
        ((4 * B * Ksup) * M2) * 2 := by ring
    _ ≤ ((4 * B * Ksup) * M2) * (M1 + M3) := by
      exact mul_le_mul_of_nonneg_left hsum hscale
    _ = (4 * B * Ksup) * M2 * (M1 + M3) := by ring

/- This specialization makes the scale loss explicit when the affine profile
   radius is the usual `B = T^η`; `Cη` is then proportional to `T^η`, not a
   uniform constant in `T`. -/
theorem sourceRegionII_actual_Ctau_coefficient_le_rpow
    {T eta M1 M2 M3 Ksup : ℝ}
    (hT : 0 < T) (hM1 : 1 ≤ M1) (hM2 : 0 < M2)
    (hM3 : 1 ≤ M3) (hKsup : 0 ≤ Ksup) :
    ((2 * Real.rpow T eta * Ksup) * (2 : ℝ) ^ 2 * M2) ≤
      (4 * Real.rpow T eta * Ksup) * M2 * (M1 + M3) := by
  exact sourceRegionII_actual_Ctau_coefficient_le hM1 hM2 hM3
    (Real.rpow_nonneg hT.le eta) hKsup

/-!
The old whole-frequency producer needs this exact premise as
`hmediumLocalizedInt`.  It follows from continuity of the two Fourier fields
and the finite indicator expansion; no estimate or centered-collar inclusion
is hidden here.
-/
theorem sourceRegionII_mediumLocalizedPairIntegrable_unitBump
    {T S F M3 B a b : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    (hM3 : 0 < M3) (hB : 0 ≤ B)
    (m1Range ellRange m2Range : Finset ℤ) :
    IntegrableOn (fun xi : ℝ =>
      ‖sourceFirstPoissonLocalizedPairSum m1Range ellRange m2Range
        (FourierTransform.fourier
          (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)))
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M3 B xi‖ ^ 2) (mediumFrequencyRegion a b) := by
  have hbumpInt : Integrable
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)) :=
    (sourceBump 1 zero_lt_one).integrable.ofReal
  have hbumpFourierCont : Continuous
      (FourierTransform.fourier
        (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hbumpInt
  have hfFourierCont := continuous_fourier_of_integrable f hf.integrable
  exact (sourceFirstPoissonLocalizedPairSum_regionIntegrable
    m1Range ellRange m2Range
    (FourierTransform.fourier
      (fun x : ℝ => (sourceBump 1 zero_lt_one x : ℂ)))
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
    hbumpFourierCont hfFourierCont hM3 hB).2

end GuthMaynardS3LiteralLemma92RegionII

#print axioms GuthMaynardS3LiteralLemma92RegionII.sourceRegionII_fixed_psi2_fourier_sup
#print axioms GuthMaynardS3LiteralLemma92RegionII.sourceRegionII_actual_Ctau_coefficient_le
#print axioms GuthMaynardS3LiteralLemma92RegionII.sourceRegionII_actual_Ctau_coefficient_le_rpow
#print axioms GuthMaynardS3LiteralLemma92RegionII.sourceRegionII_mediumLocalizedPairIntegrable_unitBump
