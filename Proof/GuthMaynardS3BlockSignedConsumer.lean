import GuthMaynardS3DilatedRectangleConsumer
import GuthMaynardS3BlockIntegralEnergy
import GuthMaynardS3ScaledWideMoments

open scoped BigOperators Real
open MeasureTheory Set
noncomputable section
namespace GuthMaynardS3BlockSignedConsumer
open GuthMaynardJIteration GuthMaynardS3ScaledWideProfile GuthMaynardS3WideProfile
open GuthMaynardS3LiteralLemma82 GuthMaynardHeathBrownInterface
open GuthMaynardS3DilatedRectangleConsumer GuthMaynardS3BlockIntegralEnergy
open GuthMaynardS3LiteralAffineReduction GuthMaynardS3LiteralBalancedGeometry
open GuthMaynardEquation55Infinite GuthMaynardS3LiteralTruncation
open GuthMaynardS3LiteralRadialDecay

/-- Source block consumer with the exact radial prefactor and all dyadic-bin
multiplicity retained. The bin estimate is an explicit input to this adapter. -/
theorem block_affine_sq_le_of_signed_bins
    (N : ℕ) (W : Finset ℝ) (rho : ℝ) (A i k d : ℕ)
    {T eta V : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hsep : TEtaSeparated W T eta) (hW : ContainedInIntervalOfLength W T)
    (hd : d < 4) (hB4 : 4 ≤ (N : ℝ)*2^k/(4*rho))
    (hbin : ∀ j ∈ Finset.range (k+7),
      sourceFiniteAffineEnergy (sourceSignedDyadicRange (2^j))
        (sourcePositiveDyadicRange (2^(k+2))) (sourceCenteredRange (16*2^(k+2)))
        (scaledWideProfile ((N : ℝ)*2^k/(4*rho)) W) ≤ V) :
    orderedBalancedBlockAffine N W rho A i k d ^ 2 ≤
      8 * (16 * radialDerivativeBudget 0 * rho * (N : ℝ)^2 / (2^k : ℝ))^2 *
        lemma82Constant eta * W.card * (k+7 : ℝ)^2 * V := by
  let B : ℝ := (N : ℝ)*2^k/(4*rho)
  have hB1 : 1 ≤ B := by dsimp [B]; linarith
  have hp := scaledWideProfile_sourceAdmissibleProfile (T:=B) hB1 hB4 (le_refl B) W
  have hp' : SourceAdmissibleProfile B (4*(W.card:ℝ)^2) (7/4)
      (fun v => wideProfile B W (4*v)) := hp
  have hE := rectangle_energy_le_of_dilated_signed_bound hp' A k (by
    simpa only [scaledWideProfile, B] using! hbin)
  have hbase := orderedBalancedBlockAffine_sq_le_source_energy N W rho A i k d hd hB4
  have hout := integral_ratioDirichletKernel_sq_on_unit_le hT heta hsep hW
  have hE0 : 0 ≤ sourceFiniteAffineEnergy
      (GuthMaynardS3BlockRectangle.blockCoordinateRange A k)
      (GuthMaynardS3BlockRectangle.blockMiddleRange A k)
      (GuthMaynardS3BlockRectangle.blockCoordinateRange A k) (wideProfile B W) :=
    integral_nonneg (fun u => sq_nonneg _)
  have hC0 := lemma82Constant_nonneg eta
  have houter := mul_le_mul_of_nonneg_right hout hE0
  have houter' := mul_le_mul_of_nonneg_left houter
    (by positivity : 0 ≤ 2*(16 * radialDerivativeBudget 0 * rho * (N : ℝ)^2 / (2^k : ℝ))^2)
  have henergy := mul_le_mul_of_nonneg_left hE
    (by positivity : 0 ≤ 2*(16 * radialDerivativeBudget 0 * rho * (N : ℝ)^2 / (2^k : ℝ))^2 *
      (lemma82Constant eta * W.card))
  dsimp [B] at houter' henergy
  nlinarith [hbase, houter', henergy]

end GuthMaynardS3BlockSignedConsumer
#print axioms GuthMaynardS3BlockSignedConsumer.block_affine_sq_le_of_signed_bins
