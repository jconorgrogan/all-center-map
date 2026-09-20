import GuthMaynardS3SignedSubpower
import GuthMaynardS3MomentTailEnvelope
import GuthMaynardS3ScaledWideMoments

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory
noncomputable section
set_option maxHeartbeats 3000000
namespace GuthMaynardS3SignedMassEnvelope

open GuthMaynardJIteration
open GuthMaynardS3SignedSubpower
open GuthMaynardS3MomentTailEnvelope
open GuthMaynardS3ScaledWideMoments
open GuthMaynardS3ScaledWideProfile
open GuthMaynardS3LiteralLemma83Energy
open GuthMaynardS3LiteralLemma83Transfer
open GuthMaynardS3LiteralLemma82
open GuthMaynardHeathBrownInterface

/-- The signed S3 energy bound with the two source moments exposed.  The
source horizon `T` and analytic horizon `U` are independent. -/
theorem scaledWide_signed_mass_envelope
    {epsilon eta : ℝ} (heps : 0 < epsilon)
    (heta : 0 < eta) (heta1 : eta ≤ 1) :
    ∃ Ce Cm T0 : ℝ, 0 < Ce ∧ 0 < Cm ∧ 0 < T0 ∧
      ∀ (T U B : ℝ) (W : Finset ℝ) (M1 M : ℕ),
        1 ≤ T → T0 ≤ U → 4 ≤ B → B ≤ U →
        (W.card : ℝ) ≤ 2 * T →
        TEtaSeparated W T eta → ContainedInIntervalOfLength W T →
        4 * (W.card : ℝ)^2 ≤ U^(4 : ℝ) →
        1 ≤ M1 → 1 ≤ M → M1 ≤ 16 * M → 16 * (M : ℝ) ≤ U →
        sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
          (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
          (scaledWideProfile B W) ≤
        Ce * U^epsilon *
          ((M : ℝ)^6 * (lemma82Constant eta * (W.card : ℝ))^2 +
           (M : ℝ)^4 * (Cm * Real.rpow T eta *
              (sourceApproximateAdditiveEnergy W : ℝ) +
              Cm * Real.rpow T (-400 : ℝ)) +
           (M : ℝ)^4 / U^100) := by
  obtain ⟨Ce, hCe, T0, hcap⟩ := scaledWide_signed_energy_subpower heps
  obtain ⟨Ceta, hCeta, htail⟩ :=
    lemma83EnergyBound_scaled_uniform heta heta1
  let Tstar : ℝ := max 1 T0
  have hTstar : 0 < Tstar := by
    dsimp [Tstar]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Ce, Ceta, Tstar, hCe, hCeta, hTstar, ?_⟩
  intro T U B W M1 M hT hUT hB4 hBU hcard hsep hcontained hUcard
    hM1 hM hM1hi hMU
  change sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
      (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
      (scaledWideProfile B W) ≤
    Ce * U^epsilon *
      ((M : ℝ)^6 * (lemma82Constant eta * (W.card : ℝ))^2 +
       (M : ℝ)^4 * (Ceta * Real.rpow T eta *
          (sourceApproximateAdditiveEnergy W : ℝ) +
          Ceta * Real.rpow T (-400 : ℝ)) +
       (M : ℝ)^4 / U^100)
  have hUT0 : T0 ≤ U :=
    (le_max_right (1 : ℝ) T0).trans hUT
  have hU1 : 1 ≤ U :=
    (le_max_left (1 : ℝ) T0).trans hUT
  have hTeta : 0 < Real.rpow T eta := Real.rpow_pos_of_pos
    (lt_of_lt_of_le zero_lt_one hT) eta
  have hR4 : 4 ≤ 4 * Real.rpow T eta := by
    have : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT (le_of_lt heta)
    nlinarith
  let q : ℕ := sourceS3MomentTailOrder eta
  have hmass := scaledWideProfile_masses_le hB4 hT heta hsep hcontained
    hR4 q
  have htailT := htail T W hT hcard
  have hLtarget :
      (∫ u : ℝ, scaledWideProfile B W u) ≤
        lemma82Constant eta * (W.card : ℝ) := hmass.1
  have hL0 : 0 ≤ ∫ u : ℝ, scaledWideProfile B W u :=
    integral_nonneg (fun u => scaledWideProfile_nonneg (by positivity) W u)
  have hLtarget0 : 0 ≤ lemma82Constant eta * (W.card : ℝ) :=
    mul_nonneg (lemma82Constant_nonneg eta) (by positivity)
  have hLsq :
      (∫ u : ℝ, scaledWideProfile B W u)^2 ≤
        (lemma82Constant eta * (W.card : ℝ))^2 :=
    (sq_le_sq₀ hL0 hLtarget0).2 hLtarget
  have hQtarget :
      (∫ u : ℝ, scaledWideProfile B W u ^ 2) ≤
        Ceta * Real.rpow T eta * (sourceApproximateAdditiveEnergy W : ℝ) +
          Ceta * Real.rpow T (-400 : ℝ) := by
    have htailT' := htailT
    change 48 * lemma83EnergyBound W (4 * Real.rpow T eta)
      (by positivity) q ≤
      Ceta * Real.rpow T eta * (sourceApproximateAdditiveEnergy W : ℝ) +
        Ceta * Real.rpow T (-400 : ℝ) at htailT'
    exact hmass.2.trans htailT'
  have hcap' := hcap U B W M1 M hUT0 hB4 hBU hUcard hM1 hM hM1hi hMU
  calc
    sourceFiniteAffineEnergy (sourceSignedDyadicRange M1)
        (sourcePositiveDyadicRange M) (sourceCenteredRange (16 * M))
        (scaledWideProfile B W) ≤
      Ce * U^epsilon *
        ((M : ℝ)^6 * (∫ u : ℝ, scaledWideProfile B W u)^2 +
         (M : ℝ)^4 * (∫ u : ℝ, scaledWideProfile B W u ^ 2) +
         (M : ℝ)^4 / U^100) := hcap'
    _ ≤ Ce * U^epsilon *
        ((M : ℝ)^6 * (lemma82Constant eta * (W.card : ℝ))^2 +
         (M : ℝ)^4 * (Ceta * Real.rpow T eta *
            (sourceApproximateAdditiveEnergy W : ℝ) +
            Ceta * Real.rpow T (-400 : ℝ)) +
         (M : ℝ)^4 / U^100) := by
      gcongr

end GuthMaynardS3SignedMassEnvelope

#print axioms GuthMaynardS3SignedMassEnvelope.scaledWide_signed_mass_envelope
