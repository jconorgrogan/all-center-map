import GuthMaynardS3StartingProfile
import GuthMaynardS3LiteralProfileFourier

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3ZeroEllLowAbsorption

open GuthMaynardJIteration
open GuthMaynardS3LiteralProfile
open GuthMaynardS3LiteralProfileFourier

/-- The literal nonnegative Lemma-8.4 profile has L1 mass equal to the
real integral used by the low-frequency estimate. -/
theorem lemma84Profile_L1_eq_integral
    {B : ℝ} (hB : 0 < B) (W : Finset ℝ) :
    (∫ u : ℝ, ‖(lemma84Profile B W u : ℂ)‖) =
      ∫ u : ℝ, lemma84Profile B W u := by
  apply integral_congr_ae
  filter_upwards with u
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (lemma84Profile_nonneg hB W u)]

/-- The zero-ell contribution's `T^eta` factor is dominated by the allowed
`T^(3 eta)` low main term, with the fixed source bump seminorm retained. -/
theorem zeroEllTail_le_extendedLowMain
    {T eta M : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hM : 0 ≤ M) (L K : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    9216 * K ^ 2 * Real.rpow T eta * M ^ 6 * L ^ 2 ≤
      9216 * K ^ 2 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by
  have hU : 0 ≤ Real.rpow T eta :=
    Real.rpow_nonneg (le_trans zero_le_one hT) eta
  have hU1 : 1 ≤ Real.rpow T eta := Real.one_le_rpow hT heta.le
  have hU3 : Real.rpow T eta ≤ (Real.rpow T eta) ^ 3 := by
    have hU2 : (Real.rpow T eta) ^ 2 ≤ (Real.rpow T eta) ^ 3 := by
      calc
        (Real.rpow T eta) ^ 2 = (Real.rpow T eta) ^ 2 * 1 := by ring
        _ ≤ (Real.rpow T eta) ^ 2 * Real.rpow T eta :=
          mul_le_mul_of_nonneg_left hU1 (sq_nonneg _)
        _ = (Real.rpow T eta) ^ 3 := by ring
    calc
      Real.rpow T eta ≤ (Real.rpow T eta) ^ 2 := by
        calc
          Real.rpow T eta = Real.rpow T eta * 1 := by ring
          _ ≤ Real.rpow T eta * Real.rpow T eta :=
            mul_le_mul_of_nonneg_left hU1 hU
          _ = (Real.rpow T eta) ^ 2 := by ring
      _ ≤ (Real.rpow T eta) ^ 3 := hU2
  have hpow : (Real.rpow T eta) ^ 3 = Real.rpow T (3 * eta) := by
    rw [show (3 : ℝ) * eta = eta * 3 by ring]
    exact (Real.rpow_mul_natCast (le_trans zero_le_one hT) eta 3).symm
  rw [← hpow]
  gcongr

/-- Combining the existing low main term with the explicit zero-ell tail only
changes its fixed absolute coefficient; no `Kψ ≤ 1` normalization is used. -/
theorem combined_zeroEll_low_main
    {T eta M : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hM : 0 ≤ M) (L K : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    57600 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 +
        9216 * K ^ 2 * Real.rpow T eta * M ^ 6 * L ^ 2 ≤
      (57600 + 9216 * K ^ 2) * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by
  have htail := zeroEllTail_le_extendedLowMain hT heta hM L K hK hL
  calc
    57600 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 +
        9216 * K ^ 2 * Real.rpow T eta * M ^ 6 * L ^ 2 ≤
      57600 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 +
        9216 * K ^ 2 * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 :=
      add_le_add le_rfl htail
    _ = (57600 + 9216 * K ^ 2) * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by ring

/-- The same absorption with the literal profile and fixed unit-bump Fourier
constant, using the actual L1 normalization carried by the source profile. -/
theorem combined_zeroEll_low_main_actualProfile
    {T eta B0 M : ℝ} (hT : 1 ≤ T) (heta : 0 < eta)
    (hB0 : 0 < B0) (hM : 0 ≤ M) (W : Finset ℝ) :
    57600 * Real.rpow T (3 * eta) * M ^ 6 *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) ^ 2 +
        9216 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2 *
          Real.rpow T eta * M ^ 6 *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) ^ 2 ≤
      (57600 + 9216 * (sourceBumpFourierConstant 1 zero_lt_one 0) ^ 2) *
        Real.rpow T (3 * eta) * M ^ 6 *
          (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖) ^ 2 := by
  apply combined_zeroEll_low_main hT heta hM
    (∫ u : ℝ, ‖(lemma84Profile B0 W u : ℂ)‖)
    (sourceBumpFourierConstant 1 zero_lt_one 0)
    (sourceBumpFourierConstant_nonneg 1 zero_lt_one 0)
    (integral_nonneg fun u => norm_nonneg _)

end GuthMaynardS3ZeroEllLowAbsorption

#print axioms GuthMaynardS3ZeroEllLowAbsorption.lemma84Profile_L1_eq_integral
#print axioms GuthMaynardS3ZeroEllLowAbsorption.combined_zeroEll_low_main
#print axioms GuthMaynardS3ZeroEllLowAbsorption.combined_zeroEll_low_main_actualProfile
