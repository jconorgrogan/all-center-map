import GuthMaynardS3ZeroEllLowAbsorption
import GuthMaynardJIterationMediumRegionGeometry

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardS3MediumActualAlgebra

/-- The retained normalized-Sigma-II square-root term has a uniform source
shape.  This keeps the fixed bump Fourier constant explicit and uses only the
actual scale hypotheses `M1,M2,M3 ≤ M`; no equality of the two dyadic scales
is introduced. -/
theorem normalizedSigma_main_factor_le
    {T eta Ceta K M M1 M2 M3 R : ℝ}
    (hT : 1 ≤ T) (heta : 0 < eta) (hCeta : 0 ≤ Ceta)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hM3 : 0 ≤ M3) (hM1M : M1 ≤ M) (hM2M : M2 ≤ M)
    (hM3M : M3 ≤ M) (hR : 0 ≤ R) :
    (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) *
        ((2 * Real.rpow T eta * (4 * Real.rpow T eta * K)) *
          (2 : ℝ) ^ 2 * M2 * R) ≤
      2048 * Ceta * K ^ 3 * Real.rpow T (4 * eta) * M ^ 2 * R := by
  have hU : 0 ≤ Real.rpow T eta :=
    Real.rpow_nonneg (le_trans zero_le_one hT) eta
  have hU2 : 0 ≤ Real.rpow T (2 * eta) :=
    Real.rpow_nonneg (le_trans zero_le_one hT) _
  have hC : 0 ≤ 16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 := by positivity
  have hscale : (M1 + M3) * M2 ≤ 2 * M ^ 2 := by
    calc
      (M1 + M3) * M2 ≤ (M + M) * M := by gcongr
      _ = 2 * M ^ 2 := by ring
  have hbase := mul_le_mul_of_nonneg_right hscale hC
  have hpow : (Real.rpow T eta) ^ 4 = Real.rpow T (4 * eta) := by
    rw [show (4 : ℝ) * eta = eta * 4 by ring]
    exact (Real.rpow_mul_natCast (le_trans zero_le_one hT) eta 4).symm
  have hpow2 : Real.rpow T (2 * eta) = (Real.rpow T eta) ^ 2 := by
    rw [show (2 : ℝ) * eta = eta * 2 by ring]
    exact Real.rpow_mul_natCast (le_trans zero_le_one hT) eta 2
  calc
    (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) *
          ((2 * Real.rpow T eta * (4 * Real.rpow T eta * K)) *
            (2 : ℝ) ^ 2 * M2 * R) =
        (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2) *
          (32 * (Real.rpow T eta) ^ 2 * K * ((M1 + M3) * M2) * R) := by ring
    _ ≤ (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2) *
          (32 * (Real.rpow T eta) ^ 2 * K * (2 * M ^ 2) * R) := by
      gcongr
    _ = 1024 * Ceta * K ^ 3 * (Real.rpow T eta) ^ 4 * M ^ 2 * R := by
      rw [hpow2]
      ring
    _ = 1024 * Ceta * K ^ 3 * Real.rpow T (4 * eta) * M ^ 2 * R := by rw [hpow]
    _ ≤ 2048 * Ceta * K ^ 3 * Real.rpow T (4 * eta) * M ^ 2 * R := by
      have hfour : 0 ≤ Real.rpow T (4 * eta) :=
        Real.rpow_nonneg (le_trans zero_le_one hT) _
      have hprod : 0 ≤ Ceta * K ^ 3 * Real.rpow T (4 * eta) * M ^ 2 * R := by
        positivity
      nlinarith

end GuthMaynardS3MediumActualAlgebra

#print axioms GuthMaynardS3MediumActualAlgebra.normalizedSigma_main_factor_le
