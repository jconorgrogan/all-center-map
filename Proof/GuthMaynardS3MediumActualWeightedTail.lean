import GuthMaynardS3MediumActualAlgebra

open scoped BigOperators Real FourierTransform

noncomputable section
namespace GuthMaynardS3MediumActualWeightedTail

/-- Weighted Sigma-II tail absorption with the finite-cardinality factor kept
explicit.  The quotient is handled as `N²/T¹⁰⁰`; no negative-power
normalization is used. -/
theorem weightedSigma_tail_le_actualLowMain
    {T eta Ceta K M M1 M2 M3 D L N Q : ℝ}
    (hT : 1 ≤ T) (heta : 0 ≤ eta) (hCeta : 0 ≤ Ceta)
    (hK : 0 ≤ K) (hM : 1 ≤ M) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hM3 : 0 ≤ M3) (hM1M : M1 ≤ M) (hM2M : M2 ≤ M)
    (hM3M : M3 ≤ M) (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hN0 : 0 ≤ N) (hN : N ≤ T ^ (4 : ℕ))
    (hQ : Q ≤
      (800 * D * Real.rpow T eta * M2 ^ 2 * L ^ 2) *
        (N ^ 2 / T ^ (100 : ℕ))) :
    (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) * Q ≤
      25600 * Ceta * K ^ 2 * D * Real.rpow T (3 * eta) * M ^ 6 * L ^ 2 := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hU : 0 ≤ Real.rpow T eta := Real.rpow_nonneg hT0 eta
  have hU2 : 0 ≤ Real.rpow T (2 * eta) := Real.rpow_nonneg hT0 _
  have hsum0 : 0 ≤ M1 + M3 := by linarith
  have hA : 0 ≤ 16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3) := by
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCeta) hU2)
        (sq_nonneg K)) hsum0
  have hNpow : N ^ 2 ≤ T ^ (100 : ℕ) := by
    calc
      N ^ 2 ≤ (T ^ (4 : ℕ)) ^ 2 :=
        (sq_le_sq₀ hN0 (by positivity)).2 hN
      _ = T ^ (8 : ℕ) := by ring
      _ ≤ T ^ (100 : ℕ) := by
        exact pow_le_pow_right₀ hT (by norm_num)
  have hratio : N ^ 2 / T ^ (100 : ℕ) ≤ 1 := by
    exact (div_le_one (by positivity)).2 hNpow
  have hQ' : Q ≤ 800 * D * Real.rpow T eta * M2 ^ 2 * L ^ 2 := by
    have hfac : 0 ≤ 800 * D * Real.rpow T eta * M2 ^ 2 * L ^ 2 := by positivity
    calc
      Q ≤ (800 * D * Real.rpow T eta * M2 ^ 2 * L ^ 2) *
          (N ^ 2 / T ^ (100 : ℕ)) := hQ
      _ ≤ _ := by
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hratio hfac)
  have hmul := mul_le_mul_of_nonneg_left hQ' hA
  have hsum : M1 + M3 ≤ 2 * M := by linarith
  have hM2sq : M2 ^ 2 ≤ M ^ 2 :=
    (sq_le_sq₀ hM2 (by positivity)).2 hM2M
  have hMprod : (M1 + M3) * M2 ^ 2 ≤ 2 * M ^ 3 := by
    calc
      (M1 + M3) * M2 ^ 2 ≤ (2 * M) * M ^ 2 := by gcongr
      _ = 2 * M ^ 3 := by ring
  have hMpow : M ^ 3 ≤ M ^ 6 := by
    calc
      M ^ 3 ≤ M ^ 3 * M ^ 3 := by
        calc
          M ^ 3 = M ^ 3 * 1 := by ring
          _ ≤ M ^ 3 * M ^ 3 :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ hM) (by positivity)
      _ = M ^ 6 := by ring
  have hUprod : Real.rpow T (2 * eta) * Real.rpow T eta =
      Real.rpow T (3 * eta) := by
    calc
      Real.rpow T (2 * eta) * Real.rpow T eta =
          Real.rpow T ((2 * eta) + eta) :=
        (Real.rpow_add hTpos (2 * eta) eta).symm
      _ = Real.rpow T (3 * eta) := by congr 1 <;> ring
  calc
    _ ≤ (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) *
        (800 * D * Real.rpow T eta * M2 ^ 2 * L ^ 2) := hmul
    _ = 12800 * Ceta * K ^ 2 * D *
        (Real.rpow T (2 * eta) * Real.rpow T eta) *
        ((M1 + M3) * M2 ^ 2) * L ^ 2 := by ring
    _ ≤ 12800 * Ceta * K ^ 2 * D *
        (Real.rpow T (2 * eta) * Real.rpow T eta) *
        (2 * M ^ 6) * L ^ 2 := by
      have hcoef : 0 ≤ 12800 * Ceta * K ^ 2 * D *
          (Real.rpow T (2 * eta) * Real.rpow T eta) * L ^ 2 := by
        positivity
      have hprod : (M1 + M3) * M2 ^ 2 ≤ 2 * M ^ 6 :=
        hMprod.trans (mul_le_mul_of_nonneg_left hMpow (by positivity))
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_left hprod hcoef)
    _ = 25600 * Ceta * K ^ 2 * D * Real.rpow T (3 * eta) *
        M ^ 6 * L ^ 2 := by rw [hUprod]; ring

end GuthMaynardS3MediumActualWeightedTail

#print axioms GuthMaynardS3MediumActualWeightedTail.weightedSigma_tail_le_actualLowMain
