import GuthMaynardS3LiteralGlobalReduction

/-!
# Honest conversion from source-sized to absolute S3 errors

The literal truncation/localization errors carry `(N^3 |W|^3)`.  This file
records the extra growth contract needed before an `O(T⁻¹⁰⁰)` statement can
be consumed.  The conversion is intentionally separate from the analytic
tail proof: it cannot be obtained by renaming the source-sized bound.
-/

namespace GuthMaynardS3LiteralErrorContract

noncomputable section

/- The existing source order already leaves seven powers of `T` of reserve;
   expose that reserve before multiplying by the `N^3 |W|^3` growth. -/
def s3Uniform106DecayOrder (eta : ℝ) : ℕ :=
  Nat.ceil (110 / eta) + 4

theorem uniform106_order_reserve {eta : ℝ} (heta : 0 < eta) :
    110 + 4 * eta ≤ eta * (s3Uniform106DecayOrder eta : ℝ) := by
  have hceil : 110 / eta ≤ (Nat.ceil (110 / eta) : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil heta.le
  have hcancel : eta * (110 / eta) = 110 := by field_simp
  rw [hcancel] at hmul
  unfold s3Uniform106DecayOrder
  push_cast
  linarith

theorem uniform106_order_minus_one_reserve {eta : ℝ} (heta : 0 < eta) :
    110 + 3 * eta ≤ eta * (s3Uniform106DecayOrder eta - 1 : ℕ) := by
  have hceil : 110 / eta ≤ (Nat.ceil (110 / eta) : ℝ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil heta.le
  have hcancel : eta * (110 / eta) = 110 := by field_simp
  rw [hcancel] at hmul
  unfold s3Uniform106DecayOrder
  have hsub : Nat.ceil (110 / eta) + 4 - 1 = Nat.ceil (110 / eta) + 3 := by omega
  rw [hsub]
  push_cast
  linarith

theorem radial_uniform106_exponent {eta : ℝ} (heta : 0 < eta) :
    3 + 3 * eta - eta * (s3Uniform106DecayOrder eta : ℝ) ≤ -106 := by
  have h := uniform106_order_reserve heta
  linarith

theorem fourier_uniform106_exponent {eta : ℝ} (heta : 0 < eta) :
    3 + 2 * eta - eta * (s3Uniform106DecayOrder eta - 1 : ℕ) ≤ -106 := by
  have h := uniform106_order_minus_one_reserve heta
  linarith

theorem cubic_uniform106_exponent {eta : ℝ} (heta : 0 < eta) :
    3 - 3 * eta * (s3Uniform106DecayOrder eta - 1 : ℕ) ≤ -106 := by
  have h := uniform106_order_minus_one_reserve heta
  linarith

theorem source_prefactor_le_eight_time_six {N : ℕ} {T : ℝ}
    (hT : 1 ≤ T) (hNle : (N : ℝ) ≤ T) (W : Finset ℝ)
    (hWle : (W.card : ℝ) ≤ 2 * T) :
    (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 ≤ 8 * T ^ 6 := by
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hW0 : 0 ≤ (W.card : ℝ) := Nat.cast_nonneg _
  have hN3 : (N : ℝ) ^ 3 ≤ T ^ 3 :=
    pow_le_pow_left₀ hN0 hNle 3
  have hW3 : (W.card : ℝ) ^ 3 ≤ (2 * T) ^ 3 :=
    pow_le_pow_left₀ hW0 hWle 3
  have hmul := mul_le_mul hN3 hW3 (by positivity) (by positivity)
  calc
    (N : ℝ) ^ 3 * (W.card : ℝ) ^ 3 ≤ T ^ 3 * (2 * T) ^ 3 := hmul
    _ = 8 * T ^ 6 := by ring

theorem source_prefactor_time_neg106_le_eight_time_neg100
    {N : ℕ} {T c : ℝ} (hT : 1 ≤ T) (hNle : (N : ℝ) ≤ T)
    (W : Finset ℝ) (hWle : (W.card : ℝ) ≤ 2 * T) (hc : 0 ≤ c) :
    c * ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3) * Real.rpow T (-106 : ℝ) ≤
      8 * c * Real.rpow T (-100 : ℝ) := by
  have hpref := source_prefactor_le_eight_time_six hT hNle W hWle
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hneg : 0 ≤ Real.rpow T (-106 : ℝ) := Real.rpow_nonneg hT0 _
  have hmul := mul_le_mul_of_nonneg_right hpref hneg
  have hpow : T ^ (6 : ℕ) * Real.rpow T (-106 : ℝ) =
      Real.rpow T (-100 : ℝ) := by
    have hpow6 : T ^ (6 : ℕ) = Real.rpow T (6 : ℝ) :=
      (Real.rpow_natCast T 6).symm
    calc
      T ^ (6 : ℕ) * Real.rpow T (-106 : ℝ) =
          Real.rpow T (6 : ℝ) * Real.rpow T (-106 : ℝ) := by rw [hpow6]
      _ = Real.rpow T ((6 : ℝ) + (-106 : ℝ)) :=
        (Real.rpow_add hTpos (6 : ℝ) (-106 : ℝ)).symm
      _ = Real.rpow T (-100 : ℝ) := by norm_num
  have hscaled := mul_le_mul_of_nonneg_left hmul hc
  calc
    c * ((N : ℝ) ^ 3 * (W.card : ℝ) ^ 3) * Real.rpow T (-106 : ℝ) ≤
        c * (8 * T ^ 6) * Real.rpow T (-106 : ℝ) := by
          simpa only [mul_assoc] using hscaled
    _ = 8 * c * (T ^ 6 * Real.rpow T (-106 : ℝ)) := by ring
    _ = 8 * c * Real.rpow T (-100 : ℝ) := by rw [hpow]

end
end GuthMaynardS3LiteralErrorContract

#print axioms GuthMaynardS3LiteralErrorContract.source_prefactor_le_eight_time_six
#print axioms GuthMaynardS3LiteralErrorContract.source_prefactor_time_neg106_le_eight_time_neg100
#print axioms GuthMaynardS3LiteralErrorContract.uniform106_order_reserve
#print axioms GuthMaynardS3LiteralErrorContract.uniform106_order_minus_one_reserve
#print axioms GuthMaynardS3LiteralErrorContract.radial_uniform106_exponent
#print axioms GuthMaynardS3LiteralErrorContract.fourier_uniform106_exponent
#print axioms GuthMaynardS3LiteralErrorContract.cubic_uniform106_exponent
