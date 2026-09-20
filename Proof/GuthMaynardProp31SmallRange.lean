import GuthMaynardProp31ValueExponent

noncomputable section
namespace GuthMaynardProp31SmallRange

/-- The target factor is at least one throughout the full legal value range. -/
theorem target_factor_one_le {N V : ℝ} (hN : 1 ≤ N) (hV : 0 < V)
    (hhigh : V ≤ N ^ (8 / 10 : ℝ)) :
    1 ≤ N ^ (6 / 5 : ℝ) * N ^ (12 / 5 : ℝ) / V ^ 4 := by
  have hN0 : 0 ≤ N := le_trans zero_le_one hN
  have hV4 : V ^ 4 ≤ N ^ (16 / 5 : ℝ) := by
    calc
      V ^ 4 ≤ (N ^ (8 / 10 : ℝ)) ^ 4 := pow_le_pow_left₀ hV.le hhigh 4
      _ = N ^ (16 / 5 : ℝ) := by
        rw [← Real.rpow_mul_natCast hN0]
        norm_num
  apply (le_div_iff₀ (pow_pos hV 4)).2
  calc
    1 * V ^ 4 = V ^ 4 := one_mul _
    _ ≤ N ^ (16 / 5 : ℝ) := hV4
    _ ≤ N ^ (18 / 5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = N ^ (6 / 5 : ℝ) * N ^ (12 / 5 : ℝ) := by
      rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hN)]
      norm_num

/-- A uniform finite-range cap needs no analytic large-value estimate. -/
theorem small_range_cardinality {N M V R eps : ℝ}
    (hN : 1 ≤ N) (hNM : N ≤ M) (hV : 0 < V)
    (hhigh : V ≤ N ^ (8 / 10 : ℝ)) (heps : 0 ≤ eps)
    (hR : R ≤ 2 * N ^ (6 / 5 : ℝ)) :
    R ≤ (2 * M ^ (6 / 5 : ℝ)) * (N ^ (6 / 5 : ℝ)) ^ eps *
      (N ^ (6 / 5 : ℝ) * N ^ (12 / 5 : ℝ) / V ^ 4) := by
  have hM : 1 ≤ M := hN.trans hNM
  have hT : 1 ≤ N ^ (6 / 5 : ℝ) := Real.one_le_rpow hN (by norm_num)
  have hpow : 1 ≤ (N ^ (6 / 5 : ℝ)) ^ eps := Real.one_le_rpow hT heps
  have htarget := target_factor_one_le hN hV hhigh
  have hC : 0 ≤ 2 * M ^ (6 / 5 : ℝ) := by positivity
  calc
    R ≤ 2 * N ^ (6 / 5 : ℝ) := hR
    _ ≤ 2 * M ^ (6 / 5 : ℝ) := by
      gcongr
    _ ≤ (2 * M ^ (6 / 5 : ℝ)) * (N ^ (6 / 5 : ℝ)) ^ eps :=
      le_mul_of_one_le_right hC hpow
    _ ≤ _ := le_mul_of_one_le_right (by positivity) htarget

end GuthMaynardProp31SmallRange
#print axioms GuthMaynardProp31SmallRange.target_factor_one_le
#print axioms GuthMaynardProp31SmallRange.small_range_cardinality
