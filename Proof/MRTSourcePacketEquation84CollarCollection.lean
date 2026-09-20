import MRTSourcePacketOuterIntersection
import MRTSourcePacketEquation84Bound

/-! Explicit constant collection for the outer-intersection equation-(84) collar. -/

namespace MAPMRTSourcePacketEquation84CollarCollection

open MeasureTheory Set

noncomputable section

/-- The collar version of the two-IBP constant collection.  Here `2 ≤ R ≤ 4`
is exactly `X/4 < H ≤ X/2`; the fixed outer window permits the absolute
amplitude budget `A0 ≤ 600`. -/
theorem equation84_collar_budget_collection
    {D R P A0 A1 A2 K1 K2 : ℝ}
    (hD : 0 < D) (hRLower : 2 ≤ R) (hRUpper : R ≤ 4)
    (hP : P ≤ 2 * R * D) (hP0 : 0 ≤ P)
    (hA0n : 0 ≤ A0) (hA1n : 0 ≤ A1) (hA2n : 0 ≤ A2)
    (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hA0 : A0 ≤ 600) (hA1 : A1 ≤ K1) (hA2 : A2 ≤ R * K2) :
    (1 / (3 * D / 4)) ^ 2 * A2 +
        3 * (1 / (3 * D / 4)) * (P / (3 * D / 4) ^ 2) * A1 +
        ((1 / (3 * D / 4)) *
            (P / (3 * D / 4) ^ 2 + 2 * P ^ 2 / (3 * D / 4) ^ 3) +
          (P / (3 * D / 4) ^ 2) ^ 2) * A0 ≤
      (150000 + 24 * K1 + 4 * K2) * R / D ^ 2 := by
  let d : ℝ := 3 * D / 4
  have hd : 0 < d := by unfold d; positivity
  have hR0 : 0 ≤ R := le_trans (by norm_num) hRLower
  have hq0 : 1 / d ≤ 2 / D := by
    rw [div_le_div_iff₀ hd hD]
    unfold d
    nlinarith
  have hq0n : 0 ≤ 1 / d := by positivity
  have hq1 : P / d ^ 2 ≤ 4 * R / D := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hd) hD]
    have hm := mul_le_mul_of_nonneg_right hP hD.le
    unfold d
    nlinarith [mul_nonneg hR0 (sq_nonneg D)]
  have hq1n : 0 ≤ P / d ^ 2 := by positivity
  have hPsq : P ^ 2 ≤ (2 * R * D) ^ 2 :=
    pow_le_pow_left₀ hP0 hP 2
  have hq2b : 2 * P ^ 2 / d ^ 3 ≤ 19 * R ^ 2 / D := by
    rw [div_le_div_iff₀ (pow_pos hd 3) hD]
    have hm := mul_le_mul_of_nonneg_left hPsq (by norm_num : (0 : ℝ) ≤ 2)
    unfold d
    nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg D)]
  have hRle : R ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hfirst : 4 * R / D ≤ 4 * R ^ 2 / D := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hRle (by norm_num)) hD.le
  have hq2 : P / d ^ 2 + 2 * P ^ 2 / d ^ 3 ≤ 23 * R ^ 2 / D := by
    calc
      P / d ^ 2 + 2 * P ^ 2 / d ^ 3 ≤
          4 * R / D + 19 * R ^ 2 / D := add_le_add hq1 hq2b
      _ ≤ 4 * R ^ 2 / D + 19 * R ^ 2 / D := add_le_add hfirst le_rfl
      _ = 23 * R ^ 2 / D := by ring
  have hq2n : 0 ≤ P / d ^ 2 + 2 * P ^ 2 / d ^ 3 := by positivity
  have ht0 : (1 / d) ^ 2 * A2 ≤ 4 * R * K2 / D ^ 2 := by
    have hs := pow_le_pow_left₀ hq0n hq0 2
    calc
      (1 / d) ^ 2 * A2 ≤ (2 / D) ^ 2 * A2 :=
        mul_le_mul_of_nonneg_right hs hA2n
      _ ≤ (2 / D) ^ 2 * (R * K2) := by gcongr
      _ = 4 * R * K2 / D ^ 2 := by field_simp [ne_of_gt hD]; ring
  have ht1 : 3 * (1 / d) * (P / d ^ 2) * A1 ≤
      24 * R * K1 / D ^ 2 := by
    calc
      3 * (1 / d) * (P / d ^ 2) * A1 ≤
          3 * (2 / D) * (4 * R / D) * K1 := by gcongr
      _ = 24 * R * K1 / D ^ 2 := by field_simp [ne_of_gt hD]; ring
  have hinner : (1 / d) *
          (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) + (P / d ^ 2) ^ 2 ≤
      62 * R ^ 2 / D ^ 2 := by
    calc
      _ ≤ (2 / D) * (23 * R ^ 2 / D) + (4 * R / D) ^ 2 := by
        apply add_le_add
        · exact mul_le_mul hq0 hq2 hq2n (by positivity)
        · exact pow_le_pow_left₀ hq1n hq1 2
      _ = 62 * R ^ 2 / D ^ 2 := by field_simp [ne_of_gt hD]; ring
  have hinnern : 0 ≤ (1 / d) *
          (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) + (P / d ^ 2) ^ 2 := by positivity
  have ht2 : ((1 / d) *
          (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) + (P / d ^ 2) ^ 2) * A0 ≤
      148800 * R / D ^ 2 := by
    calc
      _ ≤ (62 * R ^ 2 / D ^ 2) * 600 :=
        mul_le_mul hinner hA0 hA0n (by positivity)
      _ ≤ (62 * (4 * R) / D ^ 2) * 600 := by
        gcongr
        simpa [pow_two, mul_comm] using mul_le_mul_of_nonneg_left hRUpper hR0
      _ = 148800 * R / D ^ 2 := by ring
  change (1 / d) ^ 2 * A2 +
      3 * (1 / d) * (P / d ^ 2) * A1 +
      ((1 / d) * (P / d ^ 2 + 2 * P ^ 2 / d ^ 3) +
        (P / d ^ 2) ^ 2) * A0 ≤ _
  calc
    _ ≤ 4 * R * K2 / D ^ 2 + 24 * R * K1 / D ^ 2 +
        148800 * R / D ^ 2 := by gcongr
    _ = (148800 + 24 * K1 + 4 * K2) * R / D ^ 2 := by ring
    _ ≤ (150000 + 24 * K1 + 4 * K2) * R / D ^ 2 := by
      gcongr
      linarith

#print axioms equation84_collar_budget_collection

end
end MAPMRTSourcePacketEquation84CollarCollection
