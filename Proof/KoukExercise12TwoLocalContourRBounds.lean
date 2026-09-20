import KoukExercise12TwoLocalPolylogScalars

/-!
# Polynomial envelopes for the split local contour

The real/corner clearance may cost the full zero count, but those terms carry
a power saving in `X`.  The high horizontal clearance costs only one logarithm,
which preserves the decisive inverse-height saving.
-/

namespace MAPKoukExercise12TwoLocalContourRBounds

open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPKoukExercise12TwoLocalPolylogScalars

noncomputable section

private theorem localArithmeticLog_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    Real.log ((q : ℝ) * ((Real.log X) ^ D + 3)) ≤
      (((B + D : ℕ) : ℝ) + 4) * Real.log X := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hH0 : 0 ≤ (Real.log X) ^ D := pow_nonneg (by linarith) D
  have harg3 : 0 < (q : ℝ) * ((Real.log X) ^ D + 3) := by positivity
  have hscale : (q : ℝ) * ((Real.log X) ^ D + 3) ≤
      (q : ℝ) * ((Real.log X) ^ D + 8) := by gcongr <;> norm_num
  exact (Real.log_le_log harg3 hscale).trans
    (contourArithmeticLog_polylogHeight_le B D hlog hq)

private theorem localR_le_of_inv
    (r : ℕ) {L LH d K C : ℝ}
    (hL1 : 1 ≤ L) (hLH0 : 0 ≤ LH) (hLH : LH ≤ K * L)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hd : 0 < d)
    (hinv : d⁻¹ ≤ C * L ^ r) :
    20 * (Real.log 21600 + 2 * LH) + 5520 * LH + 5520 * LH / d ≤
      (20 * 21599 + 5560 * K + 5520 * K * C) * L ^ (r + 1) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hpow1 : 1 ≤ L ^ (r + 1) := one_le_pow₀ hL1
  have hLpow : L ≤ L ^ (r + 1) := by
    calc
      L = L ^ 1 := by simp
      _ ≤ L ^ (r + 1) := pow_le_pow_right₀ hL1 (by omega)
  have hinv0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hdiv : LH / d ≤ K * C * L ^ (r + 1) := by
    rw [div_eq_mul_inv]
    calc
      LH * d⁻¹ ≤ (K * L) * (C * L ^ r) :=
        mul_le_mul hLH hinv hinv0 (mul_nonneg hK hL0)
      _ = K * C * L ^ (r + 1) := by rw [pow_succ]; ring
  have hconst : Real.log 21600 ≤ 21599 := by
    convert Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < 21600 by norm_num) using 1 <;> norm_num
  have hLHpow : LH ≤ K * L ^ (r + 1) :=
    hLH.trans (mul_le_mul_of_nonneg_left hLpow hK)
  have hconstPow : Real.log 21600 ≤ 21599 * L ^ (r + 1) :=
    hconst.trans (by nlinarith [hpow1])
  calc
    20 * (Real.log 21600 + 2 * LH) + 5520 * LH + 5520 * LH / d ≤
        20 * (21599 * L ^ (r + 1) + 2 * (K * L ^ (r + 1))) +
          5520 * (K * L ^ (r + 1)) +
          5520 * (K * C * L ^ (r + 1)) := by
      gcongr
      calc
        5520 * LH / d = 5520 * (LH / d) := by ring
        _ ≤ 5520 * (K * C * L ^ (r + 1)) :=
          mul_le_mul_of_nonneg_left hdiv (show (0 : ℝ) ≤ 5520 by norm_num)
    _ = (20 * 21599 + 5560 * K + 5520 * K * C) * L ^ (r + 1) := by ring

/-- Real vertical-side logarithmic derivative envelope. -/
theorem realContourR_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    let K := (((B + D : ℕ) : ℝ) + 4)
    let C := (40000016 : ℝ)
    let d := exerciseRealClearance chi ((Real.log X) ^ D)
    let LH := Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))
    20 * (Real.log 21600 + 2 * LH) + 5520 * LH + 5520 * LH / d ≤
      (20 * 21599 + 5560 * K + 5520 * K * C) *
        (Real.log X) ^ (B + 3 * D + 1) := by
  dsimp only
  apply localR_le_of_inv (B + 3 * D)
  · linarith
  · exact Real.log_nonneg (by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      nlinarith)
  · exact localArithmeticLog_le B D hlog hq
  · positivity
  · norm_num
  · exact exerciseRealClearance_pos chi ((Real.log X) ^ D)
  · exact inv_exerciseRealClearance_polylogHeight_le B D hlog chi hprim hq

/-- High horizontal-side logarithmic derivative envelope. -/
theorem horizontalContourR_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    let K := (((B + D : ℕ) : ℝ) + 4)
    let C := 28 * (1 + 306 * K)
    let d := exerciseHorizontalClearance chi ((Real.log X) ^ D)
    let LH := Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))
    20 * (Real.log 21600 + 2 * LH) + 5520 * LH + 5520 * LH / d ≤
      (20 * 21599 + 5560 * K + 5520 * K * C) *
        (Real.log X) ^ 2 := by
  dsimp only
  apply localR_le_of_inv 1
  · linarith
  · exact Real.log_nonneg (by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      nlinarith)
  · exact localArithmeticLog_le B D hlog hq
  · positivity
  · positivity
  · exact exerciseHorizontalClearance_pos chi ((Real.log X) ^ D)
  · exact inv_exerciseHorizontalClearance_polylogHeight_le
      B D hlog chi hprim hchi hq |>.trans_eq (by simp)

/-- Lower horizontal corner envelope, where both clearances are required. -/
theorem cornerContourR_le
    (B D : ℕ) (hD : 1 ≤ D) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    let K := (((B + D : ℕ) : ℝ) + 4)
    let C := 40000016 + 28 * (1 + 306 * K)
    let d := min (exerciseRealClearance chi ((Real.log X) ^ D))
      (exerciseHorizontalClearance chi ((Real.log X) ^ D))
    let LH := Real.log ((q : ℝ) * ((Real.log X) ^ D + 3))
    20 * (Real.log 21600 + 2 * LH) + 5520 * LH + 5520 * LH / d ≤
      (20 * 21599 + 5560 * K + 5520 * K * C) *
        (Real.log X) ^ (B + 3 * D + 1) := by
  dsimp only
  apply localR_le_of_inv (B + 3 * D)
  · linarith
  · exact Real.log_nonneg (by
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.one_le (n := q)
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      nlinarith)
  · exact localArithmeticLog_le B D hlog hq
  · positivity
  · positivity
  · exact lt_min (exerciseRealClearance_pos chi ((Real.log X) ^ D))
      (exerciseHorizontalClearance_pos chi ((Real.log X) ^ D))
  · exact inv_exerciseCornerClearance_polylogHeight_le
      B D hD hlog chi hprim hchi hq

end
end MAPKoukExercise12TwoLocalContourRBounds

#print axioms MAPKoukExercise12TwoLocalContourRBounds.realContourR_le
#print axioms MAPKoukExercise12TwoLocalContourRBounds.horizontalContourR_le
#print axioms MAPKoukExercise12TwoLocalContourRBounds.cornerContourR_le
