import KoukExercise12TwoPolylogScalars
import KoukExercise12TwoLocalHorizontalAperture

/-!
# Local-contour scalar costs at polylogarithmic height

The pointwise Exercise 12.2(a) contour uses separate real and horizontal
clearances.  This file records the polynomial envelopes needed by the
Siegel--Walfisz collapse without changing the older global-clearance API.
 -/

namespace MAPKoukExercise12TwoLocalPolylogScalars

open MAPKoukExercise12TwoPolylogScalars
open MAPKoukExercise12TwoLocalHorizontalAperture

noncomputable section

theorem inv_exerciseRealClearance_polylogHeight_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (exerciseRealClearance chi ((Real.log X) ^ D))⁻¹ ≤
      40000016 * (Real.log X) ^ (B + 3 * D) := by
  have hcount := dirichletZeroCount_polylogHeight_le B D hlog chi hprim hq
  have hinv := inv_exerciseRealClearance_le_count chi ((Real.log X) ^ D)
  have hpow : 1 ≤ (Real.log X) ^ (B + 3 * D) :=
    one_le_pow₀ (by linarith : 1 ≤ Real.log X)
  calc
    _ ≤ 8 * ((DirichletZeros.dirichletZeroCount chi 0
          ((Real.log X) ^ D + 4) : ℝ) + 2) := hinv
    _ ≤ 8 * (5000000 * (Real.log X) ^ (B + 3 * D) + 2) := by gcongr
    _ ≤ 40000016 * (Real.log X) ^ (B + 3 * D) := by nlinarith

theorem contourArithmeticLog_polylogHeight_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q]
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    Real.log ((q : ℝ) * ((Real.log X) ^ D + 8)) ≤
      (((B + D : ℕ) : ℝ) + 4) * Real.log X := by
  let L := Real.log X
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hH1 : 1 ≤ L ^ D := one_le_pow₀ hL1
  have hscalePos : 0 < (q : ℝ) * (L ^ D + 8) := by
    have hq0 : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    positivity
  have hscale : (q : ℝ) * (L ^ D + 8) ≤ 9 * L ^ (B + D) := by
    have hqL : (q : ℝ) ≤ L ^ B := by simpa only [L] using hq
    calc
      _ ≤ L ^ B * (9 * L ^ D) := by
        apply mul_le_mul hqL (by nlinarith) (by positivity) (pow_nonneg hL0 B)
      _ = 9 * L ^ (B + D) := by rw [pow_add]; ring
  calc
    Real.log ((q : ℝ) * ((Real.log X) ^ D + 8)) =
        Real.log ((q : ℝ) * (L ^ D + 8)) := by rfl
    _ ≤ Real.log (9 * L ^ (B + D)) := Real.log_le_log hscalePos hscale
    _ = Real.log 9 + ((B + D : ℕ) : ℝ) * Real.log L := by
      rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0)
        (pow_pos (zero_lt_one.trans_le hL1) _).ne', Real.log_pow]
    _ ≤ (((B + D : ℕ) : ℝ) + 4) * L := by
      have hlogL := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hL1)
      have hlog9 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 9)
      have hBD0 : (0 : ℝ) ≤ ((B + D : ℕ) : ℝ) := by positivity
      nlinarith
    _ = _ := by rfl

theorem inv_exerciseHorizontalClearance_polylogHeight_le
    (B D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (exerciseHorizontalClearance chi ((Real.log X) ^ D))⁻¹ ≤
      (28 * (1 + 306 * (((B + D : ℕ) : ℝ) + 4))) * Real.log X := by
  have hH0 : 0 ≤ (Real.log X) ^ D := pow_nonneg (by linarith) D
  have hinv := inv_exerciseHorizontalClearance_le_uniform chi hprim hchi hH0
  have hlogScale := contourArithmeticLog_polylogHeight_le B D hlog hq
  have hL1 : 1 ≤ Real.log X := by linarith
  calc
    _ ≤ 28 * (1 + 306 * Real.log ((q : ℝ) * ((Real.log X) ^ D + 8))) := hinv
    _ ≤ 28 * (1 + 306 * ((((B + D : ℕ) : ℝ) + 4) * Real.log X)) := by gcongr
    _ ≤ (28 * (1 + 306 * (((B + D : ℕ) : ℝ) + 4))) * Real.log X := by
      have hcoef : 0 ≤ 306 * (((B + D : ℕ) : ℝ) + 4) := by positivity
      nlinarith

theorem inv_exerciseCornerClearance_polylogHeight_le
    (B D : ℕ) (hD : 1 ≤ D) {X : ℝ} (hlog : 2 ≤ Real.log X)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    (hq : (q : ℝ) ≤ (Real.log X) ^ B) :
    (min (exerciseRealClearance chi ((Real.log X) ^ D))
      (exerciseHorizontalClearance chi ((Real.log X) ^ D)))⁻¹ ≤
      (40000016 + 28 * (1 + 306 * (((B + D : ℕ) : ℝ) + 4))) *
        (Real.log X) ^ (B + 3 * D) := by
  let dR := exerciseRealClearance chi ((Real.log X) ^ D)
  let dH := exerciseHorizontalClearance chi ((Real.log X) ^ D)
  have hR := inv_exerciseRealClearance_polylogHeight_le B D hlog chi hprim hq
  have hI := inv_exerciseHorizontalClearance_polylogHeight_le B D hlog chi hprim hchi hq
  have hL1 : 1 ≤ Real.log X := by linarith
  have hexp : 1 ≤ B + 3 * D := by omega
  have hLpow : Real.log X ≤ (Real.log X) ^ (B + 3 * D) := by
    calc
      Real.log X = (Real.log X) ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ hL1 hexp
  have hI' : dH⁻¹ ≤
      (28 * (1 + 306 * (((B + D : ℕ) : ℝ) + 4))) *
        (Real.log X) ^ (B + 3 * D) := by
    dsimp [dH]
    exact hI.trans (mul_le_mul_of_nonneg_left hLpow (by positivity))
  dsimp [dR, dH] at hR hI' ⊢
  rcases le_total (exerciseRealClearance chi ((Real.log X) ^ D))
    (exerciseHorizontalClearance chi ((Real.log X) ^ D)) with h | h
  · rw [min_eq_left h]
    exact hR.trans (by
      have hp : 0 ≤ (Real.log X) ^ (B + 3 * D) := by positivity
      nlinarith)
  · rw [min_eq_right h]
    exact hI'.trans (by
      have hp : 0 ≤ (Real.log X) ^ (B + 3 * D) := by positivity
      nlinarith)

end
end MAPKoukExercise12TwoLocalPolylogScalars

#print axioms MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseRealClearance_polylogHeight_le
#print axioms MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseHorizontalClearance_polylogHeight_le
#print axioms MAPKoukExercise12TwoLocalPolylogScalars.inv_exerciseCornerClearance_polylogHeight_le
