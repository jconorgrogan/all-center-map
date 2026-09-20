import KoukExercise12TwoLocalPolylogScalars
import KoukExercise12TwoLocalHorizontalAperture

/-!
# Principal polynomial envelopes for the split local contour
-/

namespace MAPKoukExercise12TwoPrincipalLocalContourRBounds

open MAPKoukExercise12TwoLocalHorizontalAperture
open MAPKoukExercise12TwoLocalPolylogScalars

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private theorem principalArithmeticLog_le
    (D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X) :
    Real.log ((Real.log X) ^ D + 3) ≤
      ((D : ℝ) + 4) * Real.log X := by
  have harg : 0 < (Real.log X) ^ D + 3 := by positivity
  have hmono : (Real.log X) ^ D + 3 ≤ (Real.log X) ^ D + 8 := by norm_num
  have hbase := contourArithmeticLog_polylogHeight_le
    0 D hlog (q := 1) (by simp)
  have := (Real.log_le_log harg hmono).trans (by
    simpa only [Nat.cast_one, one_mul, Nat.zero_add] using hbase)
  norm_num at this ⊢
  exact this

private theorem principalLocalR_le_of_inv
    (r : ℕ) {L LH d K C : ℝ}
    (hL1 : 1 ≤ L) (hLH0 : 0 ≤ LH) (hLH : LH ≤ K * L)
    (hK : 0 ≤ K) (hC : 0 ≤ C) (hd : 0 < d)
    (hinv : d⁻¹ ≤ C * L ^ r) :
    2 + 20 * (Real.log 223948800 + 6 * LH) +
        30300 * LH + 30300 * LH / d ≤
      (2 + 20 * 223948800 + 30420 * K + 30300 * K * C) *
        L ^ (r + 1) := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL1
  have hpow1 : 1 ≤ L ^ (r + 1) := one_le_pow₀ hL1
  have hLpow : L ≤ L ^ (r + 1) := by
    calc L = L ^ 1 := by simp
         _ ≤ L ^ (r + 1) := pow_le_pow_right₀ hL1 (by omega)
  have hinv0 : 0 ≤ d⁻¹ := inv_nonneg.mpr hd.le
  have hdiv : LH / d ≤ K * C * L ^ (r + 1) := by
    rw [div_eq_mul_inv]
    calc
      LH * d⁻¹ ≤ (K * L) * (C * L ^ r) :=
        mul_le_mul hLH hinv hinv0 (mul_nonneg hK hL0)
      _ = K * C * L ^ (r + 1) := by rw [pow_succ]; ring
  have hconst : Real.log 223948800 ≤ 223948800 :=
    (Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < 223948800)).trans (by norm_num)
  have hLHpow : LH ≤ K * L ^ (r + 1) :=
    hLH.trans (mul_le_mul_of_nonneg_left hLpow hK)
  have hdivScaled : 30300 * LH / d ≤
      30300 * (K * C * L ^ (r + 1)) := by
    calc
      30300 * LH / d = 30300 * (LH / d) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (by norm_num)
  nlinarith

theorem realContourR_le
    (D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X) :
    let K := (D : ℝ) + 4
    let C := (40000016 : ℝ)
    let d := exerciseRealClearance
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
    let LH := Real.log ((Real.log X) ^ D + 3)
    2 + 20 * (Real.log 223948800 + 6 * LH) +
        30300 * LH + 30300 * LH / d ≤
      (2 + 20 * 223948800 + 30420 * K + 30300 * K * C) *
        (Real.log X) ^ (3 * D + 1) := by
  dsimp only
  apply principalLocalR_le_of_inv (3 * D)
  · linarith
  · exact Real.log_nonneg (by
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      linarith)
  · exact principalArithmeticLog_le D hlog
  · positivity
  · norm_num
  · exact exerciseRealClearance_pos
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
  · simpa only [Nat.zero_add] using
      inv_exerciseRealClearance_polylogHeight_le 0 D hlog
        (1 : DirichletCharacter ℂ 1)
        (by
          show (1 : DirichletCharacter ℂ 1).conductor = 1
          rw [DirichletCharacter.conductor_one]) (by simp)

theorem horizontalContourR_le
    (D : ℕ) {X : ℝ} (hlog : 2 ≤ Real.log X) :
    let K := (D : ℝ) + 4
    let C := 121204 * K
    let d := exerciseHorizontalClearance
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
    let LH := Real.log ((Real.log X) ^ D + 3)
    2 + 20 * (Real.log 223948800 + 6 * LH) +
        30300 * LH + 30300 * LH / d ≤
      (2 + 20 * 223948800 + 30420 * K + 30300 * K * C) *
        (Real.log X) ^ 2 := by
  dsimp only
  apply principalLocalR_le_of_inv 1
  · linarith
  · exact Real.log_nonneg (by
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      linarith)
  · exact principalArithmeticLog_le D hlog
  · positivity
  · positivity
  · exact exerciseHorizontalClearance_pos
      (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
  · have hinv := inv_exerciseHorizontalClearance_le_principal
      (show 0 ≤ (Real.log X) ^ D by positivity)
    have hlog8 := contourArithmeticLog_polylogHeight_le
      0 D hlog (q := 1) (by simp)
    have hlog8' : Real.log ((Real.log X) ^ D + 8) ≤
        ((D : ℝ) + 4) * Real.log X := by
      simpa only [Nat.cast_one, one_mul, Nat.zero_add] using hlog8
    exact hinv.trans (by
      have := mul_le_mul_of_nonneg_left hlog8' (by norm_num : (0 : ℝ) ≤ 121204)
      simpa [mul_assoc, mul_left_comm, mul_comm] using this)

theorem cornerContourR_le
    (D : ℕ) (hD : 1 ≤ D) {X : ℝ} (hlog : 2 ≤ Real.log X) :
    let K := (D : ℝ) + 4
    let C := 40000016 + 121204 * K
    let d := min
      (exerciseRealClearance (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D))
      (exerciseHorizontalClearance (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D))
    let LH := Real.log ((Real.log X) ^ D + 3)
    2 + 20 * (Real.log 223948800 + 6 * LH) +
        30300 * LH + 30300 * LH / d ≤
      (2 + 20 * 223948800 + 30420 * K + 30300 * K * C) *
        (Real.log X) ^ (3 * D + 1) := by
  let dR := exerciseRealClearance
    (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
  let dH := exerciseHorizontalClearance
    (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D)
  have hR : dR⁻¹ ≤ 40000016 * (Real.log X) ^ (3 * D) := by
    dsimp only [dR]
    simpa only [Nat.zero_add] using
      inv_exerciseRealClearance_polylogHeight_le 0 D hlog
        (1 : DirichletCharacter ℂ 1)
        (by
          show (1 : DirichletCharacter ℂ 1).conductor = 1
          rw [DirichletCharacter.conductor_one]) (by simp)
  have hHraw := inv_exerciseHorizontalClearance_le_principal
    (show 0 ≤ (Real.log X) ^ D by positivity)
  have hlog8 := contourArithmeticLog_polylogHeight_le
    0 D hlog (q := 1) (by simp)
  have hlog8' : Real.log ((Real.log X) ^ D + 8) ≤
      ((D : ℝ) + 4) * Real.log X := by
    simpa only [Nat.cast_one, one_mul, Nat.zero_add] using hlog8
  have hHlin : dH⁻¹ ≤
      (121204 * ((D : ℝ) + 4)) * Real.log X := by
    exact hHraw.trans (by
      have := mul_le_mul_of_nonneg_left hlog8'
        (by norm_num : (0 : ℝ) ≤ 121204)
      simpa only [dH, mul_assoc] using this)
  have hLpow : Real.log X ≤ (Real.log X) ^ (3 * D) := by
    calc
      Real.log X = (Real.log X) ^ 1 := by simp
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by omega)
  have hH : dH⁻¹ ≤
      (121204 * ((D : ℝ) + 4)) * (Real.log X) ^ (3 * D) :=
    hHlin.trans (mul_le_mul_of_nonneg_left hLpow (by positivity))
  have hmin : (min dR dH)⁻¹ ≤
      (40000016 + 121204 * ((D : ℝ) + 4)) *
        (Real.log X) ^ (3 * D) := by
    rcases le_total dR dH with h | h
    · rw [min_eq_left h]
      have hp : 0 ≤ (Real.log X) ^ (3 * D) := by positivity
      nlinarith
    · rw [min_eq_right h]
      have hp : 0 ≤ (Real.log X) ^ (3 * D) := by positivity
      nlinarith
  dsimp only
  apply principalLocalR_le_of_inv (3 * D)
  · linarith
  · exact Real.log_nonneg (by
      have hH1 : 1 ≤ (Real.log X) ^ D := one_le_pow₀ (by linarith)
      linarith)
  · exact principalArithmeticLog_le D hlog
  · positivity
  · positivity
  · exact lt_min (exerciseRealClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D))
      (exerciseHorizontalClearance_pos
        (1 : DirichletCharacter ℂ 1) ((Real.log X) ^ D))
  · simpa only [dR, dH] using hmin

end
end MAPKoukExercise12TwoPrincipalLocalContourRBounds

#print axioms MAPKoukExercise12TwoPrincipalLocalContourRBounds.realContourR_le
#print axioms MAPKoukExercise12TwoPrincipalLocalContourRBounds.horizontalContourR_le
#print axioms MAPKoukExercise12TwoPrincipalLocalContourRBounds.cornerContourR_le
