import GuthMaynardEnergyGeometry

open scoped Real

noncomputable section
namespace GuthMaynardEnergy119LogAbsorption

/-! The logarithm is bounded after the natural-number parameter is restricted
by the actual horizon.  The `max 1` keeps the `N = 0` edge literal. -/
theorem exists_log_absorption :
    ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 < C ∧
        ∀ (N : ℕ) (T : ℝ), 1 ≤ T → (N : ℝ) ≤ 2 * T →
          1 + Real.log (max 1 (2 * (N : ℝ))) ≤
            C * Real.rpow T delta := by
  intro delta hdelta
  let C : ℝ := 1 + Real.log 4 + 1 / delta
  have hC : 0 < C := by
    dsimp [C]
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine ⟨C, hC, ?_⟩
  intro N T hT hN
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : 1 ≤ Real.rpow T delta := Real.one_le_rpow hT hdelta.le
  have hmaxle : max 1 (2 * (N : ℝ)) ≤ 4 * T := by
    apply max_le
    · linarith
    · nlinarith
  have hlogmax : Real.log (max 1 (2 * (N : ℝ))) ≤ Real.log (4 * T) := by
    apply Real.log_le_log
    · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    · exact hmaxle
  have hlogT := Real.log_le_rpow_div (show 0 ≤ T by linarith) hdelta
  change Real.log T ≤ Real.rpow T delta / delta at hlogT
  have hlogmul : Real.log (4 * T) = Real.log 4 + Real.log T := by
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hTpos.ne']
  calc
    1 + Real.log (max 1 (2 * (N : ℝ))) ≤
        1 + Real.log (4 * T) := by linarith
    _ = 1 + Real.log 4 + Real.log T := by rw [hlogmul]; ring
    _ ≤ 1 + Real.log 4 + Real.rpow T delta / delta := by linarith
    _ ≤ C * Real.rpow T delta := by
      dsimp [C]
      have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      have hdiv : 0 ≤ 1 / delta := by positivity
      have hmul := mul_le_mul_of_nonneg_left hpow hdiv
      have hconst : 1 + Real.log 4 ≤
          (1 + Real.log 4) * Real.rpow T delta := by
        have := mul_le_mul_of_nonneg_right hpow
          (by positivity : 0 ≤ 1 + Real.log (4 : ℝ))
        simpa [one_mul, mul_comm] using this
      calc
        1 + Real.log 4 + Real.rpow T delta / delta =
            (1 + Real.log 4) + (1 / delta) * Real.rpow T delta := by
          ring
        _ ≤ (1 + Real.log 4) * Real.rpow T delta +
              (1 / delta) * Real.rpow T delta :=
          add_le_add hconst (le_refl _)
        _ = (1 + Real.log 4 + 1 / delta) * Real.rpow T delta := by ring

end GuthMaynardEnergy119LogAbsorption

#print axioms GuthMaynardEnergy119LogAbsorption.exists_log_absorption
