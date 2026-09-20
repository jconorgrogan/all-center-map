import FordScaledDiskGrowth
import FordEulerCenterLower

noncomputable section
namespace FordScaledDiskLogBudget
open FordScaledDiskGrowth FordGrowthWidth FordAllLambdaOffsetBound

theorem disk_log_budget :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ), 3 ≤ t →
        (∀ z ∈ Metric.closedBall (diskCenter t) (6 * diskScale t),
          ‖DirichletCharacter.LFunction χ z‖ ≤
            (N : ℝ) * ((N : ℝ) ^ 2 + C * Real.log (t + 3))) ∧
        Real.log (((N : ℝ) * ((N : ℝ) ^ 2 + C * Real.log (t + 3))) /
          ‖DirichletCharacter.LFunction χ (diskCenter t)‖) ≤
          D + 3 * Real.log (N : ℝ) + 2 * Real.log (Real.log (t + 3)) := by
  obtain ⟨C, hC, hg⟩ := scaled_disk_growth
  let A : ℝ := 32 * (1 + C) / savingCoeff
  have hc : 0 < savingCoeff := savingCoeff_pos
  have hcs : savingCoeff ≤ (1 / 10000000000 : ℝ) := min_le_right _ _
  have hA1 : 1 < A := by
    dsimp [A]
    apply (lt_div_iff₀ hc).2
    nlinarith
  let D : ℝ := Real.log A + 1
  have hD : 0 < D := by dsimp [D]; linarith [Real.log_pos hA1]
  refine ⟨C, D, hC, hD, ?_⟩
  intro N hN χ t ht
  refine ⟨hg N χ t ht, ?_⟩
  let T : ℝ := Real.log (t + 3)
  have hT : 1 ≤ T := (disk_geometry ht).1
  have hTp : 0 < T := by linarith
  have hNp : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (NeZero.one_le : 1 ≤ N)
  have ha := (disk_geometry ht).2.1
  have hah := (disk_geometry ht).2.2.1
  have hlower := FordEulerCenterLower.norm_LFunction_one_add_delta_lower χ ha
    (show diskScale t ≤ 1 by linarith) (t := t)
  change diskScale t / 2 ≤ ‖DirichletCharacter.LFunction χ (diskCenter t)‖ at hlower
  have hpow : T ^ (-1 : ℝ) ≤ T ^ (-(9 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  have hlower' : savingCoeff / (32 * T) ≤
      ‖DirichletCharacter.LFunction χ (diskCenter t)‖ := by
    calc
      savingCoeff / (32 * T) = savingCoeff * T ^ (-1 : ℝ) / 32 := by
        rw [Real.rpow_neg_one]
        ring
      _ ≤ savingCoeff * T ^ (-(9 / 10 : ℝ)) / 32 := by gcongr
      _ = diskScale t / 2 := by dsimp [diskScale, widthEta, T]; ring
      _ ≤ _ := hlower
  have hlp : 0 < ‖DirichletCharacter.LFunction χ (diskCenter t)‖ :=
    lt_of_lt_of_le (by positivity) hlower'
  let G : ℝ := (N : ℝ) * ((N : ℝ) ^ 2 + C * T)
  have hGp : 0 < G := by dsimp [G]; positivity
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
  have hG : G ≤ (1 + C) * (N : ℝ) ^ 3 * T := by
    have h1 := mul_le_mul_of_nonneg_left hT (sq_nonneg (N : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hN2 (show 0 ≤ C * T by positivity)
    have hinner : (N : ℝ) ^ 2 + C * T ≤ (1 + C) * (N : ℝ) ^ 2 * T := by
      nlinarith
    have hm := mul_le_mul_of_nonneg_left hinner hNp.le
    dsimp [G]
    nlinarith
  have hratio : G / ‖DirichletCharacter.LFunction χ (diskCenter t)‖ ≤
      A * (N : ℝ) ^ 3 * T ^ 2 := by
    calc
      _ ≤ G / (savingCoeff / (32 * T)) :=
        div_le_div_of_nonneg_left hGp.le (by positivity) hlower'
      _ ≤ ((1 + C) * (N : ℝ) ^ 3 * T) / (savingCoeff / (32 * T)) :=
        div_le_div_of_nonneg_right hG (by positivity)
      _ = A * (N : ℝ) ^ 3 * T ^ 2 := by dsimp [A]; field_simp
  have hlog := Real.log_le_log (div_pos hGp hlp) hratio
  rw [Real.log_mul (by positivity : A * (N : ℝ) ^ 3 ≠ 0) (by positivity : T ^ 2 ≠ 0),
    Real.log_mul (by positivity : A ≠ 0) (by positivity : (N : ℝ) ^ 3 ≠ 0),
    Real.log_pow, Real.log_pow] at hlog
  change Real.log (G / ‖DirichletCharacter.LFunction χ (diskCenter t)‖) ≤
    D + 3 * Real.log (N : ℝ) + 2 * Real.log T
  dsimp [D]
  norm_num at hlog
  linarith

end FordScaledDiskLogBudget
#print axioms FordScaledDiskLogBudget.disk_log_budget
