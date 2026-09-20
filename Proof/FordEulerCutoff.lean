import Mathlib

open scoped BigOperators
noncomputable section
namespace FordEulerCutoff

def cutoffM (t : ℝ) : ℕ := Nat.floor (t ^ 2)

def cutoffR (t : ℝ) : ℕ := Nat.ceil (2 * Real.log t / Real.log 2)

theorem cutoff_properties {t : ℝ} (ht : 2 ≤ t) :
    let M := cutoffM t
    let r := cutoffR t
    1 ≤ M ∧ t ^ 2 / 2 ≤ (M : ℝ) ∧ (M : ℝ) ≤ t ^ 2 ∧
      (M : ℕ) ≤ 2 ^ r ∧ (r : ℝ) ≤ 6 * Real.log t ∧
      ∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        t ^ 2 / 2 ≤ (M : ℝ) + u ∧ (M : ℝ) + u ≤ t ^ 2 + 1 := by
  dsimp [cutoffM, cutoffR]
  let M : ℕ := Nat.floor (t ^ 2)
  let x : ℝ := 2 * Real.log t / Real.log 2
  let r : ℕ := Nat.ceil x
  have htpos : 0 < t := by linarith
  have ht2 : 4 ≤ t ^ 2 := by nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hMfloor : (M : ℝ) ≤ t ^ 2 := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hMfloor_lower : t ^ 2 < (M : ℝ) + 1 := by
    dsimp [M]
    exact Nat.lt_floor_add_one (t ^ 2)
  have hMhalf : t ^ 2 / 2 ≤ (M : ℝ) := by
    nlinarith [hMfloor_lower, ht2]
  have hMone : 1 ≤ M := by
    have : (1 : ℝ) ≤ (M : ℝ) := by nlinarith [hMhalf]
    exact_mod_cast this
  have hxceil : x ≤ (r : ℝ) := by
    dsimp [r]
    exact Nat.le_ceil _
  have hrceil : (r : ℝ) < x + 1 := by
    dsimp [r]
    exact Nat.ceil_lt_add_one hx.le
  have htwo_rpow : (2 : ℝ) ^ x = t ^ 2 := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [x]
    have hlog : Real.log 2 * (2 * Real.log t / Real.log 2) =
        2 * Real.log t := by
      field_simp
    rw [hlog, ← Real.exp_log htpos]
    rw [Real.log_exp]
    rw [← Real.exp_nat_mul]
    congr 1
  have htwo_rpow_le : (2 : ℝ) ^ x ≤ (2 : ℝ) ^ (r : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hxceil
  have hMr : M ≤ 2 ^ r := by
    have hreal : (M : ℝ) ≤ (2 : ℝ) ^ (r : ℝ) := by
      calc
        (M : ℝ) ≤ t ^ 2 := hMfloor
        _ = (2 : ℝ) ^ x := htwo_rpow.symm
        _ ≤ (2 : ℝ) ^ (r : ℝ) := htwo_rpow_le
    have hreal' : (M : ℝ) ≤ ((2 ^ r : ℕ) : ℝ) := by
      simpa [Real.rpow_natCast] using hreal
    exact_mod_cast hreal'
  have hlog2_d6 : (3 : ℝ) / 5 < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlogt_lower : Real.log 2 ≤ Real.log t := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hr6 : (r : ℝ) ≤ 6 * Real.log t := by
    have hratio : 2 * Real.log t / Real.log 2 ≤ (10 / 3 : ℝ) * Real.log t := by
      apply (div_le_iff₀ hlog2).2
      nlinarith
    have hone : (1 : ℝ) ≤ (5 / 3 : ℝ) * Real.log t := by
      nlinarith [hlogt_lower, hlog2_d6]
    have hsum : x + 1 ≤ 6 * Real.log t := by
      dsimp [x]
      nlinarith [hratio, hone]
    exact (le_of_lt hrceil).trans hsum
  refine ⟨hMone, hMhalf, hMfloor, hMr, hr6, ?_⟩
  intro u hu hu1
  constructor
  · exact hMhalf.trans (by linarith)
  · exact add_le_add hMfloor hu1

end FordEulerCutoff

#print axioms FordEulerCutoff.cutoff_properties
