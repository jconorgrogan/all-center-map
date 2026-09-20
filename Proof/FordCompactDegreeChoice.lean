import FordCompactDifferenceScales

noncomputable section
namespace FordCompactDegreeChoice
open FordCompactDifferenceScales

theorem compact_degree_choice {lam : ℝ} (hlow : 1 ≤ lam)
    (hhi : lam ≤ (6492 : ℝ) / 5) :
    let r := Nat.floor lam + 1
    2 ≤ r ∧ r ≤ 1299 ∧
      (r : ℝ) - 1 ≤ lam ∧ lam ≤ r ∧
      0 < cutoffExponent r ∧
      cutoffExponent r ≤ shiftExponent r lam ∧
      shiftExponent r lam ≤ 3 / 4 ∧
      lam + (r : ℝ) * shiftExponent r lam - (r + 1) = -(1 / 2) ∧
      lam + (r : ℝ) * (shiftExponent r lam - cutoffExponent r) -
        (r + 1) = -(3 / 4) := by
  let r := Nat.floor lam + 1
  have hlam0 : 0 ≤ lam := by linarith
  have hflo : (Nat.floor lam : ℝ) ≤ lam := Nat.floor_le hlam0
  have hflo_low : 1 ≤ Nat.floor lam :=
    (Nat.le_floor_iff hlam0).mpr (by exact_mod_cast hlow)
  have hflo_hi : Nat.floor lam < 1299 := by
    apply (Nat.floor_lt hlam0).mpr
    norm_num at hhi ⊢
    linarith
  have hr2 : 2 ≤ r := by dsimp [r]; omega
  have hr1299 : r ≤ 1299 := by dsimp [r]; omega
  have hminus : (r : ℝ) - 1 ≤ lam := by
    dsimp [r]
    push_cast
    linarith
  have hplus : lam ≤ r := by
    have h := Nat.lt_floor_add_one lam
    dsimp [r]
    simpa using h.le
  have hledger := scale_ledger (r := r) (lam := lam)
    (by omega) hlow hminus hplus
  dsimp [r]
  exact ⟨hr2, hr1299, hminus, hplus, hledger.1, hledger.2.1,
    hledger.2.2.1, hledger.2.2.2.1, hledger.2.2.2.2⟩

end FordCompactDegreeChoice
#print axioms FordCompactDegreeChoice.compact_degree_choice
