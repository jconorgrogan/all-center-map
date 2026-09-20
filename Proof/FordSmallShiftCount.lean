import Mathlib

noncomputable section
namespace FordSmallShiftCount

/-- Literal set of shifts below a real cutoff, including the zero shift. -/
def smallShifts (Q : ℕ) (tau : ℝ) : Finset ℕ :=
  (Finset.range Q).filter (fun h => (h : ℝ) < tau)

theorem smallShifts_eq_range (Q : ℕ) (tau : ℝ) :
    smallShifts Q tau = Finset.range (min Q (Nat.ceil tau)) := by
  ext n
  simp [smallShifts, lt_min_iff, Nat.lt_ceil]

theorem card_smallShifts_le (Q : ℕ) {tau : ℝ} (htau : 0 ≤ tau) :
    ((smallShifts Q tau).card : ℝ) ≤ tau + 1 := by
  rw [smallShifts_eq_range, Finset.card_range]
  have h : ((min Q (Nat.ceil tau) : ℕ) : ℝ) ≤ (Nat.ceil tau : ℝ) := by
    exact_mod_cast (min_le_right Q (Nat.ceil tau))
  exact h.trans (Nat.ceil_lt_add_one htau).le

/-- The small-shift fraction retains its rounding error `1/Q`. -/
theorem fraction_smallShifts_le {Q : ℕ} (hQ : 1 ≤ Q)
    {A : ℝ} (hA : 0 ≤ A) :
    ((smallShifts Q ((Q : ℝ) * A)).card : ℝ) / Q ≤ A + 1 / Q := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hc := card_smallShifts_le Q (mul_nonneg hq.le hA)
  calc
    _ ≤ ((Q : ℝ) * A + 1) / Q := div_le_div_of_nonneg_right hc hq.le
    _ = A + 1 / Q := by field_simp

end FordSmallShiftCount
#print axioms FordSmallShiftCount.smallShifts_eq_range
#print axioms FordSmallShiftCount.card_smallShifts_le
#print axioms FordSmallShiftCount.fraction_smallShifts_le
