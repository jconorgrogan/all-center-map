import FordGoodShiftError

noncomputable section
namespace FordGoodShiftsNonempty

open FordGoodShiftError FordDiscretePairCount

/-- The last positive shift is good whenever the threshold is at most one half. -/
theorem goodShifts_nonempty {Q : ℕ} {A : ℝ}
    (hQ : 2 ≤ Q) (hA : A ≤ (1 : ℝ) / 2) :
    (goodShifts Q A).Nonempty := by
  refine ⟨Q - 1, ?_⟩
  simp only [goodShifts, positiveRange, Finset.mem_filter, Finset.mem_range]
  constructor
  · omega
  · have hQr : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hQnonneg : (0 : ℝ) ≤ (Q : ℝ) := by positivity
    have hcast : ((Q - 1 : ℕ) : ℝ) = (Q : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast]
    nlinarith

end FordGoodShiftsNonempty

#print axioms FordGoodShiftsNonempty.goodShifts_nonempty
