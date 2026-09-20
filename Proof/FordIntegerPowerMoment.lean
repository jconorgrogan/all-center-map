import FordIntegerPower
import FordDifferenceDominance

open scoped BigOperators
noncomputable section
namespace FordIntegerPowerMoment

/-- The zero difference representation count is the literal complete moment. -/
theorem zero_difference_eq_complete (r k M : ℕ) :
    FordDifferenceDominance.differencePairCount (FordIntegerPower.intPowerMap r k M) 0 =
      MAPFordCompleteSystemMoment.completeMoment r k M := by
  classical
  unfold FordDifferenceDominance.differencePairCount MAPFordCompleteSystemMoment.completeMoment
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  simp only [sub_eq_zero, FordIntegerPower.intPowerMap_eq_iff, FordPowerFibers.powerMap_eq_iff]

/-- Every literal integer power-difference frequency is dominated by the actual zero moment. -/
theorem difference_le_complete (r k M : ℕ) (d : Fin k → ℤ) :
    FordDifferenceDominance.differencePairCount (FordIntegerPower.intPowerMap r k M) d ≤
      MAPFordCompleteSystemMoment.completeMoment r k M := by
  rw [← zero_difference_eq_complete]
  exact FordDifferenceDominance.differencePairCount_le_zeroMoment _ _

end FordIntegerPowerMoment
#print axioms FordIntegerPowerMoment.zero_difference_eq_complete
#print axioms FordIntegerPowerMoment.difference_le_complete
