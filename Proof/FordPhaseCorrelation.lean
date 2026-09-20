import FordPhaseDifferencing
import FordDiscreteCorrelationDiagonal

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordPhaseCorrelation

open FordPhaseDifferencing FordDiscreteCorrelationDiagonal

/-- The literal truncated correlation of a recursively differenced phase
sequence is the next phase difference, with the shift applied on the left. -/
theorem correlation_phaseDiff_eq
    (H h : ℕ) (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    correlation H h (fun n => phaseDiff hs f (x + (n : ℝ))) =
      ∑ n ∈ Finset.range (H - h),
        phaseDiff ((h : ℝ) :: hs) f (x + (n : ℝ)) := by
  unfold correlation
  apply Finset.sum_congr rfl
  intro n hn
  rw [phaseDiff]
  congr 1
  push_cast
  ring

/-- Every term in the shifted phase sequence has unit norm. -/
theorem phaseDiff_sequence_norm
    (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) (n : ℕ) :
    ‖phaseDiff hs f (x + (n : ℝ))‖ = 1 := by
  exact phaseDiff_norm hs f (x + (n : ℝ))

end FordPhaseCorrelation

#print axioms FordPhaseCorrelation.correlation_phaseDiff_eq
#print axioms FordPhaseCorrelation.phaseDiff_sequence_norm
