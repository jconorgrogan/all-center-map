import FordWeightedOffsetBlock
import FordLogScaleOffsetBound
import FordWeightedCubicEnvelope

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordWeightedGrowthBlock

open FordAllLambdaOffsetBound FordOffsetLogTransfer

/-- The logarithmic scale cancellation estimate survives the real decay weight:
the actual complex powers are bounded by the cubic growth envelope. -/
theorem norm_weighted_growth_block :
    ∃ N0 : ℝ, ∀ (N H : ℕ) (t u eta : ℝ),
      N0 ≤ (N : ℝ) → H ≤ N → 1 < t → 0 ≤ u → u ≤ 1 →
      0 ≤ eta → eta ≤ 1 →
      1 ≤ Real.log t / Real.log (N : ℝ) →
      1000 * (Real.log t) ^ ((4 : ℝ) / 5) ≤ Real.log (N : ℝ) →
      ‖∑ n ∈ Finset.range H,
          (((N + n : ℕ) : ℝ) + u : ℂ) ^
            (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
        272 * Real.exp
          (eta * Real.sqrt (eta / savingCoeff) * Real.log t) := by
  obtain ⟨N0, hN0⟩ := FordLogScaleOffsetBound.log_scale_offset_bound
  refine ⟨N0, ?_⟩
  intro N H t u eta hlarge hH ht hu hu1 heta heta1 hlam hthreshold
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hc : N = 0 ∨ N = 1 := by omega
    rcases hc with rfl | rfl <;> norm_num at hlam
  have hσ : 0 ≤ 1 - eta := by linarith
  have hB : 0 ≤
      272 * (N : ℝ) * Real.exp
        (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2) := by
    positivity
  have hprefix : ∀ q, q ≤ H →
      ‖∑ n ∈ Finset.range q, offsetPhase t u (N + n)‖ ≤
        272 * (N : ℝ) * Real.exp
          (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2) := by
    intro q hq
    exact hN0 N q t u hlarge (le_trans hq hH) ht hu hu1 hlam hthreshold
  have hweighted := FordWeightedOffsetBlock.norm_weighted_offset_block_le
    (u := u) (σ := 1 - eta) (t := t)
    (B := 272 * (N : ℝ) * Real.exp
      (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2))
    (N := N) (H := H) hu hσ hN2 hH hB hprefix
  have henv := FordWeightedCubicEnvelope.weighted_cubic_envelope
    (N := (N : ℝ)) (T := Real.log t) (c := savingCoeff) (eta := eta)
    (by exact_mod_cast (show 1 ≤ N by omega))
    (Real.log_pos ht) FordAllLambdaOffsetBound.savingCoeff_pos heta
  calc
    _ ≤ (272 * (N : ℝ) * Real.exp
        (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2)) *
          (N : ℝ) ^ (-(1 - eta)) := hweighted
    _ = (N : ℝ) ^ (-(1 - eta)) *
        (272 * (N : ℝ) * Real.exp
          (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2)) := by ring
    _ ≤ 272 * Real.exp (eta * Real.sqrt (eta / savingCoeff) * Real.log t) := henv

end FordWeightedGrowthBlock

#print axioms FordWeightedGrowthBlock.norm_weighted_growth_block
