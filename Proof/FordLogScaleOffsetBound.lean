import FordAllLambdaOffsetBound

open scoped BigOperators
noncomputable section
namespace FordLogScaleOffsetBound
open FordAllLambdaOffsetBound FordOffsetLogTransfer

theorem power_identity {N t c : ℝ} (hN : 1 < N) (ht : 1 < t) :
    N ^ (1 - c / (Real.log t / Real.log N) ^ 2) =
      N * Real.exp (-c * (Real.log N) ^ 3 / (Real.log t) ^ 2) := by
  have hNpos : 0 < N := by linarith
  have hLN : Real.log N ≠ 0 := (Real.log_pos hN).ne'
  have hLT : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  rw [Real.rpow_def_of_pos hNpos]
  have he : Real.log N * (1 - c / (Real.log t / Real.log N) ^ 2) =
      Real.log N + (-c * (Real.log N) ^ 3 / (Real.log t) ^ 2) := by
    field_simp
    <;> ring
  rw [he, Real.exp_add, Real.exp_log hNpos]

/-- The actual exponential-sum estimate in the logarithmic scale needed for growth bounds. -/
theorem log_scale_offset_bound :
    ∃ N0 : ℝ, ∀ (N H : ℕ) (t u : ℝ),
      N0 ≤ (N : ℝ) → H ≤ N → 1 < t → 0 ≤ u → u ≤ 1 →
      1 ≤ Real.log t / Real.log (N : ℝ) →
      1000 * (Real.log t) ^ ((4 : ℝ) / 5) ≤ Real.log (N : ℝ) →
      ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
        272 * (N : ℝ) * Real.exp
          (-savingCoeff * (Real.log (N : ℝ)) ^ 3 / (Real.log t) ^ 2) := by
  obtain ⟨N0, hN0⟩ := all_lambda_offset_bound
  refine ⟨N0, ?_⟩
  intro N H t u hlarge hH ht hu hu1 hlam hthreshold
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hc : N = 0 ∨ N = 1 := by omega
    rcases hc with rfl | rfl <;> norm_num at hlam
  have hb := hN0 N H t u hlarge hH ht hu hu1 hlam hthreshold
  rw [power_identity (by exact_mod_cast (show 1 < N by omega)) ht] at hb
  simpa only [mul_assoc] using hb

end FordLogScaleOffsetBound
#print axioms FordLogScaleOffsetBound.power_identity
#print axioms FordLogScaleOffsetBound.log_scale_offset_bound
