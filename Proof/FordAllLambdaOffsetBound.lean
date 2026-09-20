import FordCompactOffsetBound
import FordOffsetThresholdBound
import FordCompactUniformExponent
import FordWEnvelopeScalar

noncomputable section
namespace FordAllLambdaOffsetBound

open FordCompactOffsetBound FordOffsetThresholdBound FordCompactUniformExponent
open FordWEnvelopeScalar FordOffsetLogTransfer

def savingCoeff : ℝ := min uniformDecay (1 / 10000000000 : ℝ)

theorem savingCoeff_pos : 0 < savingCoeff := by
  unfold savingCoeff
  exact lt_min uniformDecay_pos (by norm_num)

/-- All-lambda offset bound, combining the compact and threshold branches. -/
theorem all_lambda_offset_bound :
    ∃ N0 : ℝ, ∀ (N H : ℕ) (t u : ℝ),
      N0 ≤ (N : ℝ) → H ≤ N → 1 < t →
      0 ≤ u → u ≤ 1 →
      1 ≤ Real.log t / Real.log (N : ℝ) →
      1000 * (Real.log t) ^ ((4 : ℝ) / 5) ≤ Real.log (N : ℝ) →
      ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
        272 * (N : ℝ) ^
          (1 - savingCoeff /
            (Real.log t / Real.log (N : ℝ)) ^ 2) := by
  obtain ⟨N0, hcompact⟩ := FordCompactOffsetBound.compact_offset_bound
  refine ⟨N0, ?_⟩
  intro N H t u hN0 hH ht hu0 hu1 hlam hthreshold
  let lam : ℝ := Real.log t / Real.log (N : ℝ)
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hcases : N = 0 ∨ N = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hlam
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsavepos : 0 < savingCoeff := by
    exact savingCoeff_pos
  have hsaveu : savingCoeff ≤ uniformDecay := by
    dsimp [savingCoeff]
    exact min_le_left _ _
  have hsavetiny : savingCoeff ≤ (1 / 10000000000 : ℝ) := by
    dsimp [savingCoeff]
    exact min_le_right _ _
  have hlampos : 0 < lam := lt_of_lt_of_le (by norm_num) hlam
  have hlam2 : 1 ≤ lam ^ 2 := by nlinarith
  have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hcompactexp :
      1 - uniformDecay ≤ 1 - savingCoeff / lam ^ 2 := by
    have hdiv : savingCoeff / lam ^ 2 ≤ savingCoeff := by
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hsavepos, hlam2]
    linarith
  have hhigh_exp :
      1 - (1 / 10000000000 : ℝ) / lam ^ 2 ≤
        1 - savingCoeff / lam ^ 2 := by
    have hdiv : savingCoeff / lam ^ 2 ≤
        (1 / 10000000000 : ℝ) / lam ^ 2 :=
      div_le_div_of_nonneg_right hsavetiny (by positivity)
    linarith
  rcases le_total lam ((6492 : ℝ) / 5) with hsmall | hlarge
  · have hc := hcompact N H t u hN0 hH ht hu0 hu1 hlam hsmall
    have hp := Real.rpow_le_rpow_of_exponent_le hN1 hcompactexp
    calc
      ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
          272 * (N : ℝ) ^ (1 - uniformDecay) := hc
      _ ≤ 272 * (N : ℝ) ^ (1 - savingCoeff / lam ^ 2) :=
        mul_le_mul_of_nonneg_left hp (by norm_num)
  · have hblam : 2000 * b ≤ lam := by
      dsimp [b]
      norm_num at hlarge ⊢
      linarith
    have hh := FordOffsetThresholdBound.offset_threshold_bound
      ht hN2 hH hu0 hu1 hblam hthreshold
    have hp := Real.rpow_le_rpow_of_exponent_le hN1 hhigh_exp
    have hconst : (4 : ℝ) ≤ 272 := by norm_num
    have hh' : ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
        4 * (N : ℝ) ^
          (1 - (1 / 10000000000 : ℝ) / lam ^ 2) := by
      simpa [lam, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh
    calc
      ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
          4 * (N : ℝ) ^
            (1 - (1 / 10000000000 : ℝ) / lam ^ 2) := hh' 
      _ ≤ 272 * (N : ℝ) ^ (1 - savingCoeff / lam ^ 2) := by
        exact (mul_le_mul hconst hp (by positivity) (by positivity))

end FordAllLambdaOffsetBound

#print axioms FordAllLambdaOffsetBound.all_lambda_offset_bound
#print axioms FordAllLambdaOffsetBound.savingCoeff_pos
