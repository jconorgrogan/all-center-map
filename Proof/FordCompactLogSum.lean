import FordCompactLeafEstimate
import FordCompactUniformThreshold
import FordCompactUniformExponent
import FordCompactDegreeChoice
import FordPhasePowerDecay

open scoped BigOperators
noncomputable section
namespace FordCompactLogSum
open FordCompactDifferenceScales FordCompactUniformExponent
open FordUnitPhaseLipschitz FordPhaseTreeRecurrence

/-- Unconditional compact-lambda cancellation after one uniform threshold.
All good-shift leaf estimates, endpoint margins and finite recurrence are discharged. -/
theorem compact_log_sum :
    ∃ N0 : ℝ, ∀ (N H : ℕ) (lam u : ℝ), N0 ≤ (N : ℝ) → H ≤ N →
      1 ≤ lam → lam ≤ (6492 : ℝ) / 5 → 0 ≤ u → u ≤ 1 →
      ‖∑ n ∈ Finset.range H,
        unitPhase ((N : ℝ) ^ lam * Real.log ((N : ℝ) + u + (n : ℝ)))‖ ≤
        272 * (N : ℝ) ^ (1 - uniformDecay) := by
  obtain ⟨N0, hN0⟩ := FordCompactUniformThreshold.compact_uniform_threshold
  refine ⟨N0, ?_⟩
  intro N H lam u hNN hH hlam hlamhi hu0 hu1
  let r : ℕ := Nat.floor lam + 1
  let q : ℝ := shiftExponent r lam
  let eps : ℝ := cutoffExponent r
  obtain ⟨hr2, hrmax, hlo, hhi, heps, heq, hq, hU, hL⟩ :=
    FordCompactDegreeChoice.compact_degree_choice hlam hlamhi
  have hprops := hN0 r hr2 hrmax (N : ℝ) hNN
  have hN2 : 2 ≤ N := by exact_mod_cast hprops.1
  have hN1 : 1 ≤ N := by omega
  have hsmall : 16 * (N : ℝ) ^ (-eps) ≤ 1 := by
    simpa [eps, cutoffExponent] using hprops.2.2.1
  have hleaf : ∀ hs : List ℕ,
      (∀ g ∈ hs, g ∈ FordGoodShiftError.goodShifts (FordScaleFloor.scale N q)
        ((N : ℝ) ^ (-eps))) → hs.length = r →
      phaseSize N H (fun y : ℝ => (N : ℝ) ^ lam * Real.log y)
        ((N : ℝ) + u) hs ≤ (N : ℝ) ^ (-eps) := by
    intro hs hgood hlen
    apply FordCompactLeafEstimate.phaseSize_le hs hN2 hH (by rw [hlen]; exact hr2)
      (by exact heps.le) (by exact heq) (by exact hq) (by linarith)
      (by simpa [hlen, q, r] using hU)
      (by simpa [hlen, q, eps, r] using hL)
      hgood hu0 hu1
    · simpa [hlen] using hprops.2.1
    · simpa only [hlen, neg_div] using hprops.2.2.2.1
    · simpa only [hlen, eps, cutoffExponent, neg_div] using hprops.2.2.2.2
  have hb := FordPhasePowerDecay.norm_sum_le (r := r) hN1 hH
    (show 0 ≤ eps from heps.le) (show eps ≤ q from heq)
    (show q ≤ 1 by linarith) hsmall
    (fun y : ℝ => (N : ℝ) ^ lam * Real.log y) ((N : ℝ) + u) hleaf
  have hd : eps / ((2 ^ r : ℕ) : ℝ) = degreeDecay r :=
    cutoff_div_pow_eq_degree (by omega)
  have hu := uniform_le_degree (r := r) (by omega) hrmax
  have hp : (N : ℝ) ^ (1 - eps / ((2 ^ r : ℕ) : ℝ)) ≤
      (N : ℝ) ^ (1 - uniformDecay) := by
    apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1)
    rw [hd]
    linarith
  exact hb.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

end FordCompactLogSum
#print axioms FordCompactLogSum.compact_log_sum
