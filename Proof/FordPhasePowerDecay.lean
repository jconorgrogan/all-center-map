import FordPhaseScaleIteration
import FordPoweredDecay

open scoped BigOperators
noncomputable section
namespace FordPhasePowerDecay
open FordPhaseTreeRecurrence FordPhaseScaleIteration FordGoodShiftError
open FordUnitPhaseLipschitz FordPhaseDifferencing

/-- Conditional only on terminal good-shift cancellation; finite iteration is discharged. -/
theorem norm_sum_le {N H r : ℕ} {q eps : ℝ} (hN : 1 ≤ N) (hH : H ≤ N)
    (heps : 0 ≤ eps) (heq : eps ≤ q) (hq1 : q ≤ 1)
    (hsmall : 16 * (N : ℝ) ^ (-eps) ≤ 1)
    (f : ℝ → ℝ) (x : ℝ)
    (hleaf : ∀ hs : List ℕ,
      (∀ g ∈ hs, g ∈ goodShifts (FordScaleFloor.scale N q) ((N : ℝ) ^ (-eps))) →
      hs.length = r → phaseSize N H f x hs ≤ (N : ℝ) ^ (-eps)) :
    ‖∑ n ∈ Finset.range H, unitPhase (f (x + (n : ℝ)))‖ ≤
      272 * (N : ℝ) ^ (1 - eps / ((2 ^ r : ℕ) : ℝ)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := phaseSize_scale_iterated_le hN hH heps heq hq1 hsmall f x
    ((N : ℝ) ^ (-eps)) (Real.rpow_nonneg hn.le _) hleaf
  have hp : phaseSize N H f x [] ^ (2 ^ r) ≤
      16 ^ (2 ^ r) * (17 * (N : ℝ) ^ (-eps)) := by nlinarith [hb]
  have hd := FordPoweredDecay.decay_of_iteration
    (Nat.one_le_pow r 2 (by omega)) (phaseSize_nonneg N H f x []) hn hp
  have hs : ‖∑ n ∈ Finset.range H, unitPhase (f (x + (n : ℝ)))‖ / (N : ℝ) ≤
      272 * (N : ℝ) ^ (-eps / ((2 ^ r : ℕ) : ℝ)) := by
    simpa [phaseSize, phaseSum, phaseDiff] using hd
  have hm := (div_le_iff₀ hn).mp hs
  calc
    _ ≤ 272 * (N : ℝ) ^ (-eps / ((2 ^ r : ℕ) : ℝ)) * N := hm
    _ = 272 * (N : ℝ) ^ (1 - eps / ((2 ^ r : ℕ) : ℝ)) := by
      have hi : (N : ℝ) ^ (-eps / ((2 ^ r : ℕ) : ℝ)) * N =
          (N : ℝ) ^ (1 - eps / ((2 ^ r : ℕ) : ℝ)) := by
        calc
          _ = (N : ℝ) ^ (-eps / ((2 ^ r : ℕ) : ℝ)) * (N : ℝ) ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
      rw [mul_assoc, hi]

end FordPhasePowerDecay
#print axioms FordPhasePowerDecay.norm_sum_le
