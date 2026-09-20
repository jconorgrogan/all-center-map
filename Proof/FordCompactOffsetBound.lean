import FordCompactLogSum
import FordOffsetLogTransfer
import FordUnitPhaseSign

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordCompactOffsetBound

open FordCompactLogSum FordOffsetLogTransfer FordUnitPhaseSign
open FordUnitPhaseLipschitz

/-- Offset logarithmic sums inherit the compact cancellation bound from the
positive phase theorem by the exact unit-phase sign symmetry. -/
theorem compact_offset_bound :
    ∃ N0 : ℝ, ∀ (N H : ℕ) (t u : ℝ),
      N0 ≤ (N : ℝ) → H ≤ N → 1 < t →
      0 ≤ u → u ≤ 1 →
      1 ≤ Real.log t / Real.log (N : ℝ) →
      Real.log t / Real.log (N : ℝ) ≤ (6492 : ℝ) / 5 →
      ‖∑ n ∈ Finset.range H,
        offsetPhase t u (N + n)‖ ≤
        272 * (N : ℝ) ^ (1 - FordCompactUniformExponent.uniformDecay) := by
  obtain ⟨N0, hcompact⟩ := FordCompactLogSum.compact_log_sum
  refine ⟨N0, ?_⟩
  intro N H t u hN0 hH ht hu0 hu1 hlam hlamhi
  have hN2 : 2 ≤ N := by
    by_contra hn
    have hcases : N = 0 ∨ N = 1 := by omega
    rcases hcases with rfl | rfl <;> norm_num at hlam
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have htpos : 0 < t := by linarith
  let lam : ℝ := Real.log t / Real.log (N : ℝ)
  have htime : (N : ℝ) ^ lam = t := by
    have hNgt : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (show 1 < N by omega)
    have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos hNgt
    rw [Real.rpow_def_of_pos hNpos, show lam = Real.log t / Real.log (N : ℝ) by rfl]
    rw [show Real.log (N : ℝ) * (Real.log t / Real.log (N : ℝ)) = Real.log t by
      field_simp]
    exact Real.exp_log htpos
  have hc := hcompact N H lam u hN0 hH hlam hlamhi hu0 hu1
  have hsign := FordUnitPhaseSign.norm_sum_unitPhase_sign
    (s := Finset.range H)
    (a := fun n : ℕ => t * Real.log (((N + n : ℕ) : ℝ) + u)) 1
  have hoffpos :
      ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ =
        ‖∑ n ∈ Finset.range H,
          unitPhase (t * Real.log (((N + n : ℕ) : ℝ) + u))‖ := by
    simpa [offsetPhase] using hsign
  have harg :
      (∑ n ∈ Finset.range H,
        unitPhase (t * Real.log (((N + n : ℕ) : ℝ) + u))) =
      ∑ n ∈ Finset.range H,
        unitPhase ((N : ℝ) ^ lam *
          Real.log ((N : ℝ) + u + (n : ℝ))) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [htime]
    congr 2
    congr 1
    push_cast
    ring
  calc
    ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ =
        ‖∑ n ∈ Finset.range H,
          unitPhase (t * Real.log (((N + n : ℕ) : ℝ) + u))‖ := hoffpos
    _ = ‖∑ n ∈ Finset.range H,
          unitPhase ((N : ℝ) ^ lam *
            Real.log ((N : ℝ) + u + (n : ℝ)))‖ := by
      rw [harg]
    _ ≤ 272 * (N : ℝ) ^ (1 - FordCompactUniformExponent.uniformDecay) := hc

end FordCompactOffsetBound

#print axioms FordCompactOffsetBound.compact_offset_bound
