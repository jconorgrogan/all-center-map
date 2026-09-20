import FordScaledLocalRemainder
import FordScaledLZeroCount

open scoped BigOperators
noncomputable section
namespace FordScaledLRemainder
open FordScaledDiskGrowth

/-- A thin-disk remainder estimate for actual Dirichlet L-functions, with
no growth, zero-count, or analytic continuation assumptions left to callers. -/
theorem exists_finite_L_zero_set_remainder :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (t : ℝ), 3 ≤ t → ∃ S : Finset ℂ,
      (∀ ρ, ρ ∈ S ↔ ρ ∈ Metric.ball (diskCenter t) (3 * diskScale t) ∧
        DirichletCharacter.LFunction χ ρ = 0) ∧
      (∀ ρ ∈ S, analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ ∧
        1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
      ∀ s ∈ Metric.ball (diskCenter t) (diskScale t),
        DirichletCharacter.LFunction χ s ≠ 0 →
        ‖logDeriv (DirichletCharacter.LFunction χ) s -
          ∑ ρ ∈ S, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) /
            (s - ρ)‖ ≤
          (20 + 1 / (2 * Real.log 2)) *
            (1 + D + 3 * Real.log (N : ℝ) + 2 * Real.log (Real.log (t + 3))) /
            diskScale t := by
  obtain ⟨C, D, hC, hD, hb⟩ := FordScaledDiskLogBudget.disk_log_budget
  refine ⟨D, hD, ?_⟩
  intro N hN χ t ht
  obtain ⟨hbound, hbudget⟩ := hb N χ t ht
  obtain ⟨hT, ha, hah, hcoords⟩ := disk_geometry ht
  have hlower := FordEulerCenterLower.norm_LFunction_one_add_delta_lower χ ha
    (show diskScale t ≤ 1 by linarith) (t := t)
  change diskScale t / 2 ≤ ‖DirichletCharacter.LFunction χ (diskCenter t)‖ at hlower
  have hcenter : 0 < ‖DirichletCharacter.LFunction χ (diskCenter t)‖ :=
    lt_of_lt_of_le (by positivity) hlower
  have hfc : DirichletCharacter.LFunction χ (diskCenter t) ≠ 0 := norm_pos_iff.mp hcenter
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (NeZero.pos N)
  have hG : 0 < (N : ℝ) * ((N : ℝ) ^ 2 + C * Real.log (t + 3)) := by positivity
  have hNlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ N))
  have hTlog : 0 ≤ Real.log (Real.log (t + 3)) := Real.log_nonneg hT
  have hM : 0 < 1 + D + 3 * Real.log (N : ℝ) +
      2 * Real.log (Real.log (t + 3)) := by positivity
  rw [Real.log_div hG.ne' hcenter.ne'] at hbudget
  exact FordScaledLocalRemainder.exists_finite_zero_set_remainder ha hG hM hfc
    (FordScaledLZeroCount.analyticOnNhd_LFunction_scaled_disk χ ht)
    hbound (hbudget.trans (by linarith))

end FordScaledLRemainder
#print axioms FordScaledLRemainder.exists_finite_L_zero_set_remainder
