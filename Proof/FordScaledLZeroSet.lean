import FordScaledZeroSet
import FordScaledLZeroCount

open scoped BigOperators
noncomputable section

namespace FordScaledLZeroSet

open Complex Set Filter Metric
open FordScaledDiskGrowth

/-- The actual strict inner-disk zero set of a Dirichlet `L`-function is
finite, complete, and carries the Jensen multiplicity bound supplied by the
scaled disk count. -/
theorem exists_finite_L_zero_set :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ),
        3 ≤ t →
        ∃ S : Finset ℂ,
          (∀ ρ, ρ ∈ S ↔
            ρ ∈ Metric.ball (diskCenter t) (3 * diskScale t) ∧
              DirichletCharacter.LFunction χ ρ = 0) ∧
          (∀ ρ ∈ S,
            analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ ∧
              1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ) ∧
          (∑ ρ ∈ S,
            (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℝ)) ≤
            (D + 3 * Real.log (N : ℝ) +
              2 * Real.log (Real.log (t + 3))) / Real.log 2 := by
  obtain ⟨D, hD, hcount⟩ := FordScaledLZeroCount.scaled_L_zero_count
  refine ⟨D, hD, ?_⟩
  intro N hN χ t ht
  obtain ⟨hT, ha, hah, hcoords⟩ := disk_geometry ht
  have hlower := FordEulerCenterLower.norm_LFunction_one_add_delta_lower χ ha
    (show diskScale t ≤ 1 by linarith) (t := t)
  change diskScale t / 2 ≤
    ‖DirichletCharacter.LFunction χ (diskCenter t)‖ at hlower
  have hcenter : 0 <
      ‖DirichletCharacter.LFunction χ (diskCenter t)‖ :=
    lt_of_lt_of_le (by positivity) hlower
  have hfc : DirichletCharacter.LFunction χ (diskCenter t) ≠ 0 :=
    norm_pos_iff.mp hcenter
  obtain ⟨S, hSexact, hSmult⟩ :=
    FordScaledZeroSet.exists_finite_zero_set ha
      (FordScaledLZeroCount.analyticOnNhd_LFunction_scaled_disk χ ht) hfc
  have hSclosed : ∀ ρ ∈ S,
      ρ ∈ Metric.closedBall (diskCenter t) (3 * diskScale t) := by
    intro ρ hρ
    exact ball_subset_closedBall ((hSexact ρ).mp hρ).1
  have hbound := hcount N χ t ht S hSclosed
  refine ⟨S, hSexact, hSmult, ?_⟩
  simpa [FordScaledJensenCount.analyticMultiplicity] using hbound

end FordScaledLZeroSet

#print axioms FordScaledLZeroSet.exists_finite_L_zero_set
