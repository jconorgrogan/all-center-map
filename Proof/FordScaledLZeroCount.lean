import FordScaledDiskLogBudget
import FordScaledJensenCount

open Set
open scoped BigOperators
noncomputable section
namespace FordScaledLZeroCount
open FordScaledDiskGrowth

theorem analyticOnNhd_LFunction_upper_halfplane {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) {z : ℂ | 0 < z.im} := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    apply (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl ?_)).differentiableWithinAt
    intro h
    subst z
    simpa using hz
  · exact isOpen_lt continuous_const Complex.continuous_im

theorem analyticOnNhd_LFunction_scaled_disk {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {t : ℝ} (ht : 3 ≤ t) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ)
      (Metric.closedBall (diskCenter t) (6 * diskScale t)) := by
  apply (analyticOnNhd_LFunction_upper_halfplane χ).mono
  intro z hz
  have hzi := ((disk_geometry ht).2.2.2 z hz).2.2.1
  change 0 < z.im
  linarith

/-- A thin-disk zero count with logarithmic conductor and double-logarithmic
height cost. The finite set need not contain all zeros. -/
theorem scaled_L_zero_count :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (t : ℝ), 3 ≤ t → ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ Metric.closedBall (diskCenter t) (3 * diskScale t)) →
      (∑ z ∈ S, (FordScaledJensenCount.analyticMultiplicity (DirichletCharacter.LFunction χ) z : ℝ)) ≤
        (D + 3 * Real.log (N : ℝ) + 2 * Real.log (Real.log (t + 3))) / Real.log 2 := by
  obtain ⟨C, D, hC, hD, hb⟩ := FordScaledDiskLogBudget.disk_log_budget
  refine ⟨D, hD, ?_⟩
  intro N hN χ t ht S hS
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
  have hj := FordScaledJensenCount.finite_analyticMultiplicity_le ha
    (analyticOnNhd_LFunction_scaled_disk χ ht) hfc hG hbound S hS
  rw [Real.log_div hG.ne' hcenter.ne'] at hbudget
  exact hj.trans (div_le_div_of_nonneg_right hbudget (Real.log_pos (by norm_num)).le)

end FordScaledLZeroCount
#print axioms FordScaledLZeroCount.analyticOnNhd_LFunction_upper_halfplane
#print axioms FordScaledLZeroCount.analyticOnNhd_LFunction_scaled_disk
#print axioms FordScaledLZeroCount.scaled_L_zero_count
