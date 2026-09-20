import FordScaledZeroFree
import DirichletLFunctionConjugationGeneral

noncomputable section
namespace FordScaledZeroFreeAbsolute

open Complex FordScaledDiskGrowth FordScaledZeroFreeGeometry
open scoped ComplexConjugate

/-- The actual zero gap holds at either sign of the ordinate.  At negative
height we apply the positive-height estimate to the inverse character and the
conjugate zero. -/
theorem actual_zero_gap_absolute :
    ∃ D : ℝ, 0 < D ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (ρ : ℂ),
        3 ≤ |ρ.im| →
        DirichletCharacter.LFunction χ ρ = 0 →
        diskScale (2 * |ρ.im|) /
            (200 * remainderConstant * logBudget D N (2 * |ρ.im|)) ≤
          1 - ρ.re := by
  obtain ⟨D, hD, hgap⟩ := FordScaledZeroFree.actual_zero_gap
  refine ⟨D, hD, ?_⟩
  intro N hN χ ρ hheight hzero
  by_cases hnonneg : 0 ≤ ρ.im
  · have hheight' : 3 ≤ ρ.im := by
      simpa [abs_of_nonneg hnonneg] using hheight
    have hgap' := hgap N χ ρ.im hheight' ρ hzero rfl
    simpa [abs_of_nonneg hnonneg] using hgap'
  · have hneg : ρ.im < 0 := lt_of_not_ge hnonneg
    have hheight' : 3 ≤ |ρ.im| := hheight
    have hsneq : ρ ≠ 1 := by
      intro hs
      have himzero : ρ.im = 0 := by simpa [hs]
      linarith
    have hzero' :
        DirichletCharacter.LFunction χ⁻¹ (conj ρ) = 0 := by
      have hconj :=
        MAPDirichletLFunctionConjugationGeneral.LFunction_inv_conj_of_ne_one
          χ ρ hsneq
      rw [hconj]
      simp [hzero]
    have himconj : (conj ρ).im = |ρ.im| := by
      simp [abs_of_neg hneg]
    have hgap' := hgap N (χ⁻¹) |ρ.im| hheight' (conj ρ) hzero' himconj
    simpa [himconj] using hgap'

end FordScaledZeroFreeAbsolute

#print axioms FordScaledZeroFreeAbsolute.actual_zero_gap_absolute
