import FordScaledLZeroSet

noncomputable section
namespace FordScaledLZeroReal

/-! Right-half-plane adapters for the actual Dirichlet `L`-function zeros.
The only input is Mathlib's closed-half-plane nonvanishing theorem. -/

theorem LFunction_eq_zero_re_le_one
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hzero : DirichletCharacter.LFunction χ s = 0) :
    s.re ≤ 1 := by
  by_contra hs
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hnz := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
    (.inr hs1) (le_of_not_ge hs)
  exact hnz hzero

theorem LFunction_ne_zero_of_one_lt_re
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  intro hzero
  have hle := LFunction_eq_zero_re_le_one χ hzero
  linarith

theorem not_mem_of_actual_L_zero_set_of_one_lt_re
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {S : Finset ℂ} {s : ℂ} {P : ℂ → Prop}
    (hS : ∀ ρ, ρ ∈ S ↔ P ρ ∧
      DirichletCharacter.LFunction χ ρ = 0)
    (hs : 1 < s.re) :
    s ∉ S := by
  intro hsS
  have hzero := ((hS s).mp hsS).2
  have hle := LFunction_eq_zero_re_le_one χ hzero
  linarith

end FordScaledLZeroReal

#print axioms FordScaledLZeroReal.LFunction_eq_zero_re_le_one
#print axioms FordScaledLZeroReal.LFunction_ne_zero_of_one_lt_re
#print axioms FordScaledLZeroReal.not_mem_of_actual_L_zero_set_of_one_lt_re
