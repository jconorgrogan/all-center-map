import JutilaReflectionDirichletIdentity
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Primitive functional-equation adapter in Jutila's reflection step

Jutila's proof of Lemma 1, equation (2.1), moves the initial Mellin
integral to `Re (s + w) = -1/2` and then applies the primitive Dirichlet
functional equation (Acta Arith. 32 (1977), p. 58).  Mathlib states that
functional equation for the completed L-function.  This file certifies the
exact algebra which converts it to the uncompleted L-function and its gamma
factor.

No contour shift or estimate is asserted here.  The nonvanishing hypotheses
on the gamma factors record exactly what is needed to undo Mathlib's quotient
formula for `LFunction`.
-/

namespace JutilaPrimitiveFunctionalEquation

open Complex DirichletCharacter

noncomputable section

theorem gammaFactor_ne_zero_of_re_pos
    {q : ℕ} (chi : DirichletCharacter ℂ q) {z : ℂ} (hz : 0 < z.re) :
    gammaFactor chi z ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos hz
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [Complex.add_re, Complex.one_re]
    linarith

/-- A primitive principal Dirichlet character has level one.  Thus the only
principal residue in the primitive branch of Jutila's argument is the
Riemann-zeta residue. -/
theorem level_eq_one_of_isPrimitive_eq_one
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) (hone : chi = 1) : q = 1 := by
  have hc : conductor chi = q := (isPrimitive_def chi).mp hchi
  rw [hone, conductor_one] at hc
  exact hc.symm

/-- On Jutila's reflected line `Re z = -1/2`, neither parity's gamma
factor vanishes. -/
theorem gammaFactor_ne_zero_on_reflectedLine
    {q : ℕ} (chi : DirichletCharacter ℂ q) {z : ℂ}
    (hz : z.re = -(1 : ℝ) / 2) : gammaFactor chi z ≠ 0 := by
  rcases chi.even_or_odd with heven | hodd
  · rw [heven.gammaFactor_def]
    intro hzero
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hzero
    have hre := congrArg Complex.re hn
    norm_num [Complex.neg_re, Complex.mul_re] at hre
    rw [hz] at hre
    cases n with
    | zero => norm_num at hre
    | succ n =>
        have hnat : 1 ≤ n.succ := Nat.succ_le_succ (Nat.zero_le n)
        have hnlarge : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast hnat
        nlinarith
  · rw [hodd.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    rw [Complex.add_re, Complex.one_re]
    rw [hz]
    norm_num

theorem LFunction_mul_gammaFactor_eq_completed
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (z : ℂ)
    (hz : z ≠ 0 ∨ q ≠ 1) (hgamma : gammaFactor chi z ≠ 0) :
    LFunction chi z * gammaFactor chi z = completedLFunction chi z := by
  rw [LFunction_eq_completed_div_gammaFactor chi z hz]
  exact div_mul_cancel₀ _ hgamma

/-- The exact functional-equation identity used after Jutila's first contour
shift, with the dual side left in completed form.  It is obtained from
`IsPrimitive.completedLFunction_one_sub` by substituting `1 - z` for its
argument. -/
theorem primitive_LFunction_mul_gammaFactor_eq_completed_dual
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) (z : ℂ)
    (hz : z ≠ 0 ∨ q ≠ 1) (hgamma : gammaFactor chi z ≠ 0) :
    LFunction chi z * gammaFactor chi z =
      (q : ℂ) ^ ((1 : ℂ) / 2 - z) * rootNumber chi *
        completedLFunction chi⁻¹ (1 - z) := by
  rw [LFunction_mul_gammaFactor_eq_completed chi z hz hgamma]
  have hfe := hchi.completedLFunction_one_sub (1 - z)
  convert hfe using 1 <;> ring

/-- Fully uncompleted form of the primitive functional equation.  This is the
literal algebraic replacement needed before expanding the dual Dirichlet
series in Jutila's proof. -/
theorem primitive_LFunction_functionalEquation
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) (z : ℂ)
    (hz : z ≠ 0 ∨ q ≠ 1)
    (hdual : 1 - z ≠ 0 ∨ q ≠ 1)
    (hgamma : gammaFactor chi z ≠ 0)
    (hgammaDual : gammaFactor chi⁻¹ (1 - z) ≠ 0) :
    LFunction chi z * gammaFactor chi z =
      (q : ℂ) ^ ((1 : ℂ) / 2 - z) * rootNumber chi *
        (LFunction chi⁻¹ (1 - z) * gammaFactor chi⁻¹ (1 - z)) := by
  rw [primitive_LFunction_mul_gammaFactor_eq_completed_dual hchi z hz hgamma]
  rw [LFunction_mul_gammaFactor_eq_completed chi⁻¹ (1 - z) hdual hgammaDual]

/-- Jutila's functional-equation algebra on the exact reflected line.  The
gamma nonvanishing conditions are discharged from the line equation rather
than left as hypotheses. -/
theorem primitive_LFunction_functionalEquation_on_reflectedLine
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hchi : IsPrimitive chi) (z : ℂ)
    (hzre : z.re = -(1 : ℝ) / 2)
    (hz : z ≠ 0 ∨ q ≠ 1)
    (hdual : 1 - z ≠ 0 ∨ q ≠ 1) :
    LFunction chi z * gammaFactor chi z =
      (q : ℂ) ^ ((1 : ℂ) / 2 - z) * rootNumber chi *
        (LFunction chi⁻¹ (1 - z) * gammaFactor chi⁻¹ (1 - z)) := by
  apply primitive_LFunction_functionalEquation hchi z hz hdual
    (gammaFactor_ne_zero_on_reflectedLine chi hzre)
  apply gammaFactor_ne_zero_of_re_pos
  rw [Complex.sub_re, Complex.one_re]
  rw [hzre]
  norm_num

end

end JutilaPrimitiveFunctionalEquation

#print axioms JutilaPrimitiveFunctionalEquation.LFunction_mul_gammaFactor_eq_completed
#print axioms JutilaPrimitiveFunctionalEquation.level_eq_one_of_isPrimitive_eq_one
#print axioms JutilaPrimitiveFunctionalEquation.gammaFactor_ne_zero_on_reflectedLine
#print axioms JutilaPrimitiveFunctionalEquation.primitive_LFunction_functionalEquation
#print axioms JutilaPrimitiveFunctionalEquation.primitive_LFunction_functionalEquation_on_reflectedLine
