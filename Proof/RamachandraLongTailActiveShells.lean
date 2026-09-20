import RamachandraLongTailShellCauchy

/-!
# Exact active-shell threshold for the long reflected tail

The literal mask is retained.  Every dyadic cell whose upper endpoint is at
most `X` vanishes identically, before any norm or mean-value estimate is used.
This is the lower-cutoff fact needed for the scale-sharp geometric summation.
-/

namespace RamachandraLongTailActiveShells

open Complex MeasureTheory
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedReflectedTailInfiniteAssembly
open RamachandraLongTailShellCauchy
open MRTLemma215DyadicPartition

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A shell below the tail threshold is exactly zero. -/
theorem ramachandraReflectedTailDyadicShell_eq_zero_of_upper_le
    (psi : DirichletCharacter ℂ d) {X : ℝ} {z : ℂ} {j : ℕ}
    (hupper : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ X) :
    ramachandraReflectedTailDyadicShell psi X z j = 0 := by
  unfold ramachandraReflectedTailDyadicShell
  apply Finset.sum_eq_zero
  intro n hn
  have hnupperNat : n ≤ 2 ^ (j + 1) := by
    have hn2 := (Finset.mem_Ioc.mp hn).2
    simpa [pow_succ, Nat.mul_comm] using hn2
  have hnupper : (n : ℝ) ≤ X :=
    (by exact_mod_cast hnupperNat : (n : ℝ) ≤ (2 ^ (j + 1) : ℕ)).trans hupper
  rw [if_neg (not_lt.mpr hnupper)]

/-- Consequently the literal long-shell contour integrand vanishes at every
pair of ordinates. -/
theorem longTailShellIntegrand_eq_zero_of_upper_le
    (psi : DirichletCharacter ℂ d) {X sigma t v : ℝ} {j : ℕ}
    (hupper : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ X) :
    longTailShellIntegrand psi X sigma t j v = 0 := by
  unfold longTailShellIntegrand
  rw [ramachandraReflectedTailDyadicShell_eq_zero_of_upper_le psi hupper]
  simp

/-- The integrated shell is exactly zero, so inactive cells contribute no
spurious cost to the primitive family. -/
theorem integral_longTailShell_eq_zero_of_upper_le
    (psi : DirichletCharacter ℂ d) {X sigma t : ℝ} {j : ℕ}
    (hupper : ((2 ^ (j + 1) : ℕ) : ℝ) ≤ X) :
    (∫ v : ℝ, longTailShellIntegrand psi X sigma t j v) = 0 := by
  simp_rw [longTailShellIntegrand_eq_zero_of_upper_le psi hupper]
  simp

end
end RamachandraLongTailActiveShells

#print axioms RamachandraLongTailActiveShells.ramachandraReflectedTailDyadicShell_eq_zero_of_upper_le
