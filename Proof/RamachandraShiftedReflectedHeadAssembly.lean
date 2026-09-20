import RamachandraShiftedHeadFiniteContour
import RamachandraShiftedReflectedBlockBudget
import MRTLemma215DyadicPartition

/-!
# Exact source-dyadic assembly of Ramachandra's shifted reflected head

The `I₂` contour contains the finite reflected Dirichlet polynomial `n ≤ X`.
This file partitions that literal polynomial into the unit coefficient and the
exact source dyadic cells, without replacing the continuous Mellin ordinate.
-/

namespace RamachandraShiftedReflectedHeadAssembly

open scoped BigOperators LSeries.notation
open Complex
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedReflectedSeries
open RamachandraShiftedHeadFiniteContour
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction
open BHPAllCharacterDyadicBudget

noncomputable section

/-- The exact truncated source shell in the reflected head. -/
def reflectedHeadSourceShellCoeff
    (M : ℕ) (sigma u v : ℝ)
    (j : Fin (sourceDyadicCount M)) : ℕ → ℂ :=
  sourceDyadicCoeff M (shiftedReflectedBlockCoeff sigma u v) j

/-- The unit coefficient in the reflected head. -/
def reflectedHeadSourceUnitCoeff
    (M : ℕ) (sigma u v : ℝ) : ℕ → ℂ :=
  sourceUnitCoeff M (shiftedReflectedBlockCoeff sigma u v)

/-- A truncated reflected source shell has exactly the same polynomial as its
ambient dyadic support. -/
theorem reflectedHeadSourceShellPolynomial_eq_dyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (M : ℕ) (sigma u v t : ℝ) (j : Fin (sourceDyadicCount M)) :
    twistedFinitePolynomial d (Finset.Icc 1 M)
        (reflectedHeadSourceShellCoeff M sigma u v j) (star psi) (-t) =
      ramachandraDyadicBlock d (2 ^ (j : ℕ))
        (reflectedHeadSourceShellCoeff M sigma u v j) true psi t := by
  let S := Finset.Icc 1 M
  let D := dyadicSupport (2 ^ (j : ℕ))
  let U := S ∪ D
  let F : ℕ → ℂ := fun n =>
    (reflectedHeadSourceShellCoeff M sigma u v j n * star psi n) *
      twistedPhase n (-t)
  have hSU : S ⊆ U := Finset.subset_union_left
  have hDU : D ⊆ U := Finset.subset_union_right
  have houtS : ∀ n ∈ U, n ∉ S → F n = 0 := by
    intro n hnU hnS
    have hnD : n ∈ D := by
      rcases Finset.mem_union.mp hnU with hn | hn
      · exact (hnS hn).elim
      · exact hn
    have hnpos : 1 ≤ n := by
      have h := Finset.mem_Ioc.mp hnD
      omega
    have hnM : ¬ n ≤ M := by
      intro h
      exact hnS (Finset.mem_Icc.mpr ⟨hnpos, h⟩)
    unfold F reflectedHeadSourceShellCoeff sourceDyadicCoeff
    rw [if_neg]
    · simp
    · intro h
      exact hnM h.2.1
  have houtD : ∀ n ∈ U, n ∉ D → F n = 0 := by
    intro n hnU hnD
    have hsupp := sourceDyadicCoeff_supported M
      (shiftedReflectedBlockCoeff sigma u v) j n hnD
    unfold F reflectedHeadSourceShellCoeff
    rw [hsupp]
    simp
  unfold ramachandraDyadicBlock
  simp only [if_true]
  unfold twistedFinitePolynomial
  change (∑ n ∈ S, F n) = ∑ n ∈ D, F n
  calc
    (∑ n ∈ S, F n) = ∑ n ∈ U, F n :=
      Finset.sum_subset hSU houtS
    _ = ∑ n ∈ D, F n := (Finset.sum_subset hDU houtD).symm

/-- The literal finite head is the reflected polynomial on `[1,floor X]`. -/
theorem ramachandraReflectedHead_eq_prefixPolynomial
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 0 ≤ X) (sigma u v t : ℝ) :
    ramachandraReflectedHead psi X
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) =
      twistedFinitePolynomial d (Finset.Icc 1 ⌊X⌋₊)
        (shiftedReflectedBlockCoeff sigma u v) (star psi) (-t) := by
  rw [ramachandraReflectedHead_eq_finset psi hX]
  let M : ℕ := ⌊X⌋₊
  let R := Finset.range (M + 1)
  let S := Finset.Icc 1 M
  have hSR : S ⊆ R := by
    intro n hn
    exact Finset.mem_range.mpr (by
      have h := Finset.mem_Icc.mp hn
      omega)
  have hout : ∀ n ∈ R, n ∉ S →
      ramachandraReflectedTerm psi
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) n = 0 := by
    intro n hnR hnS
    have hnle : n ≤ M := by
      have := Finset.mem_range.mp hnR
      omega
    have hn0 : n = 0 := by
      by_contra hn0
      exact hnS (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnle⟩)
    subst n
    simp [ramachandraReflectedTerm, LSeries.term_zero]
  change (∑ n ∈ R, ramachandraReflectedTerm psi
      (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) n) = _
  rw [← Finset.sum_subset hSR hout]
  unfold twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  exact reflectedTerm_eq_blockTerm psi
    (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1) sigma u t v

/-- Exact unit-plus-dyadic decomposition of the reflected head. -/
theorem ramachandraReflectedHead_eq_unit_add_shells
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    {X : ℝ} (hX : 0 ≤ X) (sigma u v t : ℝ) :
    ramachandraReflectedHead psi X
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) =
      twistedFinitePolynomial d (Finset.Icc 1 ⌊X⌋₊)
          (reflectedHeadSourceUnitCoeff ⌊X⌋₊ sigma u v) (star psi) (-t) +
        ∑ j : Fin (sourceDyadicCount ⌊X⌋₊),
          ramachandraDyadicBlock d (2 ^ (j : ℕ))
            (reflectedHeadSourceShellCoeff ⌊X⌋₊ sigma u v j) true psi t := by
  rw [ramachandraReflectedHead_eq_prefixPolynomial psi hX sigma u v t]
  have hshell (j : Fin (sourceDyadicCount ⌊X⌋₊)) :
      ramachandraDyadicBlock d (2 ^ (j : ℕ))
          (reflectedHeadSourceShellCoeff ⌊X⌋₊ sigma u v j) true psi t =
        twistedFinitePolynomial d (Finset.Icc 1 ⌊X⌋₊)
          (reflectedHeadSourceShellCoeff ⌊X⌋₊ sigma u v j)
            (star psi) (-t) := by
    exact (reflectedHeadSourceShellPolynomial_eq_dyadicBlock
      psi ⌊X⌋₊ sigma u v t j).symm
  simp_rw [hshell]
  unfold twistedFinitePolynomial
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnrange : 1 ≤ n ∧ n ≤ ⌊X⌋₊ := Finset.mem_Icc.mp hn
  have hcoeff := unit_add_sum_sourceDyadicCoeff_eq_truncation
    ⌊X⌋₊ (shiftedReflectedBlockCoeff sigma u v) n
  rw [if_pos hnrange] at hcoeff
  unfold reflectedHeadSourceUnitCoeff reflectedHeadSourceShellCoeff
  rw [← hcoeff, add_mul, add_mul]
  simp only [Finset.sum_mul]

/-- The reflected source-shell coefficient remains continuous in the exact
Mellin ordinate. -/
theorem continuous_reflectedHeadSourceShellCoeff
    (M : ℕ) (sigma u : ℝ) (j : Fin (sourceDyadicCount M)) (n : ℕ) :
    Continuous (fun v => reflectedHeadSourceShellCoeff M sigma u v j n) := by
  unfold reflectedHeadSourceShellCoeff sourceDyadicCoeff
  split_ifs
  · exact continuous_shiftedReflectedBlockCoeff sigma u n
  · exact continuous_const

end
end RamachandraShiftedReflectedHeadAssembly

#print axioms RamachandraShiftedReflectedHeadAssembly.ramachandraReflectedHead_eq_unit_add_shells
#print axioms RamachandraShiftedReflectedHeadAssembly.continuous_reflectedHeadSourceShellCoeff
