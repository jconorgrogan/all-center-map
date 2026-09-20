import RamachandraShiftedReflectedHeadAssembly

/-!
# Exact finite truncation of the shifted reflected tail

Ramachandra truncates `I₁` at a finite reflected-series cap before applying
the dyadic mean square.  This module gives that literal finite object and its
exact unit-plus-shell expansion; no infinite-series interchange is hidden in
the block estimate.
-/

namespace RamachandraShiftedReflectedTailAssembly

open scoped BigOperators LSeries.notation
open Complex
open BHPRamachandraMeanValueFromDyadicAFE
open RamachandraPrimitiveShiftedContourReduction
open RamachandraShiftedReflectedSeries
open MRTLemma215DyadicPartition
open MAPMRTLemma210OrthogonalityReduction
open BHPAllCharacterDyadicBudget
open MontgomeryVaughanFiniteReduction

noncomputable section

/-- The literal `X<n≤Y` reflected truncation used inside `I₁`. -/
def ramachandraReflectedTailTrunc {d : ℕ} [NeZero d]
    (psi : DirichletCharacter ℂ d) (X Y : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊,
    if X < n then ramachandraReflectedTerm psi z n else 0

/-- Coefficient of the finite reflected tail after extracting the character
and the `t` phase. -/
def reflectedTailTruncCoeff
    (X : ℝ) (M : ℕ) (sigma u v : ℝ) (n : ℕ) : ℂ :=
  if X < n ∧ n ≤ M then shiftedReflectedBlockCoeff sigma u v n else 0

def reflectedTailSourceShellCoeff
    (X : ℝ) (M : ℕ) (sigma u v : ℝ)
    (j : Fin (sourceDyadicCount M)) : ℕ → ℂ :=
  sourceDyadicCoeff M (reflectedTailTruncCoeff X M sigma u v) j

def reflectedTailSourceUnitCoeff
    (X : ℝ) (M : ℕ) (sigma u v : ℝ) : ℕ → ℂ :=
  sourceUnitCoeff M (reflectedTailTruncCoeff X M sigma u v)

/-- Exact finite-polynomial realization of the truncated tail. -/
theorem ramachandraReflectedTailTrunc_eq_prefixPolynomial
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X : ℝ) {Y : ℝ} (hY : 0 ≤ Y) (sigma u v t : ℝ) :
    ramachandraReflectedTailTrunc psi X Y
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) =
      twistedFinitePolynomial d (Finset.Icc 1 ⌊Y⌋₊)
        (reflectedTailTruncCoeff X ⌊Y⌋₊ sigma u v) (star psi) (-t) := by
  unfold ramachandraReflectedTailTrunc twistedFinitePolynomial
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
  have hnM : n ≤ ⌊Y⌋₊ := (Finset.mem_Icc.mp hn).2
  by_cases hXn : X < n
  · rw [if_pos hXn]
    rw [reflectedTerm_eq_blockTerm psi hnpos sigma u t v]
    simp [reflectedTailTruncCoeff, hXn, hnM]
  · rw [if_neg hXn]
    simp [reflectedTailTruncCoeff, hXn]

/-- A finite tail shell is represented by the standard dyadic block engine. -/
theorem reflectedTailSourceShellPolynomial_eq_dyadicBlock
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X : ℝ) (M : ℕ) (sigma u v t : ℝ)
    (j : Fin (sourceDyadicCount M)) :
    twistedFinitePolynomial d (Finset.Icc 1 M)
        (reflectedTailSourceShellCoeff X M sigma u v j) (star psi) (-t) =
      ramachandraDyadicBlock d (2 ^ (j : ℕ))
        (reflectedTailSourceShellCoeff X M sigma u v j) true psi t := by
  let S := Finset.Icc 1 M
  let D := dyadicSupport (2 ^ (j : ℕ))
  let U := S ∪ D
  let F : ℕ → ℂ := fun n =>
    (reflectedTailSourceShellCoeff X M sigma u v j n * star psi n) *
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
    unfold F reflectedTailSourceShellCoeff sourceDyadicCoeff
    rw [if_neg]
    · simp
    · intro h
      exact hnM h.2.1
  have houtD : ∀ n ∈ U, n ∉ D → F n = 0 := by
    intro n hnU hnD
    have hsupp := sourceDyadicCoeff_supported M
      (reflectedTailTruncCoeff X M sigma u v) j n hnD
    unfold F reflectedTailSourceShellCoeff
    rw [hsupp]
    simp
  unfold ramachandraDyadicBlock
  simp only [if_true]
  unfold twistedFinitePolynomial
  change (∑ n ∈ S, F n) = ∑ n ∈ D, F n
  calc
    (∑ n ∈ S, F n) = ∑ n ∈ U, F n := Finset.sum_subset hSU houtS
    _ = ∑ n ∈ D, F n := (Finset.sum_subset hDU houtD).symm

/-- Exact unit-plus-dyadic decomposition of the literal finite `I₁` tail. -/
theorem ramachandraReflectedTailTrunc_eq_unit_add_shells
    {d : ℕ} [NeZero d] (psi : DirichletCharacter ℂ d)
    (X : ℝ) {Y : ℝ} (hY : 0 ≤ Y) (sigma u v t : ℝ) :
    ramachandraReflectedTailTrunc psi X Y
        (ramachandraShiftedPoint sigma t + ((u : ℂ) + v * I)) =
      twistedFinitePolynomial d (Finset.Icc 1 ⌊Y⌋₊)
          (reflectedTailSourceUnitCoeff X ⌊Y⌋₊ sigma u v) (star psi) (-t) +
        ∑ j : Fin (sourceDyadicCount ⌊Y⌋₊),
          ramachandraDyadicBlock d (2 ^ (j : ℕ))
            (reflectedTailSourceShellCoeff X ⌊Y⌋₊ sigma u v j) true psi t := by
  rw [ramachandraReflectedTailTrunc_eq_prefixPolynomial psi X hY sigma u v t]
  have hshell (j : Fin (sourceDyadicCount ⌊Y⌋₊)) :
      ramachandraDyadicBlock d (2 ^ (j : ℕ))
          (reflectedTailSourceShellCoeff X ⌊Y⌋₊ sigma u v j) true psi t =
        twistedFinitePolynomial d (Finset.Icc 1 ⌊Y⌋₊)
          (reflectedTailSourceShellCoeff X ⌊Y⌋₊ sigma u v j)
            (star psi) (-t) :=
    (reflectedTailSourceShellPolynomial_eq_dyadicBlock
      psi X ⌊Y⌋₊ sigma u v t j).symm
  simp_rw [hshell]
  unfold twistedFinitePolynomial
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hnrange : 1 ≤ n ∧ n ≤ ⌊Y⌋₊ := Finset.mem_Icc.mp hn
  have hcoeff := unit_add_sum_sourceDyadicCoeff_eq_truncation
    ⌊Y⌋₊ (reflectedTailTruncCoeff X ⌊Y⌋₊ sigma u v) n
  rw [if_pos hnrange] at hcoeff
  unfold reflectedTailSourceUnitCoeff reflectedTailSourceShellCoeff
  rw [← hcoeff, add_mul, add_mul]
  simp only [Finset.sum_mul]

theorem continuous_reflectedTailSourceShellCoeff
    (X : ℝ) (M : ℕ) (sigma u : ℝ)
    (j : Fin (sourceDyadicCount M)) (n : ℕ) :
    Continuous (fun v => reflectedTailSourceShellCoeff X M sigma u v j n) := by
  unfold reflectedTailSourceShellCoeff sourceDyadicCoeff reflectedTailTruncCoeff
  split_ifs
  · exact continuous_shiftedReflectedBlockCoeff sigma u n
  all_goals fun_prop

end
end RamachandraShiftedReflectedTailAssembly

#print axioms RamachandraShiftedReflectedTailAssembly.ramachandraReflectedTailTrunc_eq_unit_add_shells
#print axioms RamachandraShiftedReflectedTailAssembly.continuous_reflectedTailSourceShellCoeff
