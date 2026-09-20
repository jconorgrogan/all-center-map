import MRTLemma215DynamicClassificationV3

/-!
# Source-faithful high packet cells

The complement of a selected Type-dj factor is re-dyadicized exactly.  Cells
whose upper endpoint lies below the complement's literal lower support are
proved zero and removed.  Every surviving cell then has the honest geometry
`(1/2) M^2 <= N`; no stronger `M^2 <= N` claim is inserted.
-/

namespace MRTLemma215DynamicHighPacketsV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215ComplementDyadicV3

noncomputable section

def survivingComplementCells
    (M : ℕ) (complement : List NatDyadicFactor) :
    Finset (Fin (sourceDyadicCount (factorUpperProduct complement))) :=
  Finset.univ.filter fun cell ↦ M ^ 2 ≤ 2 * 2 ^ (cell : ℕ)

/-- A complementary output shell lying wholly below the proved lower support
is the zero arithmetic function. -/
theorem dyadicComplement_eq_zero_of_not_surviving
    (short : NatDyadicFactor) (complement : List NatDyadicFactor)
    (hsquare : short.length ^ 2 ≤ factorLowerProduct complement)
    (cell : Fin (sourceDyadicCount (factorUpperProduct complement)))
    (hcell : cell ∉ survivingComplementCells short.length complement) :
    sourceDyadicArithmetic (factorUpperProduct complement)
      (factorConvolution complement) cell = 0 := by
  have hbelow : 2 * 2 ^ (cell : ℕ) < short.length ^ 2 := by
    simpa [survivingComplementCells] using hcell
  ext n
  change (if 2 ≤ n ∧ n ≤ factorUpperProduct complement ∧
      (n - 1).log2 = (cell : ℕ) then
        factorConvolution complement n else 0) = 0
  split_ifs with hmask
  · have hnCell : n ≤ 2 * 2 ^ (cell : ℕ) := by
      have hmem : n ∈ DeterminantCountWeld.dyadic (2 ^ (cell : ℕ)) := by
        exact (log2_sub_one_eq_iff_mem_Ioc hmask.1).mp hmask.2.2
      exact (Finset.mem_Ioc.mp hmem).2
    have hnLower : n ≤ factorLowerProduct complement := by
      exact hnCell.trans (le_trans (Nat.le_of_lt hbelow) hsquare)
    cases complement with
    | nil =>
        simp [factorLowerProduct] at hsquare hbelow
        exfalso
        nlinarith
    | cons head tail =>
        exact factorConvolution_zero_of_le head tail hnLower
  · rfl

/-- Exact output partition after deleting only cells already proved zero. -/
theorem mul_factorConvolution_eq_sum_survivingDyadicComplement
    (short : NatDyadicFactor)
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (hone : ∀ f ∈ head :: tail, 1 ≤ f.length)
    (hsquare : short.length ^ 2 ≤
      factorLowerProduct (head :: tail)) :
    short.coeff * factorConvolution (head :: tail) =
      ∑ cell ∈ survivingComplementCells short.length (head :: tail),
        short.coeff *
          sourceDyadicArithmetic (factorUpperProduct (head :: tail))
            (factorConvolution (head :: tail)) cell := by
  rw [mul_factorConvolution_eq_sum_dyadicComplement short head tail hone]
  exact (Finset.sum_subset (by simp)
    (fun cell hcell hsurvive => by
      rw [dyadicComplement_eq_zero_of_not_surviving short (head :: tail)
        hsquare cell hsurvive]
      simp)).symm

theorem survivingComplementCell_longLength_two
    {short : NatDyadicFactor} {complement : List NatDyadicFactor}
    (hshort : 2 ≤ short.length)
    {cell : Fin (sourceDyadicCount (factorUpperProduct complement))}
    (hcell : cell ∈ survivingComplementCells short.length complement) :
    2 ≤ 2 ^ (cell : ℕ) := by
  have hgeom : short.length ^ 2 ≤ 2 * 2 ^ (cell : ℕ) := by
    simpa [survivingComplementCells] using hcell
  nlinarith [show 4 ≤ short.length ^ 2 by nlinarith]

/-- Literal scale separation of a surviving output cell. -/
theorem survivingComplementCell_half_square_le
    {short : NatDyadicFactor} {complement : List NatDyadicFactor}
    {cell : Fin (sourceDyadicCount (factorUpperProduct complement))}
    (hcell : cell ∈ survivingComplementCells short.length complement) :
    (1 / 2 : ℝ) * (short.length : ℝ) ^ 2 ≤
      (2 ^ (cell : ℕ) : ℕ) := by
  have hgeom : short.length ^ 2 ≤ 2 * 2 ^ (cell : ℕ) := by
    simpa [survivingComplementCells] using hcell
  have hgeomR : (short.length : ℝ) ^ 2 ≤
      2 * (2 ^ (cell : ℕ) : ℕ) := by
    exact_mod_cast hgeom
  nlinarith

end
end MRTLemma215DynamicHighPacketsV3

#print axioms MRTLemma215DynamicHighPacketsV3.dyadicComplement_eq_zero_of_not_surviving
#print axioms MRTLemma215DynamicHighPacketsV3.mul_factorConvolution_eq_sum_survivingDyadicComplement
#print axioms MRTLemma215DynamicHighPacketsV3.survivingComplementCell_half_square_le
