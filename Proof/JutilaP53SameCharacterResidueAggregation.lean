import JutilaP53KernelSourceForm

/-!
# Same-character aggregation of the p.53 principal residues

The principal quotient is selected by `bar chi_i * chi_j = 1`.  This file
rewrites that mask exactly as equality of the two row characters and records
the deterministic aggregation bound.  It deliberately does not identify
same-character pairs with identical rows: controlling the remaining zeros of
a fixed character is the genuine packing input.
-/

namespace MAPJutilaP53SameCharacterResidueAggregation

open scoped BigOperators
open Complex
open MAPJutilaP53AggregateCorrelationLeaf
open MAPJutilaP53KernelSourceForm

noncomputable section

local instance {q : ℕ} : DecidableEq (DirichletCharacter ℂ q) := Classical.decEq _

def p53PrincipalPairSum {q : ℕ}
    (rows : Finset (JutilaP53Row q))
    (C : JutilaP53Row q → JutilaP53Row q → ℂ) : ℂ :=
  ∑ i ∈ rows, ∑ j ∈ rows,
    if jutilaP53PairCharacter i j = 1 then C i j else 0

def p53SameCharacterPairSum {q : ℕ}
    (rows : Finset (JutilaP53Row q))
    (C : JutilaP53Row q → JutilaP53Row q → ℂ) : ℂ :=
  ∑ i ∈ rows, ∑ j ∈ rows,
    if i.character = j.character then C i j else 0

/-- The principal-residue mask is literally the same-character mask. -/
theorem p53PrincipalPairSum_eq_sameCharacter
    {q : ℕ} (rows : Finset (JutilaP53Row q))
    (C : JutilaP53Row q → JutilaP53Row q → ℂ) :
    p53PrincipalPairSum rows C = p53SameCharacterPairSum rows C := by
  unfold p53PrincipalPairSum p53SameCharacterPairSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : jutilaP53PairCharacter i j = 1
  · have hc : i.character = j.character :=
      (pairCharacter_eq_one_iff i j).mp h
    simp [h, hc]
  · have hc : i.character ≠ j.character := by
      intro hij
      exact h ((pairCharacter_eq_one_iff i j).mpr hij)
    simp [h, hc]

/-- Once each fixed-character fiber has budget `F`, all principal residues
cost at most `F * #rows`.  This is the exact aggregation step behind the
linear diagonal term on p.53. -/
theorem norm_p53PrincipalPairSum_le_card_mul
    {q : ℕ} (rows : Finset (JutilaP53Row q))
    (C : JutilaP53Row q → JutilaP53Row q → ℂ) (F : ℝ)
    (hfiber : ∀ i ∈ rows,
      ‖∑ j ∈ rows, if i.character = j.character then C i j else 0‖ ≤ F) :
    ‖p53PrincipalPairSum rows C‖ ≤ (rows.card : ℝ) * F := by
  rw [p53PrincipalPairSum_eq_sameCharacter]
  unfold p53SameCharacterPairSum
  calc
    ‖∑ i ∈ rows, ∑ j ∈ rows,
        if i.character = j.character then C i j else 0‖ ≤
      ∑ i ∈ rows, ‖∑ j ∈ rows,
        if i.character = j.character then C i j else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ rows, F := by
      apply Finset.sum_le_sum
      intro i hi
      exact hfiber i hi
    _ = (rows.card : ℝ) * F := by
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]

end

end MAPJutilaP53SameCharacterResidueAggregation

#print axioms MAPJutilaP53SameCharacterResidueAggregation.p53PrincipalPairSum_eq_sameCharacter
#print axioms MAPJutilaP53SameCharacterResidueAggregation.norm_p53PrincipalPairSum_le_card_mul
