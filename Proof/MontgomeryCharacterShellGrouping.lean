import CGLProofDAG

/-!
# Common shell extraction across a character family

Montgomery's detector split first chooses a dyadic shell separately for each
character.  Theorem 8.3 must instead see one coefficient sequence, hence one
shell, across the whole character family.  This file proves the exact finite
pigeonhole step and its cardinality cost.  It is entirely deterministic.
-/

namespace MAPMontgomeryCharacterShellGrouping

open scoped BigOperators

noncomputable section

/-- Keep only the fibers whose separately chosen index agrees with `i`. -/
def restrictFamilyByIndex
    {I A : Type*} [DecidableEq A] {r : ℕ}
    (chosen : I → Fin r) (W : I → Finset A) (i : Fin r) (x : I) :
    Finset A :=
  if chosen x = i then W x else ∅

theorem card_restrictFamilyByIndex
    {I A : Type*} [DecidableEq A] {r : ℕ}
    (chosen : I → Fin r) (W : I → Finset A) (i : Fin r) (x : I) :
    (restrictFamilyByIndex chosen W i x).card =
      if chosen x = i then (W x).card else 0 := by
  by_cases h : chosen x = i <;> simp [restrictFamilyByIndex, h]

/-- Summing the index fibers recovers the original family cardinality
exactly, including empty character fibers. -/
theorem sum_index_sum_card_restrictFamilyByIndex
    {I A : Type*} [Fintype I] [DecidableEq A]
    {r : ℕ}
    (chosen : I → Fin r) (W : I → Finset A) :
    ∑ i : Fin r, ∑ x : I,
        (restrictFamilyByIndex chosen W i x).card =
      ∑ x : I, (W x).card := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  calc
    (∑ i : Fin r, (restrictFamilyByIndex chosen W i x).card) =
        (restrictFamilyByIndex chosen W (chosen x) x).card := by
      apply Finset.sum_eq_single (chosen x)
      · intro i hi hne
        have hne' : chosen x ≠ i := Ne.symm hne
        simp [restrictFamilyByIndex, hne']
      · simp
    _ = (W x).card := by simp [restrictFamilyByIndex]

/-- A single shell carries at least a `1/r` share of the total cardinality
after all per-character choices.  This is the missing family-level
pigeonhole between the fixed-character source split and Theorem 8.3. -/
theorem exists_common_character_index
    {I A : Type*} [Fintype I] [DecidableEq A]
    {r : ℕ} (hr : 0 < r)
    (chosen : I → Fin r) (W : I → Finset A) :
    ∃ i : Fin r,
      ∑ x : I, (W x).card ≤
        r * ∑ x : I, (restrictFamilyByIndex chosen W i x).card := by
  classical
  have hpartition :=
    sum_index_sum_card_restrictFamilyByIndex chosen W
  have heq :
      (∑ _i : Fin r, ∑ x : I, (W x).card) ≤
        ∑ i : Fin r,
          r * ∑ x : I, (restrictFamilyByIndex chosen W i x).card := by
    calc
      (∑ _i : Fin r, ∑ x : I, (W x).card) =
          r * ∑ x : I, (W x).card := by simp
      _ = r * ∑ i : Fin r,
          ∑ x : I, (restrictFamilyByIndex chosen W i x).card := by
            rw [hpartition]
      _ ≤ ∑ i : Fin r,
          r * ∑ x : I, (restrictFamilyByIndex chosen W i x).card := by
            rw [Finset.mul_sum]
  obtain ⟨i, -, hi⟩ := Finset.exists_le_of_sum_le
    ⟨⟨0, hr⟩, Finset.mem_univ _⟩ heq
  exact ⟨i, hi⟩

/-- Restricting by a common shell preserves any property inherited by
subsets, in particular one-separation and height bounds. -/
theorem restrictFamilyByIndex_subset
    {I A : Type*} [DecidableEq A] {r : ℕ}
    (chosen : I → Fin r) (W : I → Finset A) (i : Fin r) (x : I) :
    restrictFamilyByIndex chosen W i x ⊆ W x := by
  classical
  by_cases h : chosen x = i
  · simp [restrictFamilyByIndex, h]
  · simp [restrictFamilyByIndex, h]

end
end MAPMontgomeryCharacterShellGrouping

#print axioms MAPMontgomeryCharacterShellGrouping.sum_index_sum_card_restrictFamilyByIndex
#print axioms MAPMontgomeryCharacterShellGrouping.exists_common_character_index
#print axioms MAPMontgomeryCharacterShellGrouping.restrictFamilyByIndex_subset
