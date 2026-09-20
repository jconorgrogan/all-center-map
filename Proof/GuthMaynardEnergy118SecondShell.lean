import GuthMaynardEnergy118ShellCount

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy118SecondShell
open CGLProofDAG GuthMaynardLemma116 GuthMaynardEnergy118ShellCount

theorem oneSeparated_floor_injective (W : Finset ℝ) (hsep : OneSeparated W) :
    Set.InjOn (fun t : ℝ => ⌊t⌋) W := by
  intro t ht u hu hfloor
  by_contra hne
  have hlow := hsep t ht u hu hne
  have hhigh := abs_sub_lt_one_of_floor_eq hfloor
  linarith

theorem floor_collision_card_eq_card (W : Finset ℝ) (hsep : OneSeparated W) :
    ((W.product W).filter fun p => ⌊p.1⌋ = ⌊p.2⌋).card = W.card := by
  have heq : ((W.product W).filter fun p => ⌊p.1⌋ = ⌊p.2⌋) = W.diag := by
    ext p
    simp only [Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_diag]
    constructor
    · rintro ⟨⟨h1,h2⟩,he⟩
      exact ⟨h1, oneSeparated_floor_injective W hsep h1 h2 he⟩
    · rintro ⟨h1,he⟩
      refine ⟨⟨h1,?_⟩,?_⟩
      · simpa only [← he] using h1
      · rw [he]
  rw [heq]
  simp

/-- Unit difference-shell count for a one-separated sample set. -/
theorem difference_shell_card_le_two_card
    (W : Finset ℝ) (hsep : OneSeparated W) (m : ℤ) :
    ((W.product W).filter fun p => (m : ℝ) ≤ p.1-p.2 ∧
      p.1-p.2 < (m : ℝ)+1).card ≤ 2*W.card := by
  have hh := shell_card_le_two_floor_energy W (fun t => t) m
  rw [floor_collision_card_eq_card W hsep] at hh
  exact hh

end GuthMaynardEnergy118SecondShell
#print axioms GuthMaynardEnergy118SecondShell.difference_shell_card_le_two_card
