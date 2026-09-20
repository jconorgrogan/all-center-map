import Mathlib

open scoped BigOperators
noncomputable section
namespace MAPFordFiniteCoverSelection

/-- A finite cover supplies one literal mask containing at least the average
number of points. Overlap between masks is allowed. -/
theorem exists_large_mask
    {A I : Type*} [Fintype A] [Fintype I] [Nonempty I]
    (mask : I → A → Prop) (hcover : ∀ a, ∃ i, mask i a) :
    ∃ i : I, Fintype.card A ≤ Fintype.card I *
      Nat.card {a : A // mask i a} := by
  classical
  simp only [Nat.card_eq_fintype_card]
  let f : A → (i : I) × {a : A // mask i a} := fun a =>
    ⟨Classical.choose (hcover a), ⟨a, Classical.choose_spec (hcover a)⟩⟩
  have hinj : Function.Injective f := by
    intro a b h
    exact congrArg (fun t : (i : I) × {a : A // mask i a} => t.2.1) h
  have hc := Fintype.card_le_of_injective f hinj
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset I) (fun i => Fintype.card {a : A // mask i a})
    Finset.univ_nonempty
  refine ⟨i, hc.trans ?_⟩
  rw [Fintype.card_sigma]
  calc
    (∑ j : I, Fintype.card {a : A // mask j a}) ≤
        ∑ _j : I, Fintype.card {a : A // mask i a} := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmax j hj
    _ = _ := by simp [Nat.mul_comm]

end MAPFordFiniteCoverSelection
#print axioms MAPFordFiniteCoverSelection.exists_large_mask
