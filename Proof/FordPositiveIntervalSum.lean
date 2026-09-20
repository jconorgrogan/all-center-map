import FordSubsetMoment
open scoped BigOperators
open FordSubsetMoment
noncomputable section
namespace FordPositiveIntervalSum
lemma interval_bounded (M : ℕ) : ∀ b ∈ Finset.Icc 1 M, 1 ≤ b ∧ b ≤ M := by simp

def intervalEquiv (M : ℕ) : BoundedNat (Finset.Icc 1 M) ≃ Fin M where
  toFun := toFinM _ M (interval_bounded M)
  invFun := fun i => ⟨i.val+1, by simp⟩
  left_inv := by
    intro b
    apply Subtype.ext
    exact toFinM_val_add_one _ M (interval_bounded M) b
  right_inv := by
    intro i
    apply Fin.ext
    simp [toFinM]

lemma sum_interval_eq {α : Type*} [AddCommMonoid α] (M : ℕ) (f : ℕ → α) :
    (∑ b : BoundedNat (Finset.Icc 1 M), f b.val) =
      ∑ i : Fin M, f (i.val+1) := by
  apply Fintype.sum_equiv (intervalEquiv M)
  intro b
  rw [show ((intervalEquiv M) b).val+1 = b.val from
    toFinM_val_add_one _ M (interval_bounded M) b]

lemma card_interval (M : ℕ) : (Finset.Icc 1 M).card = M := by simp
end FordPositiveIntervalSum
#print axioms FordPositiveIntervalSum.sum_interval_eq
