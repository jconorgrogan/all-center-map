import FordClassEnergyMoment

open scoped BigOperators
open FordBoundaryCountGeometry FordClassEnergyMoment

noncomputable section
namespace FordClassEnergyInjective

variable {A U C : Type*} [Fintype A] [Fintype U] [Fintype C] {k : ℕ}

/-- If each class contains at most one source point, the class count is
exactly the fully aligned diagonal, including empty alphabets and n=0. -/
def injectiveClassEquiv
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (hc : Function.Injective cls) (n : ℕ) :
    ClassEnergyZero f g cls n ≃ BaseZero f × (Fin n → U) where
  toFun r := (⟨(r.1.1.1.1, r.1.1.2.1), by
    have hw : r.1.1.1.2 = r.1.1.2.2 := funext (fun i => hc (r.2 i))
    have he := r.1.2
    rw [hw] at he
    exact add_right_cancel he⟩, r.1.1.1.2)
  invFun r := ⟨⟨((r.1.1.1, r.2), (r.1.1.2, r.2)), by
    change f r.1.1.1 + ∑ i, g (r.2 i) = f r.1.1.2 + ∑ i, g (r.2 i)
    rw [r.1.2]⟩, fun _ => rfl⟩
  left_inv r := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · exact funext (fun i => hc (r.2 i))
  right_inv r := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · rfl

theorem card_classEnergy_of_injective
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (cls : U → C)
    (hc : Function.Injective cls) (n : ℕ) :
    Fintype.card (ClassEnergyZero f g cls n) =
      Fintype.card (BaseZero f) * Fintype.card U ^ n := by
  simpa using Fintype.card_congr (injectiveClassEquiv f g cls hc n)

end FordClassEnergyInjective

#print axioms FordClassEnergyInjective.injectiveClassEquiv
#print axioms FordClassEnergyInjective.card_classEnergy_of_injective
