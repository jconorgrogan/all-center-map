import FordBoundaryCrossFourier
import FordBoundaryCountGeometry

open scoped BigOperators ZMod ComplexConjugate
open FordBoundaryCountGeometry
open MAPFordBoundaryCrossFourier MAPFordP16FiniteFourierBridge

noncomputable section
namespace FordCollisionPinnedBound

variable {A U : Type*} [Fintype A] [Fintype U]
variable {L k s : ℕ} [NeZero L]

abbrev CollisionPinned (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :=
  {r : EnergyZero f g (s+2) // r.1.1.2 0 = r.1.1.2 1}

abbrev PinCross (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :=
  {r : ((A × U) × (Fin s → U)) × (A × (Fin (s+2) → U)) //
    (fun j => f r.1.1.1 j + g r.1.1.2 j + g r.1.1.2 j +
      ∑ i : Fin s, g (r.1.2 i) j) =
    (fun j => f r.2.1 j + ∑ i : Fin (s+2), g (r.2.2 i) j)}

instance collisionPinnedFintype (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :
    Fintype (CollisionPinned f g s) := by
  classical
  unfold CollisionPinned
  infer_instance

instance pinCrossFintype (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :
    Fintype (PinCross f g s) := by
  classical
  unfold PinCross
  infer_instance

end FordCollisionPinnedBound


namespace FordCollisionPinnedBound

private def collisionPinnedEquivDraft (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :
    CollisionPinned f g s ≃ PinCross f g s := by
  let toFun : CollisionPinned f g s → PinCross f g s := fun r =>
    let st := r.1.1
    let left := st.1
    let right := st.2
    let a := left.1
    let u := left.2
    let b := right.1
    let v := right.2
    let e := u 0
    let rest : Fin s → U := fun i => u i.succ.succ
    ⟨(((a, e), rest), (b, v)), by
      funext j
      have hh := congrFun r.1.2 j
      have he : u 0 = u 1 := r.2
      have hpin : r.1.1.1.2 (Fin.succ 0) = r.1.1.1.2 0 := he.symm
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh ⊢
      rw [hpin] at hh
      simpa [st, left, right, a, u, b, v, e, rest, add_assoc] using hh⟩
  let invFun : PinCross f g s → CollisionPinned f g s := fun r =>
    let left := r.1.1
    let right := r.1.2
    let a := left.1.1
    let e := left.1.2
    let rest := left.2
    let b := right.1
    let v := right.2
    let u : Fin (s+2) → U := Fin.cons e (Fin.cons e rest)
    ⟨⟨((a, u), (b, v)), by
      funext j
      have hh := congrFun r.2 j
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at hh ⊢
      simpa [left, right, a, e, rest, b, v, u, add_assoc] using hh⟩, by rfl⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext
          · rfl
          · funext i
            let u := r.1.1.1.2
            refine Fin.cases ?_ (fun i => ?_) i
            · rfl
            · refine Fin.cases ?_ (fun i => ?_) i
              · exact r.2
              · rfl
        · rfl
      right_inv := by
        intro r
        apply Subtype.ext
        rfl }

end FordCollisionPinnedBound

namespace FordCollisionPinnedBound

variable {A U : Type*} [Fintype A] [Fintype U]
variable {L k s : ℕ} [NeZero L]

theorem collisionPinned_card_eq_pinCross
    (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ) :
    Fintype.card (CollisionPinned f g s) = Fintype.card (PinCross f g s) :=
  Fintype.card_congr (collisionPinnedEquivDraft f g s)

end FordCollisionPinnedBound

#print axioms FordCollisionPinnedBound.collisionPinned_card_eq_pinCross

