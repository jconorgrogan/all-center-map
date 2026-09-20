import FordBoundarySlotSymmetry

open scoped BigOperators
open FordBoundaryCountGeometry FordBoundarySlotSymmetry
noncomputable section
namespace FordBoundaryCollisionGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

/-- The source solutions whose left or right word repeats a slot. -/
def CollisionBad (f : A → G) (g : U → G) (n : ℕ) :=
  {r : EnergyZero f g n //
    (¬ Function.Injective r.1.1.2) ∨ (¬ Function.Injective r.1.2.2)}

/-- A collision pinned to the first two left slots. -/
def CollisionPinned (f : A → G) (g : U → G) (s : ℕ) :=
  {r : EnergyZero f g (s + 2) //
    r.1.1.2 (0 : Fin (s + 2)) = r.1.1.2 (1 : Fin (s + 2))}

instance (f : A → G) (g : U → G) (n : ℕ) : Fintype (CollisionBad f g n) := by
  classical unfold CollisionBad; infer_instance
instance (f : A → G) (g : U → G) (s : ℕ) : Fintype (CollisionPinned f g s) := by
  classical unfold CollisionPinned; infer_instance

def CollisionPair (f : A → G) (g : U → G) (n : ℕ)
    (side : Bool) (i j : Fin n) :=
  {r : EnergyZero f g n //
    (if side then r.1.2.2 i = r.1.2.2 j else r.1.1.2 i = r.1.1.2 j)}

instance (f : A → G) (g : U → G) (n : ℕ) (side : Bool) (i j : Fin n) :
    Fintype (CollisionPair f g n side i j) := by
  classical unfold CollisionPair; infer_instance

/-- Canonical first two slots, available when `2 ≤ n`. -/
def zeroFin {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨0, by omega⟩
def oneFin {n : ℕ} (hn : 2 ≤ n) : Fin n := ⟨1, by omega⟩

/-- A permutation sending 0 to `i` and 1 to `j` when `i ≠ j`. -/
def sendTwo {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) : Equiv.Perm (Fin n) := by
  let a : Equiv.Perm (Fin n) := Equiv.swap (zeroFin hn) i
  let b : Equiv.Perm (Fin n) := Equiv.swap (oneFin hn) (a.symm j)
  exact b.trans a

lemma sendTwo_zero {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    sendTwo hn i j hij (zeroFin hn) = i := by
  dsimp [sendTwo]
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs with h0 h1 <;> simp_all [zeroFin, oneFin] <;> omega

lemma sendTwo_one {n : ℕ} (hn : 2 ≤ n) (i j : Fin n) (hij : i ≠ j) :
    sendTwo hn i j hij (oneFin hn) = j := by
  dsimp [sendTwo]
  simp only [Equiv.trans_apply, Equiv.swap_apply_def]
  split_ifs with h0 h1 <;> simp_all [zeroFin, oneFin] <;> omega

end FordBoundaryCollisionGeometry

namespace FordBoundaryCollisionGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

def collisionPair_toPinned
    (f : A → G) (g : U → G) (s : ℕ) (side : Bool)
    (i j : Fin (s + 2)) (hij : i ≠ j)
    (r : CollisionPair f g (s + 2) side i j) :
    CollisionPinned f g s := by
  let pi := sendTwo (n := s + 2) (by omega) i j hij
  let z : EnergyZero f g (s + 2) :=
    if side then swapSides f g r.1 else r.1
  refine ⟨reindex f g pi z, ?_⟩
  cases side with
  | false =>
      change r.1.1.1.2 (pi (zeroFin (by omega))) = r.1.1.1.2 (pi (oneFin (by omega)))
      rw [sendTwo_zero, sendTwo_one]
      exact r.2
  | true =>
      change r.1.1.2.2 (pi (zeroFin (by omega))) = r.1.1.2.2 (pi (oneFin (by omega)))
      rw [sendTwo_zero, sendTwo_one]
      exact r.2

lemma collisionPair_toPinned_injective
    (f : A → G) (g : U → G) (s : ℕ) (side : Bool)
    (i j : Fin (s + 2)) (hij : i ≠ j) :
    Function.Injective (fun r : CollisionPair f g (s + 2) side i j =>
      collisionPair_toPinned f g s side i j hij r) := by
  cases side with
  | false =>
      intro r t h
      apply Subtype.ext
      apply reindex_injective f g (sendTwo (n := s + 2) (by omega) i j hij)
      have hh := congrArg Subtype.val h
      dsimp [collisionPair_toPinned] at hh
      change reindex f g (sendTwo (n := s + 2) (by omega) i j hij) r.1 =
        reindex f g (sendTwo (n := s + 2) (by omega) i j hij) t.1 at hh
      exact hh
  | true =>
      intro r t h
      apply Subtype.ext
      apply swapSides_injective f g
      apply reindex_injective f g (sendTwo (n := s + 2) (by omega) i j hij)
      have hh := congrArg Subtype.val h
      dsimp [collisionPair_toPinned] at hh
      change reindex f g (sendTwo (n := s + 2) (by omega) i j hij) (swapSides f g r.1) =
        reindex f g (sendTwo (n := s + 2) (by omega) i j hij) (swapSides f g t.1) at hh
      exact hh

lemma collisionPair_card_le_pinned
    (f : A → G) (g : U → G) (s : ℕ) (side : Bool)
    (i j : Fin (s + 2)) (hij : i ≠ j) :
    Fintype.card (CollisionPair f g (s + 2) side i j) ≤
      Fintype.card (CollisionPinned f g s) := by
  exact Fintype.card_le_of_injective
    (collisionPair_toPinned f g s side i j hij)
    (collisionPair_toPinned_injective f g s side i j hij)

end FordBoundaryCollisionGeometry

namespace FordBoundaryCollisionGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

lemma exists_collision {X Y : Type*} (w : X → Y) (hn : ¬ Function.Injective w) :
    ∃ i j, i ≠ j ∧ w i = w j := by
  classical
  by_contra h
  push_neg at h
  apply hn
  intro i j hij
  by_contra hne
  exact h i j hne hij

/-- Witnesses for a repeated slot, retaining the side and both distinct indices. -/
def CollisionWitness (f : A → G) (g : U → G) (s : ℕ) :=
  Sigma (fun side : Bool =>
    Sigma (fun ij : {p : Fin (s + 2) × Fin (s + 2) // p.1 ≠ p.2} =>
      CollisionPair f g (s + 2) side ij.1.1 ij.1.2))

instance (f : A → G) (g : U → G) (s : ℕ) : Fintype (CollisionWitness f g s) := by
  classical unfold CollisionWitness; infer_instance

/-- Every bad source has a chosen collision witness. -/
lemma exists_badWitness (f : A → G) (g : U → G) (s : ℕ)
    (r : CollisionBad f g (s + 2)) :
    ∃ w : CollisionWitness f g s, w.2.2.1 = r.1 := by
  classical
  by_cases hL : ¬ Function.Injective r.1.1.1.2
  · let hw := exists_collision r.1.1.1.2 hL
    let i := Classical.choose hw
    let hwj := Classical.choose_spec hw
    let j := Classical.choose hwj
    let hp := Classical.choose_spec hwj
    exact ⟨⟨false, ⟨⟨i,j⟩, hp.1⟩, ⟨r.1, hp.2⟩⟩, rfl⟩
  · have hR : ¬ Function.Injective r.1.1.2.2 := Or.resolve_left r.2 hL
    let hw := exists_collision r.1.1.2.2 hR
    let i := Classical.choose hw
    let hwj := Classical.choose_spec hw
    let j := Classical.choose hwj
    let hp := Classical.choose_spec hwj
    exact ⟨⟨true, ⟨⟨i,j⟩, hp.1⟩, ⟨r.1, hp.2⟩⟩, rfl⟩

noncomputable def badToWitness (f : A → G) (g : U → G) (s : ℕ) :
    CollisionBad f g (s + 2) → CollisionWitness f g s :=
  fun r => Classical.choose (exists_badWitness f g s r)

lemma badToWitness_source (f : A → G) (g : U → G) (s : ℕ)
    (r : CollisionBad f g (s + 2)) :
    (badToWitness f g s r).2.2.1 = r.1 :=
  Classical.choose_spec (exists_badWitness f g s r)

lemma badToWitness_injective (f : A → G) (g : U → G) (s : ℕ) :
    Function.Injective (badToWitness f g s) := by
  intro r t h
  apply Subtype.ext
  have hh := congrArg (fun z : CollisionWitness f g s => z.2.2.1) h
  change (badToWitness f g s r).2.2.1 = (badToWitness f g s t).2.2.1 at hh
  rw [badToWitness_source f g s r, badToWitness_source f g s t] at hh
  exact hh

end FordBoundaryCollisionGeometry

namespace FordBoundaryCollisionGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

lemma pairIndex_card_le (s : ℕ) :
    Fintype.card {p : Fin (s + 2) × Fin (s + 2) // p.1 ≠ p.2} ≤
      (s + 2) * (s + 2) := by
  let val : {p : Fin (s + 2) × Fin (s + 2) // p.1 ≠ p.2} →
      Fin (s + 2) × Fin (s + 2) := Subtype.val
  have hi : Function.Injective val := Subtype.val_injective
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (Fintype.card_le_of_injective val hi)

lemma collisionWitness_card_le
    (f : A → G) (g : U → G) (s : ℕ) :
    Fintype.card (CollisionWitness f g s) ≤
      2 * (s + 2) * (s + 2) * Fintype.card (CollisionPinned f g s) := by
  let pin : ℕ := Fintype.card (CollisionPinned f g s)
  let I := {p : Fin (s + 2) × Fin (s + 2) // p.1 ≠ p.2}
  have hpair : ∀ (side : Bool) (ij : I),
      Fintype.card (CollisionPair f g (s + 2) side ij.1.1 ij.1.2) ≤ pin := by
    intro side ij
    dsimp [pin]
    exact collisionPair_card_le_pinned f g s side ij.1.1 ij.1.2 ij.2
  calc
    Fintype.card (CollisionWitness f g s) =
        ∑ side : Bool, ∑ ij : I,
          Fintype.card (CollisionPair f g (s + 2) side ij.1.1 ij.1.2) := by
      change Fintype.card (Sigma (fun side : Bool =>
        Sigma (fun ij : I => CollisionPair f g (s + 2) side ij.1.1 ij.1.2))) = _
      simp_rw [Fintype.card_sigma]
    _ ≤ ∑ side : Bool, ∑ _ij : I, pin := by
      apply Finset.sum_le_sum
      intro side hside
      apply Finset.sum_le_sum
      intro ij hij
      exact hpair side ij
    _ = 2 * Fintype.card I * pin := by
      simp [Finset.sum_const, Fintype.card_bool, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ 2 * (s + 2) * (s + 2) * pin := by
      have hI0 := pairIndex_card_le s
      change Fintype.card {p : Fin (s + 2) × Fin (s + 2) // p.1 ≠ p.2} ≤
        (s + 2) * (s + 2) at hI0
      have hI : Fintype.card I ≤ (s + 2) * (s + 2) := by exact hI0
      calc
        2 * Fintype.card I * pin ≤ (2 * ((s + 2) * (s + 2))) * pin :=
          Nat.mul_le_mul_right pin (Nat.mul_le_mul_left 2 hI)
        _ = 2 * (s + 2) * (s + 2) * pin := by simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

lemma collisionBad_card_le
    (f : A → G) (g : U → G) (s : ℕ) :
    Fintype.card (CollisionBad f g (s + 2)) ≤
      2 * (s + 2) * (s + 2) * Fintype.card (CollisionPinned f g s) := by
  calc
    Fintype.card (CollisionBad f g (s + 2)) ≤
        Fintype.card (CollisionWitness f g s) :=
      Fintype.card_le_of_injective (badToWitness f g s) (badToWitness_injective f g s)
    _ ≤ _ := collisionWitness_card_le f g s

end FordBoundaryCollisionGeometry

namespace FordBoundaryCollisionGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

/-- The complementary collision-free source carrier. -/
def CollisionGood (f : A → G) (g : U → G) (n : ℕ) :=
  {r : EnergyZero f g n //
    Function.Injective r.1.1.2 ∧ Function.Injective r.1.2.2}

instance (f : A → G) (g : U → G) (n : ℕ) : Fintype (CollisionGood f g n) := by
  classical unfold CollisionGood; infer_instance

lemma good_of_not_bad (f : A → G) (g : U → G) (n : ℕ)
    (r : EnergyZero f g n)
    (h : ¬ ((¬ Function.Injective r.1.1.2) ∨ (¬ Function.Injective r.1.2.2))) :
    Function.Injective r.1.1.2 ∧ Function.Injective r.1.2.2 := by
  constructor
  · by_contra hn
    exact h (Or.inl hn)
  · by_contra hn
    exact h (Or.inr hn)

lemma collision_card_partition (f : A → G) (g : U → G) (n : ℕ) :
    Fintype.card (EnergyZero f g n) =
      Fintype.card (CollisionBad f g n) + Fintype.card (CollisionGood f g n) := by
  classical
  let E : EnergyZero f g n ≃ CollisionBad f g n ⊕ CollisionGood f g n :=
    { toFun := fun r =>
        if h : (¬ Function.Injective r.1.1.2) ∨ (¬ Function.Injective r.1.2.2) then
          Sum.inl ⟨r, h⟩
        else
          Sum.inr ⟨r, good_of_not_bad f g n r h⟩
      invFun := fun z => match z with | Sum.inl r => r.1 | Sum.inr r => r.1
      left_inv := by
        intro r
        dsimp
        split_ifs <;> rfl
      right_inv := by
        intro z
        cases z with
        | inl r =>
            dsimp
            rw [dif_pos r.2]
            rfl
        | inr r =>
            dsimp
            rw [dif_neg]
            · rfl
            · intro hbad
              exact hbad.elim (fun hn => hn r.2.1) (fun hn => hn r.2.2)
    }
  simpa only [Fintype.card_sum] using Fintype.card_congr E

end FordBoundaryCollisionGeometry

#print axioms FordBoundaryCollisionGeometry.collisionBad_card_le
#print axioms FordBoundaryCollisionGeometry.collision_card_partition
