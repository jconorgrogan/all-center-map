import FordDifferenceDominance
import FordCompleteSystemMoment

open scoped BigOperators
noncomputable section

namespace FordSubsetMoment

abbrev BoundedNat (B : Finset ℕ) := {b : ℕ // b ∈ B}

def toFinM (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) (b : BoundedNat B) : Fin M :=
  ⟨b.val - 1, by
    have hb := (hB b.val b.property).2
    have hbpos := (hB b.val b.property).1
    omega⟩

lemma toFinM_val_add_one (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) (b : BoundedNat B) :
    (toFinM B M hB b).val + 1 = b.val := by
  dsimp [toFinM]
  exact Nat.sub_add_cancel (hB b.val b.property).1

lemma toFinM_injective (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    Function.Injective (toFinM B M hB) := by
  intro a b hab
  apply Subtype.ext
  have ha := (hB a.val a.property).1
  have hb := (hB b.val b.property).1
  have hv := congrArg Fin.val hab
  dsimp [toFinM] at hv
  omega

def mapTuple (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M)
    {s : ℕ} (x : Fin s → BoundedNat B) : Fin s → Fin M :=
  fun i => toFinM B M hB (x i)

lemma mapTuple_injective (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {s : ℕ} :
    Function.Injective (mapTuple B M hB (s := s)) := by
  intro x y hxy
  funext i
  apply toFinM_injective B M hB
  exact congrFun hxy i

def subsetPowerEq (B : Finset ℕ) (s k : ℕ)
    (xy : (Fin s → BoundedNat B) × (Fin s → BoundedNat B)) : Prop :=
  ∀ j ∈ Finset.Icc 1 k,
    (∑ i : Fin s, (xy.1 i).val ^ j) =
      ∑ i : Fin s, (xy.2 i).val ^ j

def subsetMoment (B : Finset ℕ) (s k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun xy :
    (Fin s → BoundedNat B) × (Fin s → BoundedNat B) =>
      subsetPowerEq B s k xy)).card

def mapPair (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {s : ℕ}
    (xy : (Fin s → BoundedNat B) × (Fin s → BoundedNat B)) :
    (Fin s → Fin M) × (Fin s → Fin M) :=
  (mapTuple B M hB xy.1, mapTuple B M hB xy.2)

lemma mapPair_injective (B : Finset ℕ) (M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) {s : ℕ} :
    Function.Injective (mapPair B M hB (s := s)) := by
  intro xy yz hxy
  apply Prod.ext
  · apply mapTuple_injective B M hB
    exact congrArg Prod.fst hxy
  · apply mapTuple_injective B M hB
    exact congrArg Prod.snd hxy

theorem subsetMoment_le_completeMoment (B : Finset ℕ) (s k M : ℕ)
    (hB : ∀ b ∈ B, 1 ≤ b ∧ b ≤ M) :
    subsetMoment B s k ≤ MAPFordCompleteSystemMoment.completeMoment s k M := by
  classical
  let Qb : Finset ((Fin s → BoundedNat B) × (Fin s → BoundedNat B)) :=
    Finset.univ.filter (fun xy => subsetPowerEq B s k xy)
  let Qm : Finset ((Fin s → Fin M) × (Fin s → Fin M)) :=
    Finset.univ.filter (fun xy =>
      ∀ j ∈ Finset.Icc 1 k,
        (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
          ∑ i : Fin s, ((xy.2 i).val + 1) ^ j)
  have hmap : Set.MapsTo (mapPair B M hB (s := s)) Qb Qm := by
    intro xy hxy
    have hxy' : subsetPowerEq B s k xy := by
      simpa [Qb] using hxy
    change mapPair B M hB xy ∈ Qm
    have hfull : ∀ j ∈ Finset.Icc 1 k,
        (∑ i : Fin s, (((mapPair B M hB xy).1 i).val + 1) ^ j) =
          ∑ i : Fin s, (((mapPair B M hB xy).2 i).val + 1) ^ j := by
      intro j hj
      have hh := hxy' j hj
      simpa only [mapPair, mapTuple, toFinM_val_add_one] using hh
    simpa only [Qm, Finset.mem_filter, Finset.mem_univ, true_and] using hfull
  have hinj : (Qb : Set ((Fin s → BoundedNat B) × (Fin s → BoundedNat B))).InjOn
      (mapPair B M hB (s := s)) := by
    intro xy hxy yz hyz heq
    exact mapPair_injective B M hB heq
  have hcard : Qb.card ≤ Qm.card :=
    Finset.card_le_card_of_injOn (mapPair B M hB (s := s)) hmap hinj
  simpa [subsetMoment, MAPFordCompleteSystemMoment.completeMoment, Qb, Qm] using hcard

end FordSubsetMoment

#print axioms FordSubsetMoment.subsetMoment_le_completeMoment
