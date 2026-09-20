import Mathlib

open scoped BigOperators
noncomputable section
namespace FordPhaseFibers

def multiplicity {X C : Type*} [Fintype X] [DecidableEq C]
    (f : X → C) (c : C) : ℕ :=
  (Finset.univ.filter (fun x => f x = c)).card

theorem grouped_sum {X C : Type*} [Fintype X] [DecidableEq C]
    (f : X → C) (S : Finset C) (hf : ∀ x, f x ∈ S) (F : C → ℂ) :
    ∑ x, F (f x) = ∑ c ∈ S, (multiplicity f c : ℂ) * F c := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset X)) (t := S) (fun x _ => hf x)
    (fun x => F (f x))
  rw [← h]
  apply Finset.sum_congr rfl
  intro c hc
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x => f x = c), F c := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ = _ := by simp [multiplicity]

theorem total_mass {X C : Type*} [Fintype X] [DecidableEq C]
    (f : X → C) (S : Finset C) (hf : ∀ x, f x ∈ S) :
    ∑ c ∈ S, multiplicity f c = Fintype.card X := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset X)) (t := S) (fun x _ => hf x)
    (fun _ => (1 : ℕ))
  simpa [multiplicity] using h

theorem collision_mass {X C : Type*} [Fintype X] [DecidableEq C]
    (f : X → C) (S : Finset C) (hf : ∀ x, f x ∈ S) :
    ∑ c ∈ S, multiplicity f c ^ 2 =
      (Finset.univ.filter (fun p : X × X => f p.1 = f p.2)).card := by
  classical
  let Q := Finset.univ.filter (fun p : X × X => f p.1 = f p.2)
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Q) (t := S)
    (fun p _ => show f p.1 ∈ S from hf p.1) (fun _ => (1 : ℕ))
  have heq (c : C) : Q.filter (fun p => f p.1 = c) =
      ((Finset.univ : Finset X).filter (fun x => f x = c)).product
        ((Finset.univ : Finset X).filter (fun x => f x = c)) := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpQ, h2⟩
      have h1 := (Finset.mem_filter.mp hpQ).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩,
         Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1 ▸ h2⟩⟩
    · intro hp
      rcases Finset.mem_product.mp hp with ⟨hx, hy⟩
      have h1 := (Finset.mem_filter.mp hx).2
      have h2 := (Finset.mem_filter.mp hy).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1.trans h2.symm⟩, h1⟩
  have hh : ∑ c ∈ S, (Q.filter (fun p => f p.1 = c)).card = Q.card := by
    simpa using h
  simpa [heq, Finset.card_product, multiplicity, pow_two, Q] using hh

end FordPhaseFibers
#print axioms FordPhaseFibers.grouped_sum
#print axioms FordPhaseFibers.total_mass
#print axioms FordPhaseFibers.collision_mass
