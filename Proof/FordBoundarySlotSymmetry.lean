import FordBoundaryCountGeometry

open scoped BigOperators
open FordBoundaryCountGeometry
noncomputable section
namespace FordBoundarySlotSymmetry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]
variable (f : A → G) (g : U → G) {s : ℕ}

def reindex (pi : Equiv.Perm (Fin s)) (r : EnergyZero f g s) : EnergyZero f g s :=
  ⟨((r.1.1.1,fun i => r.1.1.2 (pi i)),(r.1.2.1,fun i => r.1.2.2 (pi i))), by
    change f r.1.1.1 + ∑ i, g (r.1.1.2 (pi i)) = f r.1.2.1 + ∑ i, g (r.1.2.2 (pi i))
    rw [Equiv.sum_comp pi (fun i => g (r.1.1.2 i)),
      Equiv.sum_comp pi (fun i => g (r.1.2.2 i))]
    exact r.2⟩

theorem reindex_injective (pi : Equiv.Perm (Fin s)) : Function.Injective (reindex f g pi) := by
  intro r t h
  have hh := congrArg Subtype.val h
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · simpa only [reindex] using congrArg (fun z : State A U s => z.1.1) hh
    · funext i
      have hw := congrArg (fun z : State A U s => z.1.2) hh
      have hi := congrFun hw (pi.symm i)
      simpa only [reindex, Equiv.apply_symm_apply] using hi
  · apply Prod.ext
    · simpa only [reindex] using congrArg (fun z : State A U s => z.2.1) hh
    · funext i
      have hw := congrArg (fun z : State A U s => z.2.2) hh
      have hi := congrFun hw (pi.symm i)
      simpa only [reindex, Equiv.apply_symm_apply] using hi

/-- Reindexing both words preserves the count, regardless of their frequencies. -/
theorem pinned_reindex_le (pi : Equiv.Perm (Fin s)) (e : U) (side : Bool) (i : Fin s) :
    Fintype.card (Pinned f g s e (side, pi i)) ≤
      Fintype.card (Pinned f g s e (side, i)) := by
  classical
  let tr : Pinned f g s e (side,pi i) → Pinned f g s e (side,i) :=
    fun r => ⟨reindex f g pi r.1, by
      cases side <;> simpa only [coord, reindex, Bool.false_eq_true, if_false, if_true] using r.2⟩
  apply Fintype.card_le_of_injective tr
  intro r t h
  apply Subtype.ext
  exact reindex_injective f g pi (congrArg Subtype.val h)

def swapSides (r : EnergyZero f g s) : EnergyZero f g s :=
  ⟨(r.1.2,r.1.1), r.2.symm⟩

theorem swapSides_injective : Function.Injective (swapSides f g (s := s)) := by
  intro r t h
  apply Subtype.ext
  have hh := congrArg (fun z : EnergyZero f g s => (z.1.2,z.1.1)) h
  exact hh

theorem pinned_right_le_left (e : U) (i : Fin s) :
    Fintype.card (Pinned f g s e (true,i)) ≤
      Fintype.card (Pinned f g s e (false,i)) := by
  classical
  let tr : Pinned f g s e (true,i) → Pinned f g s e (false,i) :=
    fun r => ⟨swapSides f g r.1, by simpa only [coord, swapSides, if_true, if_false] using r.2⟩
  apply Fintype.card_le_of_injective tr
  intro r t h
  apply Subtype.ext
  exact swapSides_injective f g (congrArg Subtype.val h)

/-- Any endpoint slot is bounded by the chosen left slot. -/
theorem pinned_le_fixed_left (e : U) (i0 : Fin s) (i : Bool × Fin s) :
    Fintype.card (Pinned f g s e i) ≤
      Fintype.card (Pinned f g s e (false,i0)) := by
  classical
  rcases i with ⟨side, i⟩
  have hp := pinned_reindex_le f g (Equiv.swap i0 i) e side i0
  simp only [Equiv.swap_apply_left] at hp
  cases side with
  | false => exact hp
  | true => exact hp.trans (pinned_right_le_left f g e i0)

/-- The union bound also applies to real-valued Fourier upper bounds. -/
theorem boundary_le_two_s_mul_real (e : U) (H : ℝ)
    (hH : ∀ i, (Fintype.card (Pinned f g s e i) : ℝ) ≤ H) :
    (Fintype.card (Boundary f g s e) : ℝ) ≤ 2 * (s : ℝ) * H := by
  calc
    _ ≤ ∑ i : Bool × Fin s, (Fintype.card (Pinned f g s e i) : ℝ) := by
      exact_mod_cast card_boundary_le_sum_pinned f g s e
    _ ≤ ∑ _i : Bool × Fin s, H := Finset.sum_le_sum (fun i _ => hH i)
    _ = 2 * (s : ℝ) * H := by simp [Fintype.card_prod, mul_assoc]

end FordBoundarySlotSymmetry
#print axioms FordBoundarySlotSymmetry.reindex_injective
#print axioms FordBoundarySlotSymmetry.pinned_le_fixed_left
#print axioms FordBoundarySlotSymmetry.boundary_le_two_s_mul_real
