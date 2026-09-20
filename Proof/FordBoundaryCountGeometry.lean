import Mathlib

open scoped BigOperators
noncomputable section
namespace FordBoundaryCountGeometry

variable {A U G : Type*} [Fintype A] [Fintype U] [AddCommMonoid G]

abbrev State (A U : Type*) (s : ℕ) := (A × (Fin s → U)) × (A × (Fin s → U))

def EnergyZero (f : A → G) (g : U → G) (s : ℕ) :=
  {r : State A U s // f r.1.1 + ∑ i, g (r.1.2 i) = f r.2.1 + ∑ i, g (r.2.2 i)}

instance (f : A → G) (g : U → G) (s : ℕ) : Fintype (EnergyZero f g s) := by
  classical
  unfold EnergyZero
  infer_instance

def coord {s : ℕ} (r : State A U s) (i : Bool × Fin s) : U :=
  if i.1 then r.2.2 i.2 else r.1.2 i.2

def Boundary (f : A → G) (g : U → G) (s : ℕ) (e : U) :=
  {r : EnergyZero f g s // ∃ i, coord r.1 i = e}

def Interior (f : A → G) (g : U → G) (s : ℕ) (e : U) :=
  {r : EnergyZero f g s // ∀ i, coord r.1 i ≠ e}

def Pinned (f : A → G) (g : U → G) (s : ℕ) (e : U) (i : Bool × Fin s) :=
  {r : EnergyZero f g s // coord r.1 i = e}

instance (f : A → G) (g : U → G) (s : ℕ) (e : U) : Fintype (Boundary f g s e) := by
  classical
  unfold Boundary
  infer_instance
instance (f : A → G) (g : U → G) (s : ℕ) (e : U) : Fintype (Interior f g s e) := by
  classical
  unfold Interior
  infer_instance
instance (f : A → G) (g : U → G) (s : ℕ) (e : U) (i : Bool × Fin s) :
    Fintype (Pinned f g s e i) := by
  classical
  unfold Pinned
  infer_instance

/-- An exact partition: a word either uses the endpoint in some slot or none. -/
theorem card_energy_partition (f : A → G) (g : U → G) (s : ℕ) (e : U) :
    Fintype.card (EnergyZero f g s) =
      Fintype.card (Boundary f g s e) + Fintype.card (Interior f g s e) := by
  classical
  let E : EnergyZero f g s ≃ Boundary f g s e ⊕ Interior f g s e :=
    { toFun := fun r => if h : ∃ i, coord r.1 i = e then Sum.inl ⟨r, h⟩
        else Sum.inr ⟨r, by simpa only [not_exists] using h⟩
      invFun := fun | Sum.inl r => r.1 | Sum.inr r => r.1
      left_inv := by intro r; dsimp; split_ifs <;> rfl
      right_inv := by
        intro r
        cases r with
        | inl r =>
          dsimp
          rw [dif_pos r.property]
          rfl
        | inr r =>
          have hh : ¬ ∃ i, coord r.1.1 i = e := by simpa only [not_exists] using r.property
          dsimp
          rw [dif_neg hh]
          rfl }
  simpa only [Fintype.card_sum] using Fintype.card_congr E

/-- Choosing one occupied endpoint slot gives the literal union bound. -/
theorem card_boundary_le_sum_pinned (f : A → G) (g : U → G) (s : ℕ) (e : U) :
    Fintype.card (Boundary f g s e) ≤
      ∑ i : Bool × Fin s, Fintype.card (Pinned f g s e i) := by
  classical
  let chooseSlot : Boundary f g s e → Sigma (Pinned f g s e) :=
    fun r => ⟨Classical.choose r.property, ⟨r.1, Classical.choose_spec r.property⟩⟩
  have hinj : Function.Injective chooseSlot := by
    intro r t h
    apply Subtype.ext
    have hh := congrArg (fun z : Sigma (Pinned f g s e) => z.2.1) h
    exact hh
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_injective chooseSlot hinj

def BaseZero (f : A → G) := {r : A × A // f r.1 = f r.2}
instance (f : A → G) : Fintype (BaseZero f) := by
  classical
  unfold BaseZero
  infer_instance

/-- The diagonal u=v remains available with both source masks unchanged. -/
theorem diagonal_lower (f : A → G) (g : U → G) (s : ℕ) :
    Fintype.card (BaseZero f) * (Fintype.card U)^s ≤
      Fintype.card (EnergyZero f g s) := by
  classical
  let diag : (BaseZero f × (Fin s → U)) → EnergyZero f g s :=
    fun r => ⟨((r.1.1.1, r.2), (r.1.1.2, r.2)), by rw [r.1.2]⟩
  have hinj : Function.Injective diag := by
    intro r t h
    have hh := congrArg Subtype.val h
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z : State A U s => z.1.1) hh
      · exact congrArg (fun z : State A U s => z.2.1) hh
    · exact congrArg (fun z : State A U s => z.1.2) hh
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective diag hinj

/-- A common bound for all 2s endpoint slots bounds the boundary count. -/
theorem boundary_le_two_s_mul (f : A → G) (g : U → G) (s : ℕ) (e : U) (H : ℕ)
    (hH : ∀ i, Fintype.card (Pinned f g s e i) ≤ H) :
    Fintype.card (Boundary f g s e) ≤ 2*s*H := by
  calc
    _ ≤ ∑ i : Bool × Fin s, Fintype.card (Pinned f g s e i) :=
      card_boundary_le_sum_pinned f g s e
    _ ≤ ∑ _i : Bool × Fin s, H := Finset.sum_le_sum (fun i _ => hH i)
    _ = 2*s*H := by simp [Fintype.card_prod]

end FordBoundaryCountGeometry
#print axioms FordBoundaryCountGeometry.card_energy_partition
#print axioms FordBoundaryCountGeometry.card_boundary_le_sum_pinned
#print axioms FordBoundaryCountGeometry.diagonal_lower
#print axioms FordBoundaryCountGeometry.boundary_le_two_s_mul
