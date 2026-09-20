import FordClassEnergyMoment

open scoped BigOperators

namespace FordClassEnergyDiagonal

open FordBoundaryCountGeometry
open FordClassEnergyMoment

noncomputable section

private def classState
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (r : ClassEnergyZero f g cls (n + 1)) : State A U (n + 1) :=
  (r.1).1

abbrev alignedDiag
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) : Type _ :=
  {r : ClassEnergyZero f g cls (n + 1) //
    ∃ i : Fin (n + 1),
      (classState f g cls r).1.2 i = (classState f g cls r).2.2 i}

instance alignedDiagFintype
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (n : ℕ) : Fintype (alignedDiag f g cls n) := by
  classical
  unfold alignedDiag
  infer_instance

private noncomputable def deleteAligned
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (r : alignedDiag f g cls n) :
    Fin (n + 1) × U × ClassEnergyZero f g cls n := by
  let st : State A U (n + 1) := classState f g cls r.1
  let i : Fin (n + 1) := Classical.choose r.property
  let left : Fin n → U := fun j => st.1.2 (i.succAbove j)
  let right : Fin n → U := fun j => st.2.2 (i.succAbove j)
  have hi : st.1.2 i = st.2.2 i := Classical.choose_spec r.property
  have henergy :
      f st.1.1 + ∑ j : Fin n, g (left j) =
        f st.2.1 + ∑ j : Fin n, g (right j) := by
    funext j
    have hh := congrFun r.1.1.2 j
    simp only [Pi.add_apply, Finset.sum_apply] at hh
    change f st.1.1 j + ∑ c : Fin (n + 1), g (st.1.2 c) j =
      f st.2.1 j + ∑ c : Fin (n + 1), g (st.2.2 c) j at hh
    rw [Fin.sum_univ_succAbove (fun q : Fin (n + 1) => g (st.1.2 q) j)
      (Classical.choose r.property),
      Fin.sum_univ_succAbove (fun q : Fin (n + 1) => g (st.2.2 q) j)
      (Classical.choose r.property)] at hh
    rw [hi] at hh
    simp only [Pi.add_apply, Finset.sum_apply]
    change f st.1.1 j + ∑ c : Fin n, g (st.1.2 (i.succAbove c)) j =
      f st.2.1 j + ∑ c : Fin n, g (st.2.2 (i.succAbove c)) j
    linarith
  have hclass : ∀ j : Fin n, cls (left j) = cls (right j) := by
    intro j
    exact r.1.2 ((Classical.choose r.property).succAbove j)
  exact (Classical.choose r.property, st.1.2 (Classical.choose r.property),
    ⟨⟨((st.1.1, left), (st.2.1, right)), henergy⟩, hclass⟩)
private theorem deleteAligned_index
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (r : alignedDiag f g cls n) :
    (deleteAligned f g cls r).1 = Classical.choose r.property := by
  rfl

private theorem deleteAligned_left
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (r : alignedDiag f g cls n) (j : Fin n) :
    (deleteAligned f g cls r).2.2.1.1.1.2 j =
      (classState f g cls r.1).1.2 ((Classical.choose r.property).succAbove j) := by
  rfl

private theorem deleteAligned_right
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) (r : alignedDiag f g cls n) (j : Fin n) :
    (deleteAligned f g cls r).2.2.1.1.2.2 j =
      (classState f g cls r.1).2.2 ((Classical.choose r.property).succAbove j) := by
  rfl

theorem alignedDiag_card_le
    {A U C : Type*} [Fintype A] [Fintype U] [Fintype C]
    {k n : ℕ} (f : A → Fin k → ℤ) (g : U → Fin k → ℤ)
    (cls : U → C) :
    Fintype.card (alignedDiag f g cls n) ≤
      (n + 1) * Fintype.card U * Fintype.card (ClassEnergyZero f g cls n) := by
  classical
  let toCarrier : alignedDiag f g cls n →
      Fin (n + 1) × U × ClassEnergyZero f g cls n :=
    fun r => deleteAligned f g cls r
  have hinj : Function.Injective toCarrier := by
    intro r t h
    refine Subtype.ext ?_
    have hi : Classical.choose r.property = Classical.choose t.property :=
      congrArg (fun z => z.1) h
    have hu : (classState f g cls r.1).1.2 (Classical.choose r.property) =
        (classState f g cls t.1).1.2 (Classical.choose t.property) := by
      have hh := congrArg (fun z => z.2.1) h
      exact hh
    have hrleft : (classState f g cls r.1).1.2 = (classState f g cls t.1).1.2 := by
      funext q
      cases q using Fin.succAboveCases (Classical.choose r.property) with
      | x => simpa [hi] using hu
      | p j =>
          have hh := congrArg (fun z => z.2.2.1.1.1.2 j) h
          simpa [toCarrier, deleteAligned_left, hi] using hh
    have hrright : (classState f g cls r.1).2.2 = (classState f g cls t.1).2.2 := by
      funext q
      cases q using Fin.succAboveCases (Classical.choose r.property) with
      | x =>
          have hdr := Classical.choose_spec r.property
          have hdt := Classical.choose_spec t.property
          have hu' := hu
          rw [← hi] at hu'
          rw [← hi] at hdt
          exact (hdr.symm.trans (hu'.trans hdt))
      | p j =>
          have hh := congrArg (fun z => z.2.2.1.1.2.2 j) h
          simpa [toCarrier, deleteAligned_right, hi] using hh
    have hbaseL : (classState f g cls r.1).1.1 =
        (classState f g cls t.1).1.1 := by
      have hh := congrArg (fun z => z.2.2.1.1.1.1) h
      simpa [toCarrier, classState] using hh
    have hbaseR : (classState f g cls r.1).2.1 =
        (classState f g cls t.1).2.1 := by
      have hh := congrArg (fun z => z.2.2.1.1.2.1) h
      simpa [toCarrier, classState] using hh
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact hbaseL
      · exact hrleft
    · apply Prod.ext
      · exact hbaseR
      · exact hrright
  have hcard := Fintype.card_le_of_injective toCarrier hinj
  simpa [Fintype.card_prod, Nat.mul_assoc] using hcard

end
end FordClassEnergyDiagonal

#print axioms FordClassEnergyDiagonal.alignedDiag_card_le
