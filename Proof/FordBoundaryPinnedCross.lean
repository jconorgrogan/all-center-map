import FordBoundarySlotSymmetry

open scoped BigOperators
open FordBoundaryCountGeometry
noncomputable section
namespace FordBoundaryPinnedCross

variable {A U : Type*} [Fintype A] [Fintype U] {k : ℕ}

def wordFreq (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (s : ℕ)
    (r : A × (Fin s → U)) : Fin k → ℤ :=
  fun j => f r.1 j + ∑ i, g (r.2 i) j

def pinnedFreq (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ)
    (r : A × (Fin s → U)) : Fin k → ℤ :=
  fun j => f r.1 j + g e j + ∑ i, g (r.2 i) j

def PinnedCross (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ) :=
  {r : (A × (Fin s → U)) × (A × (Fin (s+1) → U)) //
    ∀ j, pinnedFreq f g e s r.1 j = wordFreq f g (s+1) r.2 j}

instance (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ) :
    Fintype (PinnedCross f g e s) := by
  classical
  unfold PinnedCross
  infer_instance

/-- Fixing the left zero slot leaves exactly s free left letters and s+1 right letters. -/
def pinnedZeroEquivCross (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ) :
    Pinned f g (s+1) e (false,0) ≃ PinnedCross f g e s :=
  { toFun := fun r => ⟨((r.1.1.1.1,fun i => r.1.1.1.2 i.succ),r.1.1.2), by
      intro j
      have hh := congrFun r.1.2 j
      have he : r.1.1.1.2 0 = e := r.2
      simp only [Pi.add_apply, Finset.sum_apply, Fin.sum_univ_succ, he] at hh
      simpa only [pinnedFreq, wordFreq, Fin.sum_univ_succ, add_assoc] using hh⟩
    invFun := fun r => ⟨⟨((r.1.1.1,Fin.cons e r.1.1.2),r.1.2), by
      funext j
      have hh := r.2 j
      simp only [pinnedFreq, wordFreq, Fin.sum_univ_succ, add_assoc] at hh
      simpa only [Pi.add_apply, Finset.sum_apply, Fin.sum_univ_succ,
        Fin.cons_zero, Fin.cons_succ, add_assoc] using hh⟩, by
      change (Fin.cons e r.1.1.2 : Fin (s+1) → U) 0 = e
      simp only [Fin.cons_zero]⟩
    left_inv := by
      intro r
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          refine Fin.cases ?_ (fun i => ?_) i
          · have he : r.1.1.1.2 0 = e := r.2
            simpa only [Fin.cons_zero] using he.symm
          · simp only [Fin.cons_succ]
      · rfl
    right_inv := by
      intro r
      apply Subtype.ext
      apply Prod.ext
      · apply Prod.ext
        · rfl
        · funext i
          change (Fin.cons e r.1.1.2 : Fin (s+1) → U) i.succ = r.1.1.2 i
          simp only [Fin.cons_succ]
      · rfl }

theorem pinned_zero_card_eq_cross (f : A → Fin k → ℤ) (g : U → Fin k → ℤ) (e : U) (s : ℕ) :
    Fintype.card (Pinned f g (s+1) e (false,0)) = Fintype.card (PinnedCross f g e s) :=
  Fintype.card_congr (pinnedZeroEquivCross f g e s)

end FordBoundaryPinnedCross
#print axioms FordBoundaryPinnedCross.pinned_zero_card_eq_cross
