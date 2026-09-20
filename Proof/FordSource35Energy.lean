import FordBoundaryCountGeometry
import FordP16Source35Reparam

open scoped BigOperators
open MAPFordP16FiniteFourierBridge MAPFordP16Source35Reparam
open FordBoundaryCountGeometry
noncomputable section
namespace FordSource35Energy

variable {p k d Q P : ℕ} [NeZero p]

def sourceF (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (z : fordFiniteFCarrier (p := p) (P := P) hdk hp psi) : Fin k → ℤ :=
  fordSourceFrequencyAt psi z.1

def shiftedPower (q : ℕ) (c : Fin p) (u : shiftedU (Q := Q) c) : Fin k → ℤ :=
  fun j => (q : ℤ)^(j.val+1) * ((p : ℤ)*(u.1.val : ℤ)-(c.val : ℤ))^(j.val+1)

/-- The literal source-(3.5) system is equality of two additive frequencies. -/
theorem source35_frequency_iff {s q : ℕ}
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (z w : fordFiniteFCarrier (p := p) (P := P) hdk hp psi)
    (u v : Fin s → shiftedU (Q := Q) c) :
    (∀ j, source35Frequency (q := q) hdk hp psi c (((z,u),v),w) j = 0) ↔
      sourceF hdk hp psi z + ∑ i, shiftedPower q c (u i) =
        sourceF hdk hp psi w + ∑ i, shiftedPower q c (v i) := by
  constructor
  · intro h
    funext j
    simp only [Pi.add_apply, Finset.sum_apply, sourceF, shiftedPower]
    have hh := h j
    change fordSourceFrequencyAt psi z.1 j - fordSourceFrequencyAt psi w.1 j +
      (q : ℤ)^(j.val+1) * (∑ i : Fin s,
        (((p : ℤ)*(u i).1.val-c.val)^(j.val+1) -
          ((p : ℤ)*(v i).1.val-c.val)^(j.val+1))) = 0 at hh
    change fordSourceFrequencyAt psi z.1 j +
      (∑ i : Fin s, (q : ℤ)^(j.val+1) * ((p : ℤ)*(u i).1.val-c.val)^(j.val+1)) =
      fordSourceFrequencyAt psi w.1 j +
      (∑ i : Fin s, (q : ℤ)^(j.val+1) * ((p : ℤ)*(v i).1.val-c.val)^(j.val+1))
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum] at hh
    linarith
  · intro h j
    have hh := congrFun h j
    simp only [Pi.add_apply, Finset.sum_apply, sourceF, shiftedPower] at hh
    change fordSourceFrequencyAt psi z.1 j +
      (∑ i : Fin s, (q : ℤ)^(j.val+1) * ((p : ℤ)*(u i).1.val-c.val)^(j.val+1)) =
      fordSourceFrequencyAt psi w.1 j +
      (∑ i : Fin s, (q : ℤ)^(j.val+1) * ((p : ℤ)*(v i).1.val-c.val)^(j.val+1)) at hh
    change fordSourceFrequencyAt psi z.1 j - fordSourceFrequencyAt psi w.1 j +
      (q : ℤ)^(j.val+1) * (∑ i : Fin s,
        (((p : ℤ)*(u i).1.val-c.val)^(j.val+1) -
          ((p : ℤ)*(v i).1.val-c.val)^(j.val+1))) = 0
    simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum]
    linarith

/-- Reassociation only: both source masks, all words, and all equations remain. -/
def source35EquivEnergy {s q : ℕ}
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    source35Carrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c ≃
      EnergyZero (sourceF (P := P) hdk hp psi) (shiftedPower (Q := Q) q c) s :=
  { toFun := fun r => ⟨((r.1.1.1.1,r.1.1.1.2),(r.1.2,r.1.1.2)),
      (source35_frequency_iff hdk hp psi c _ _ _ _).mp r.2⟩
    invFun := fun r => ⟨(((r.1.1.1,r.1.1.2),r.1.2.2),r.1.2.1),
      (source35_frequency_iff hdk hp psi c _ _ _ _).mpr r.2⟩
    left_inv := by intro r; rfl
    right_inv := by intro r; rfl }

theorem source35_card_eq_energy {s q : ℕ}
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype.card (source35Carrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) =
      Fintype.card (EnergyZero (sourceF (P := P) hdk hp psi) (shiftedPower (Q := Q) q c) s) :=
  Fintype.card_congr (source35EquivEnergy hdk hp psi c)

theorem source35_diagonal_lower {s q : ℕ}
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype.card (BaseZero (sourceF (P := P) hdk hp psi)) *
        (Fintype.card (shiftedU (Q := Q) c))^s ≤
      Fintype.card (source35Carrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  rw [source35_card_eq_energy]
  exact diagonal_lower _ _ _

end FordSource35Energy
#print axioms FordSource35Energy.source35_frequency_iff
#print axioms FordSource35Energy.source35_card_eq_energy
#print axioms FordSource35Energy.source35_diagonal_lower
