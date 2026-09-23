import FordP16Source35Triangular
import FordShiftedEndpointGeometry
import FordSource35Energy
import FordBoundaryAbsorption

open scoped BigOperators ZMod

namespace MAPFordSource35BoundaryCap
noncomputable section
set_option maxHeartbeats 1200000

open MAPFordP16FiniteFourierBridge
open MAPFordP16Source35Reparam
open MAPFordP16Source35Triangular
open MAPFordShiftedEndpointGeometry
open FordBoundaryCountGeometry
open FordSource35Energy

/-- Source-(3.5) solutions whose shifted tuples avoid the full endpoint. -/
def source35Interior
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Type :=
  {r : source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c //
    (∀ i : Fin s, (r.1.1.1.2 i).1.val ≤ Q / p) ∧
    (∀ i : Fin s, (r.1.1.2 i).1.val ≤ Q / p)}

instance source35InteriorFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype (source35Interior (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) := by
  classical
  dsimp [source35Interior]
  infer_instance

def source35InteriorEquivInterior
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    source35Interior (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c ≃
    Interior (sourceF (P := P) hdk hp psi)
      (shiftedPower (Q := Q) q c) s
      (shiftedUEndpoint (p := p) (Q := Q) c hboundary) := by
  let E := source35EquivEnergy (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c
  let e := shiftedUEndpoint (p := p) (Q := Q) c hboundary
  refine {
    toFun := fun r =>
      ⟨E r.1, ?_⟩
    invFun := fun r =>
      ⟨E.symm r.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    rcases i with ⟨b, idx⟩
    cases b with
    | false =>
      simpa [coord, E, e, source35EquivEnergy] using!
        ((shiftedU_ne_endpoint_iff_le (p := p) (Q := Q) c hboundary
          (r.1.1.1.1.2 idx)).2 (r.2.1 idx))
    | true =>
      simpa [coord, E, e, source35EquivEnergy] using!
        ((shiftedU_ne_endpoint_iff_le (p := p) (Q := Q) c hboundary
          (r.1.1.1.2 idx)).2 (r.2.2 idx))
  · have hcoord := r.2
    refine ⟨?_, ?_⟩
    · intro i
      have hne := hcoord (false, i)
      have hne' : (E.symm r.1).1.1.1.2 i ≠ e := by
        intro hbad
        apply hne
        simpa [coord, E, e, source35EquivEnergy] using! hbad
      exact (shiftedU_ne_endpoint_iff_le (p := p) (Q := Q) c hboundary
        ((E.symm r.1).1.1.1.2 i)).1 hne'
    · intro i
      have hne := hcoord (true, i)
      have hne' : (E.symm r.1).1.1.2 i ≠ e := by
        intro hbad
        apply hne
        simpa [coord, E, e, source35EquivEnergy] using! hbad
      exact (shiftedU_ne_endpoint_iff_le (p := p) (Q := Q) c hboundary
        ((E.symm r.1).1.1.2 i)).1 hne'
  · intro r
    apply Subtype.ext
    exact E.left_inv r.1
  · intro r
    apply Subtype.ext
    exact E.right_inv r.1

theorem source35_card_eq_restricted_interior_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    Fintype.card (source35Interior (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) =
    Fintype.card (Interior (sourceF (P := P) hdk hp psi)
      (shiftedPower (Q := Q) q c) s
      (shiftedUEndpoint (p := p) (Q := Q) c hboundary)) := by
  exact Fintype.card_congr (source35InteriorEquivInterior hdk hp psi c hboundary)

theorem source35_card_le_twice_restricted_interior_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hs : 1 ≤ s)
    (hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c)
    (hsize : (4*s)^2 < shiftedUFullCap (p := p) (Q := Q) c) :
    Fintype.card (source35Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) ≤
      2 * Fintype.card (source35Interior (p := p) (s := s) (k := k) (d := d)
        (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  have hsize' : (4*s)^2 < Fintype.card (shiftedU (p := p) (Q := Q) c) := by
    simpa only [shiftedU_card (p := p) (Q := Q) c] using hsize
  have henergy := FordBoundaryAbsorption.energy_le_twice_interior
    (A := fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi)
    (U := shiftedU (p := p) (Q := Q) c)
    (k := k) (sourceF (P := P) hdk hp psi) (shiftedPower (Q := Q) q c)
    (shiftedUEndpoint (p := p) (Q := Q) c hboundary) s hs hsize'
  rw [source35_card_eq_energy hdk hp psi c]
  rw [source35_card_eq_restricted_interior_card hdk hp psi c hboundary]
  exact henergy


def source35ToInterior_no_boundary
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hno : ¬ Q / p < shiftedUFullCap (p := p) (Q := Q) c)
    (r : source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) :
    source35Interior (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c := by
  have hcap : shiftedUFullCap (p := p) (Q := Q) c ≤ Q / p := by
    exact Nat.le_of_not_gt hno
  refine ⟨r, ?_⟩
  constructor
  · intro i
    have hu := (r.1.1.1.2 i).1.isLt
    change (r.1.1.1.2 i).1.val <
      shiftedUFullCap (p := p) (Q := Q) c + 1 at hu
    omega
  · intro i
    have hv := (r.1.1.2 i).1.isLt
    change (r.1.1.2 i).1.val <
      shiftedUFullCap (p := p) (Q := Q) c + 1 at hv
    omega

lemma source35ToInterior_no_boundary_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hno : ¬ Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    Function.Injective (source35ToInterior_no_boundary (p := p) (s := s)
      (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi c hno) := by
  intro a b hab
  exact congrArg Subtype.val hab

theorem source35_card_le_native_interior_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hno : ¬ Q / p < shiftedUFullCap (p := p) (Q := Q) c) :
    Fintype.card (source35Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) ≤
      Fintype.card (source35Interior (p := p) (s := s) (k := k) (d := d)
        (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  exact Fintype.card_le_of_injective _
    (source35ToInterior_no_boundary_injective (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi c hno)

theorem source35_card_le_twice_native_interior_card
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hs : 1 ≤ s)
    (hnative : (4*s)^2 * p ≤ Q) :
    Fintype.card (source35Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c) ≤
      2 * Fintype.card (source35Interior (p := p) (s := s) (k := k) (d := d)
        (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  by_cases hboundary : Q / p < shiftedUFullCap (p := p) (Q := Q) c
  · have hTle : (4*s)^2 ≤ Q / p := by
      apply (Nat.le_div_iff_mul_le hp.pos).2
      exact hnative
    have hcap := shiftedUFullCap_eq_succ_of_boundary (p := p) (Q := Q) c hboundary
    have hsize : (4*s)^2 < shiftedUFullCap (p := p) (Q := Q) c := by
      omega
    exact source35_card_le_twice_restricted_interior_card hdk hp psi c hs
      hboundary hsize
  · have hcard := source35_card_le_native_interior_card (p := p) (s := s)
      (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi c hboundary
    omega

end
end MAPFordSource35BoundaryCap

#print axioms MAPFordSource35BoundaryCap.source35_card_eq_restricted_interior_card
#print axioms MAPFordSource35BoundaryCap.source35_card_le_twice_restricted_interior_card
#print axioms MAPFordSource35BoundaryCap.source35_card_le_native_interior_card
#print axioms MAPFordSource35BoundaryCap.source35_card_le_twice_native_interior_card
