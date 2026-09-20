import FordTriangularJacobian
import FordP16Source35Triangular

open scoped BigOperators ZMod

namespace MAPFordSource36InteriorCarrier
noncomputable section
set_option maxHeartbeats 1200000

open MAPFordP16FiniteFourierBridge
open MAPFordP16Source35Reparam
open MAPFordP16SourceCountBridge
open MAPFordP16Source35Triangular
open MAPFordP16LiteralResidueBridge

/-- The source-36 interior where both shifted tuples stay below `Q/p`. -/
def source36Interior
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) : Type :=
  {r : source36Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c //
    (∀ i : Fin s, (r.1.1.1.2 i).1.val ≤ Q / p) ∧
    (∀ i : Fin s, (r.1.1.2 i).1.val ≤ Q / p)}

instance source36InteriorFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype (source36Interior (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) := by
  classical
  dsimp [source36Interior]
  infer_instance

/-- Forget the shift and retain the same positive integer in the short raw box. -/
def interiorPositiveX
    {p Q : ℕ} [NeZero p] (c : Fin p)
    (u : shiftedU (p := p) (Q := Q) c) (hu : u.1.val ≤ Q / p) :
    fordFinitePositiveX (Q := Q / p) :=
  ⟨⟨u.1.val, by omega⟩, u.2⟩

/-- Transport an `F` point across the proved literal mask equivalence. -/
def transportF
    {p k d P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) (q c : ℤ)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (z : fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) :
    fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp
      (phiRow psi q c) := by
  refine ⟨z.1, ?_⟩
  exact (fordPolynomialMask_phiRow_iff (p := p) (k := k) (d := d) (P := P)
    hdk hp psi q c hzero z.1).mpr z.2

def interiorTuple
    {p s Q : ℕ} [NeZero p] (c : Fin p)
    (u : Fin s → shiftedU (p := p) (Q := Q) c)
    (hu : ∀ i : Fin s, (u i).1.val ≤ Q / p) :
    Fin s → fordFinitePositiveX (Q := Q / p) :=
  fun i => interiorPositiveX (p := p) (Q := Q) c (u i) (hu i)


end
end MAPFordSource36InteriorCarrier
#print axioms MAPFordSource36InteriorCarrier.transportF
#print axioms MAPFordSource36InteriorCarrier.interiorTuple
