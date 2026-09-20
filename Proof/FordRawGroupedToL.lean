import FordRawStateGeometry
import FordExactFrequencyGrouping

noncomputable section
namespace MAPFordRawGroupedToL
open MAPFordRawStateGeometry MAPFordP16SourceCountBridge
open MAPFordRawCongruenceToL MAPFordLemma32LiteralContract

/-- Exact finite source-to-L comparison from the literal per-total residue
class cap. The arithmetic producer of hC is a separate obligation. -/
theorem raw_card_le_L_of_class_cap {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) (C : ℕ)
    (hC : ∀ t : Fin k → ℤ,
      ((Finset.univ.filter (fun a : RawState (s := s) (Q := Q) (P := P) hdk hp phi =>
        total hdk hp phi q a = t)).image (residue hdk hp phi r)).card ≤ C) :
    Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P)
      (q := p*q) hdk hp phi) ≤ C * Fintype.card (LPoint s k P Q p q r phi) := by
  classical
  have h := FordExactFrequencyGrouping.collision_card_le_class_collision_card
    (total (s := s) (Q := Q) (P := P) hdk hp phi q)
    (residue (s := s) (Q := Q) (P := P) hdk hp phi r) C hC
  have hraw := Fintype.card_congr
    (rawEquivCollision (s := s) (Q := Q) (P := P) (q := q) hdk hp phi)
  have hrest := Fintype.card_congr
    (restrictedEquivRawCongruent (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi)
  rw [← hraw, hrest] at h
  exact h.trans (Nat.mul_le_mul_left C (rawCongruent_card_le_L hdk hp phi))

end MAPFordRawGroupedToL
#print axioms MAPFordRawGroupedToL.raw_card_le_L_of_class_cap
