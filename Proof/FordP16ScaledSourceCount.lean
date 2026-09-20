import FordSource35BoundaryCap
import FordSource36InteriorCarrier
import FordPositiveQSourceHolder

open scoped BigOperators ZMod
noncomputable section
namespace MAPFordP16ScaledSourceCount
open MAPFordP16FiniteFourierBridge MAPFordP16SourceCountBridge
open MAPFordP16Source35Reparam MAPFordP16Source35Triangular
open MAPFordSource35BoundaryCap MAPFordSource36InteriorCarrier MAPFordPositiveQSourceHolder

def source35InteriorTo36 {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (a : source35Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) :
    source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c :=
  ⟨source35To36 hdk hp psi c a.1, a.2⟩

lemma source35InteriorTo36_injective {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Function.Injective (source35InteriorTo36 (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  intro a b h
  apply Subtype.ext
  exact source35To36_injective hdk hp psi c (congrArg Subtype.val h)

/-- The exact fixed-residue p16 count shrinks its full shifted box to Q/p,
retaining both masks under the corrected q*c transform. -/
theorem fixed_residue_card_le_twice_scaled {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p)
    (hzero : ∀ j : Fin k, j.val < d → psi j = 0)
    (hs : 1 ≤ s) (hnative : (4*s)^2*p ≤ Q) :
    Fintype.card (fordFiniteRawS4Carrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi b) ≤
      2 * Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q/p) (P := P)
        (q := p*q) hdk hp (phiRow psi (q : ℤ) (negResidue b).val)) := by
  have hraw := Fintype.card_le_of_injective _
    (rawS4ToSource35_injective (s := s) (Q := Q) (P := P) (q := q) hdk hp psi b)
  have hcap := source35_card_le_twice_native_interior_card
    (s := s) (Q := Q) (P := P) (q := q) hdk hp psi (negResidue b) hs hnative
  have h36 := Fintype.card_le_of_injective _
    (source35InteriorTo36_injective (s := s) (Q := Q) (P := P) (q := q) hdk hp psi (negResidue b))
  have hshort := source36Interior_card_le_rawFrequency_card
    (s := s) (Q := Q) (P := P) (q := q) hdk hp psi (negResidue b) hzero
  exact hraw.trans (hcap.trans (Nat.mul_le_mul_left 2 (h36.trans hshort)))

/-- The actual source-count Holder step and boundary cap combined. All
Fourier, no-alias, and boundary-moment inputs are internal. Only positivity
of q is required: integer cancellation precedes residue reduction. -/
theorem rawFrequency_exists_scaled_count {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 1 ≤ s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin k, j.val < d → psi j = 0)
    (hq : 0 < q) (hnative : (4*s)^2*p ≤ Q) :
    ∃ b : ZMod p,
      Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
        (2 * Nat.factorial d * p^(2*s-d)) *
          Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q/p) (P := P)
            (q := p*q) hdk hp (phiRow psi (q : ℤ) (negResidue b).val)) := by
  have hlow : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0 :=
    fun j => hzero (Fin.castLE hdk j) j.isLt
  obtain ⟨b, hb⟩ := fordFiniteRawFrequency_exists_fixed_residue_holder_of_pos
    (s := s) (Q := Q) (P := P) (q := q) hp hd hds hs hdk psi hlow hq
  have hcap := fixed_residue_card_le_twice_scaled (P := P) (q := q) hdk hp psi b hzero hs hnative
  refine ⟨b, ?_⟩
  have h := hb.trans (Nat.mul_le_mul_left (Nat.factorial d * p^(2*s-d)) hcap)
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

end MAPFordP16ScaledSourceCount
#print axioms MAPFordP16ScaledSourceCount.fixed_residue_card_le_twice_scaled
#print axioms MAPFordP16ScaledSourceCount.rawFrequency_exists_scaled_count
