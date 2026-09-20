import FordP16ScaledSourceCount
import FordActualGroupedToL
import FordMaskedKToRaw
import FordPhiType

noncomputable section
namespace MAPFordMaskedKToL
open MAPFordP16ScaledSourceCount MAPFordMaskedKToRaw MAPFordP16SourceCountBridge
open MAPFordP16Source35Triangular MAPFordP16Source35Reparam
open MAPFordLemma32LiteralContract MAPFordType

/-- The actual fixed-prime p16/p17 count, with a literal transformed family.
The initial selection of a prime and the subsequent recurrence are separate. -/
theorem maskedK_exists_L {p s k d Q P q r m : ℕ} {T : ℤ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 1 ≤ s)
    (hdk : d ≤ k) (hr1 : 1 ≤ r) (hrk : r ≤ k)
    (psi : Fin k → Polynomial ℤ)
    (htype : FordType k d T m (psiNatSucc psi))
    (hq : 0 < q) (hnative : (4*s)^2*p ≤ Q) :
    ∃ b : ZMod p,
      FordType k d T m (psiNatSucc (phiRow psi (q : ℤ) (negResidue b).val)) ∧
      Fintype.card (MaskedK (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
        (2 * Nat.factorial d * p ^
          (2*s-d + ((r-d)*(r-d-1)/2 + r*d + (k-d)))) *
          Fintype.card (LPoint s k P (Q/p) p q r
            (phiRow psi (q : ℤ) (negResidue b).val)) := by
  have hzero : ∀ j : Fin k, j.val < d → psi j = 0 := by
    intro j hj
    have h := (htype (j.val+1) (by omega)).1 (by omega)
    simpa [psiNatSucc, psiNat] using h
  obtain ⟨b, hb⟩ := rawFrequency_exists_scaled_count
    (P := P) (Q := Q) (q := q) hp hd hds hs hdk psi hzero hq hnative
  refine ⟨b, MAPFordPhiType.phiRow_has_FordType psi _ _ htype, ?_⟩
  have hg := FordActualGroupedToL.actual_card_le_L
    (P := P) (Q := Q/p) (q := q) (s := s) hdk hp hr1 hrk
    (phiRow psi (q : ℤ) (negResidue b).val)
  have hm := maskedK_card_le_raw (s := s) (Q := Q) (P := P) (q := q) hdk hp psi
  have hall := hm.trans (hb.trans
    (Nat.mul_le_mul_left (2 * Nat.factorial d * p^(2*s-d)) hg))
  simpa only [pow_add, mul_assoc] using hall

end MAPFordMaskedKToL
#print axioms MAPFordMaskedKToL.maskedK_exists_L
