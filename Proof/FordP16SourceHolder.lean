import FordP16SourceCountBridge

open scoped BigOperators ZMod

namespace MAPFordP16SourceHolder
noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordP16FiniteTargetCount
open MAPFordP16IntegerHolder
open MAPFordP16SourceCountBridge

theorem fordFiniteRawFrequency_integer_holder
    {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q) :
    Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) *
        ∑ b : ZMod p, Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s)
          (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  apply le_trans (fordFiniteRawFrequency_card_le_targetZero hdk hp psi hzero hq)
  simpa only [fixed_b_s4_card_eq] using
    (integer_target_holder (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hp hd hds hs hdk psi)

theorem fordFiniteRawFrequency_exists_fixed_residue_holder
    {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q) :
    ∃ b : ZMod p,
      Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
        (Nat.factorial d * p ^ (2*s-d) : ℕ) *
          Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s) (k := k)
            (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  let f : ZMod p → ℕ := fun b =>
    Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b)
  have hsource := fordFiniteRawFrequency_integer_holder (p := p) (s := s) (k := k)
    (d := d) (Q := Q) (P := P) (q := q) hp hd hds hs hdk psi hzero hq
  have huniv : (Finset.univ : Finset (ZMod p)).Nonempty := Finset.univ_nonempty
  obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (ZMod p))
    huniv f
  have hsum : ∑ b' : ZMod p, f b' ≤ p * f b := by
    calc
      ∑ b' : ZMod p, f b' ≤ (Finset.univ : Finset (ZMod p)).card • f b := by
        apply Finset.sum_le_card_nsmul
        intro b' hb'
        exact (Finset.le_sup hb').trans_eq hmax
      _ = p * f b := by simp [ZMod.card]
  have hscaled :
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) * ∑ b' : ZMod p, f b' ≤
        (Nat.factorial d * p ^ (2*s-d-1) : ℕ) * (p * f b) :=
    Nat.mul_le_mul_left _ hsum
  have hexp : 2*s-d-1 + 1 = 2*s-d := by omega
  have hmul :
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) * (p * f b) =
        (Nat.factorial d * p ^ (2*s-d) : ℕ) * f b := by
    calc
      _ = (Nat.factorial d * p ^ (2*s-d-1) : ℕ) * p * f b := by ring
      _ = (Nat.factorial d * p ^ (2*s-d-1 + 1) : ℕ) * f b := by
        rw [Nat.pow_succ]
        ring
      _ = _ := by rw [hexp]
  refine ⟨b, ?_⟩
  change Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
    (Nat.factorial d * p ^ (2*s-d) : ℕ) * f b
  exact hsource.trans (hscaled.trans_eq hmul)

end
end MAPFordP16SourceHolder

#print axioms MAPFordP16SourceHolder.fordFiniteRawFrequency_integer_holder
#print axioms MAPFordP16SourceHolder.fordFiniteRawFrequency_exists_fixed_residue_holder
