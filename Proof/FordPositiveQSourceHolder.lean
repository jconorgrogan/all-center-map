import FordP16SourceHolder

open scoped BigOperators ZMod

namespace MAPFordPositiveQSourceHolder

noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordP16FiniteTargetCount
open MAPFordP16IntegerHolder
open MAPFordP16SourceCountBridge

/- The low-frequency equation is cancelled over `ℤ` before reduction modulo
`p`; consequently this bridge needs only positivity of `q`, not `p ∤ q`. -/
lemma fordFiniteRawFrequency_power_residue_eq_of_pos
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q)
    (r : fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteRawPowerResidue (p := p) (d := d) r.1.1.2 =
      fordFiniteRawPowerResidue (p := p) (d := d) r.1.2.2 := by
  letI : Fact p.Prime := ⟨hp⟩
  funext j
  have hfreq := r.2 (Fin.castLE hdk j)
  have hx := fordFiniteRawSourceFrequency_zero_of_low hdk psi hzero
    (r.1.1.1).1 j
  have hy := fordFiniteRawSourceFrequency_zero_of_low hdk psi hzero
    (r.1.2.1).1 j
  have hqfreq :
      fordQFrequencyAt (q := q) (fun i => (r.1.1.2 i).1) (Fin.castLE hdk j) =
        fordQFrequencyAt (q := q) (fun i => (r.1.2.2 i).1) (Fin.castLE hdk j) := by
    dsimp [fordFiniteRawFrequency] at hfreq
    rw [hx, hy] at hfreq
    omega
  have hqint :
      (q : ℤ) ^ (j.val + 1) *
          (∑ i : Fin s, ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1)) =
        (q : ℤ) ^ (j.val + 1) *
          (∑ i : Fin s, ((r.1.2.2 i).1.val : ℤ) ^ (j.val + 1)) := by
    calc
      _ = ∑ i : Fin s,
          (q : ℤ) ^ (j.val + 1) * ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1) := by
        rw [Finset.mul_sum]
      _ = ∑ i : Fin s,
          (q : ℤ) ^ ((Fin.castLE hdk j).val + 1) *
            ((r.1.1.2 i).1.val : ℤ) ^ ((Fin.castLE hdk j).val + 1) := by rfl
      _ = ∑ i : Fin s, fordQScalarFrequency (q := q) (r.1.1.2 i).1
          (Fin.castLE hdk j) := by rfl
      _ = fordQFrequencyAt (q := q) (fun i => (r.1.1.2 i).1)
          (Fin.castLE hdk j) := by rfl
      _ = fordQFrequencyAt (q := q) (fun i => (r.1.2.2 i).1)
          (Fin.castLE hdk j) := hqfreq
      _ = ∑ i : Fin s, fordQScalarFrequency (q := q) (r.1.2.2 i).1
          (Fin.castLE hdk j) := by rfl
      _ = ∑ i : Fin s,
          (q : ℤ) ^ ((Fin.castLE hdk j).val + 1) *
            ((r.1.2.2 i).1.val : ℤ) ^ ((Fin.castLE hdk j).val + 1) := by rfl
      _ = ∑ i : Fin s,
          (q : ℤ) ^ (j.val + 1) * ((r.1.2.2 i).1.val : ℤ) ^ (j.val + 1) := by rfl
      _ = _ := by rw [← Finset.mul_sum]
  have hqpow : (q : ℤ) ^ (j.val + 1) ≠ 0 := by
    apply pow_ne_zero
    exact_mod_cast (Nat.ne_of_gt hqpos)
  have hsumInt :
      (∑ i : Fin s, ((r.1.1.2 i).1.val : ℤ) ^ (j.val + 1)) =
        ∑ i : Fin s, ((r.1.2.2 i).1.val : ℤ) ^ (j.val + 1) :=
    mul_left_cancel₀ hqpow hqint
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hsumInt
  simpa [Int.cast_sum, Int.cast_pow] using hcast

def fordFiniteRawFrequencyToS3_of_pos
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q)
    (r : fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi :=
  ⟨r.1, fordFiniteRawFrequency_power_residue_eq_of_pos hdk hp psi hzero hqpos r,
    r.2⟩

theorem fordFiniteRawFrequencyToS3_of_pos_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q) :
    Function.Injective (fordFiniteRawFrequencyToS3_of_pos (p := p) (s := s)
      (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi hzero hqpos) := by
  intro a b hab
  apply Subtype.ext
  change a.1 = b.1
  simpa [fordFiniteRawFrequencyToS3_of_pos] using congrArg Subtype.val hab

theorem fordFiniteRawFrequency_card_le_targetZero_of_pos
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q) :
    Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
    Fintype.card {t : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi t j = 0} := by
  exact Fintype.card_le_of_injective
    (f := fun r => fordFiniteRawS3ToTargetZero hdk hp psi
      (fordFiniteRawFrequencyToS3_of_pos hdk hp psi hzero hqpos r))
    (fun a b hab =>
      fordFiniteRawFrequencyToS3_of_pos_injective hdk hp psi hzero hqpos
        (fordFiniteRawS3ToTargetZero_injective hdk hp psi hab))

theorem fordFiniteRawFrequency_integer_holder_of_pos
    {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q) :
    Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
      (Nat.factorial d * p ^ (2*s-d-1) : ℕ) *
        ∑ b : ZMod p, Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s)
          (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  apply le_trans (fordFiniteRawFrequency_card_le_targetZero_of_pos hdk hp psi hzero hqpos)
  simpa only [fixed_b_s4_card_eq] using
    (integer_target_holder (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hp hd hds hs hdk psi)

theorem fordFiniteRawFrequency_exists_fixed_residue_holder_of_pos
    {p s k d Q P q : ℕ} [NeZero p]
    (hp : p.Prime) (hd : d < p) (hds : d ≤ s) (hs : 0 < s)
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hqpos : 0 < q) :
    ∃ b : ZMod p,
      Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
        (Nat.factorial d * p ^ (2*s-d) : ℕ) *
          Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s)
            (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  let f : ZMod p → ℕ := fun b =>
    Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b)
  have hsource := fordFiniteRawFrequency_integer_holder_of_pos
    (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q)
    hp hd hds hs hdk psi hzero hqpos
  have huniv : (Finset.univ : Finset (ZMod p)).Nonempty := Finset.univ_nonempty
  obtain ⟨b, hb, hmax⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (ZMod p)) huniv f
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
end MAPFordPositiveQSourceHolder

#print axioms MAPFordPositiveQSourceHolder.fordFiniteRawFrequency_power_residue_eq_of_pos
#print axioms MAPFordPositiveQSourceHolder.fordFiniteRawFrequency_integer_holder_of_pos
#print axioms MAPFordPositiveQSourceHolder.fordFiniteRawFrequency_exists_fixed_residue_holder_of_pos
