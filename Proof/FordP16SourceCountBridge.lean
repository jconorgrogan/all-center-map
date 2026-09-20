import FordP16IntegerHolder

open scoped BigOperators ZMod

namespace MAPFordP16SourceCountBridge
noncomputable section

open MAPFordP16FiniteFourierBridge
open MAPFordP16FiniteTargetCount
open MAPFordP16IntegerHolder

def fordFinitePositiveX {Q : ℕ} : Type :=
  {x : Fin (Q + 1) // 1 ≤ x.val}

instance fordFinitePositiveXFintype {Q : ℕ} : Fintype (fordFinitePositiveX (Q := Q)) := by
  classical
  dsimp [fordFinitePositiveX]
  infer_instance

abbrev fordFiniteRawTuple {s Q : ℕ} : Type :=
  Fin s → fordFinitePositiveX (Q := Q)

instance fordFiniteRawTupleFintype {s Q : ℕ} :
    Fintype (fordFiniteRawTuple (s := s) (Q := Q)) := by
  classical
  dsimp [fordFiniteRawTuple]
  infer_instance

def fordFiniteRawPowerResidue {p s d Q : ℕ} [NeZero p]
    (x : fordFiniteRawTuple (s := s) (Q := Q)) : Fin d → ZMod p :=
  fun j => ∑ i : Fin s, ((x i).1.val : ZMod p) ^ (j.val + 1)

def fordFiniteRawFrequency
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) ×
      (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q))) : Fin k → ℤ :=
  fordSourceFrequencyAt psi r.1.1.1 - fordSourceFrequencyAt psi r.2.1.1 +
    fordQFrequencyAt (q := q) (fun i => (r.1.2 i).1) -
    fordQFrequencyAt (q := q) (fun i => (r.2.2 i).1)

def fordFiniteRawS3Carrier
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) : Type :=
  {r : (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) ×
      (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) //
    fordFiniteRawPowerResidue (p := p) (d := d) r.1.2 =
        fordFiniteRawPowerResidue (p := p) (d := d) r.2.2 ∧
      ∀ j, fordFiniteRawFrequency (q := q) hdk hp psi r j = 0}

instance fordFiniteRawS3CarrierFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Fintype (fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) := by
  classical
  dsimp [fordFiniteRawS3Carrier]
  infer_instance

/- A frequency-only raw carrier.  Its power-residue equality is recovered
   below from the low-coordinate frequency equations when `p ∤ q` and the
   low source polynomials vanish. -/
abbrev fordFiniteRawFrequencyCarrier
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) : Type :=
  {r : (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) ×
      (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) //
    ∀ j, fordFiniteRawFrequency (q := q) hdk hp psi r j = 0}

instance fordFiniteRawFrequencyCarrierFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Fintype (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) := by
  classical
  dsimp [fordFiniteRawFrequencyCarrier]
  infer_instance

lemma fordFiniteRawSourceFrequency_zero_of_low
    {k d P : ℕ}
    (hdk : d ≤ k) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (z : Fin k → Fin (P + 1)) (j : Fin d) :
    fordSourceFrequencyAt psi z (Fin.castLE hdk j) = 0 := by
  simp [fordSourceFrequencyAt, hzero j]

lemma fordFiniteRawFrequency_power_residue_eq
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q)
    (r : fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteRawPowerResidue (p := p) (d := d) r.1.1.2 =
      fordFiniteRawPowerResidue (p := p) (d := d) r.1.2.2 := by
  letI : Fact p.Prime := ⟨hp⟩
  funext j
  have hfreq := r.2 (Fin.castLE hdk j)
  have hx := fordFiniteRawSourceFrequency_zero_of_low hdk psi hzero (r.1.1.1).1 j
  have hy := fordFiniteRawSourceFrequency_zero_of_low hdk psi hzero (r.1.2.1).1 j
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
          (q : ℤ) ^ ((Fin.castLE hdk j).val + 1) * ((r.1.1.2 i).1.val : ℤ) ^
            ((Fin.castLE hdk j).val + 1) := by rfl
      _ = ∑ i : Fin s, fordQScalarFrequency (q := q) (r.1.1.2 i).1
          (Fin.castLE hdk j) := by rfl
      _ = fordQFrequencyAt (q := q) (fun i => (r.1.1.2 i).1) (Fin.castLE hdk j) := by rfl
      _ = fordQFrequencyAt (q := q) (fun i => (r.1.2.2 i).1) (Fin.castLE hdk j) := hqfreq
      _ = ∑ i : Fin s, fordQScalarFrequency (q := q) (r.1.2.2 i).1
          (Fin.castLE hdk j) := by rfl
      _ = ∑ i : Fin s,
          (q : ℤ) ^ ((Fin.castLE hdk j).val + 1) * ((r.1.2.2 i).1.val : ℤ) ^
            ((Fin.castLE hdk j).val + 1) := by rfl
      _ = ∑ i : Fin s,
          (q : ℤ) ^ (j.val + 1) * ((r.1.2.2 i).1.val : ℤ) ^ (j.val + 1) := by rfl
      _ = _ := by rw [← Finset.mul_sum]
  have hqcast : (q : ZMod p) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hq
  have hcast := congrArg (fun z : ℤ => (z : ZMod p)) hqint
  have hpow : (q : ZMod p) ^ (j.val + 1) ≠ 0 := pow_ne_zero _ hqcast
  have hsum :
      (q : ZMod p) ^ (j.val + 1) *
          (∑ i : Fin s, ((r.1.1.2 i).1.val : ZMod p) ^ (j.val + 1)) =
        (q : ZMod p) ^ (j.val + 1) *
          (∑ i : Fin s, ((r.1.2.2 i).1.val : ZMod p) ^ (j.val + 1)) := by
    simpa [Int.cast_mul, Int.cast_pow, Int.cast_sum] using hcast
  exact mul_left_cancel₀ hpow hsum

def fordFiniteRawFrequencyToS3
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q)
    (r : fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi :=
  ⟨r.1, fordFiniteRawFrequency_power_residue_eq hdk hp psi hzero hq r, r.2⟩

theorem fordFiniteRawFrequencyToS3_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q) :
    Function.Injective (fordFiniteRawFrequencyToS3 (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi hzero hq) := by
  intro a b hab
  apply Subtype.ext
  change a.1 = b.1
  simpa [fordFiniteRawFrequencyToS3] using congrArg Subtype.val hab

def fordFiniteRawToTargetState
    {L p s k d Q : ℕ} [NeZero L] [NeZero p]
    (x : fordFiniteRawTuple (s := s) (Q := Q)) :
    fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q)
      (fordFiniteRawPowerResidue (p := p) (d := d) x) := by
  refine ⟨⟨fun i => ((x i).1.val : ZMod p), ?_⟩, ?_⟩
  · intro j
    rfl
  · intro i
    exact ⟨(x i).1, (x i).2, rfl⟩

lemma targetState_cast_qval
    {p s d Q : ℕ} [NeZero p]
    {t t' : Fin d → ZMod p} (h : t = t')
    (v : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) t) :
    ∀ i, ((h ▸ v).2 i).1 = (v.2 i).1 := by
  intro i
  cases h
  rfl

def fordFiniteTargetStateRawValue
    {p s d Q : ℕ} [NeZero p]
    {target : Fin d → ZMod p}
    (u : fordFiniteTargetState (p := p) (s := s) (d := d) (Q := Q) target) :
    fordFiniteRawTuple (s := s) (Q := Q) :=
  fun i => ⟨(u.2 i).1, (u.2 i).2.1⟩

lemma fordFiniteTargetStateRawValue_rawToTarget
    {p s d Q : ℕ} [NeZero p]
    (x : fordFiniteRawTuple (s := s) (Q := Q)) :
    fordFiniteTargetStateRawValue
      (fordFiniteRawToTargetState (L := 1) (p := p) (s := s) (k := 0) (d := d)
        (Q := Q) x) = x := by
  funext i
  apply Subtype.ext
  rfl

def fordFiniteRawS3ToTargetZero
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    {t : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi t j = 0} := by
  let target := fordFiniteRawPowerResidue (p := p) (d := d) r.1.1.2
  let u := fordFiniteRawToTargetState (L := 1) (p := p) (s := s) (k := k) (d := d)
    (Q := Q) r.1.1.2
  let v0 := fordFiniteRawToTargetState (L := 1) (p := p) (s := s) (k := k) (d := d)
    (Q := Q) r.1.2.2
  let v := r.2.1.symm ▸ v0
  refine ⟨((r.1.1.1, ⟨target, (u, v)⟩), r.1.2.1), ?_⟩
  intro j
  have hz := r.2.2 j
  have hvval := targetState_cast_qval (p := p) (s := s) (d := d) (Q := Q)
    (h := r.2.1.symm) (v := v0)
  have hqv : ∀ j : Fin k,
      fordQFrequencyAt (q := q) (fun i => (v.2 i).1) j =
        fordQFrequencyAt (q := q) (fun i => (r.1.2.2 i).1) j := by
    intro j
    have hfun : (fun i => (v.2 i).1) = (fun i => (v0.2 i).1) := by
      funext i
      exact hvval i
    rw [hfun]
    rfl
  change
    fordSourceFrequencyAt psi ((r.1.1).1).1 j - fordSourceFrequencyAt psi ((r.1.2).1).1 j +
      fordQFrequencyAt (q := q) (fun i => ((r.1.1).2 i).1) j -
      fordQFrequencyAt (q := q) (fun i => (v.2 i).1) j = 0
  rw [hqv j]
  exact hz

def fordFiniteTargetZeroRawProjection
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (t : {t : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi t j = 0}) :
    ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q)) ×
     (fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      fordFiniteRawTuple (s := s) (Q := Q))) :=
  ((t.1.1.1, fordFiniteTargetStateRawValue t.1.1.2.2.1),
    (t.1.2, fordFiniteTargetStateRawValue t.1.1.2.2.2))

lemma fordFiniteTargetZeroRawProjection_map
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteTargetZeroRawProjection hdk hp psi
      (fordFiniteRawS3ToTargetZero hdk hp psi r) = r.1 := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply funext
      intro i
      apply Subtype.ext
      rfl
  · apply Prod.ext
    · rfl
    · apply funext
      intro i
      apply Subtype.ext
      have hv := targetState_cast_qval (p := p) (s := s) (d := d) (Q := Q)
        (h := r.2.1.symm)
        (v := fordFiniteRawToTargetState (L := 1) (p := p) (s := s)
          (k := k) (d := d) (Q := Q) r.1.2.2)
      dsimp [fordFiniteTargetZeroRawProjection, fordFiniteRawS3ToTargetZero,
        fordFiniteTargetStateRawValue]
      exact hv i

theorem fordFiniteRawS3ToTargetZero_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Function.Injective (fordFiniteRawS3ToTargetZero (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi) := by
  intro a b hab
  apply Subtype.ext
  have hpj := congrArg (fordFiniteTargetZeroRawProjection hdk hp psi) hab
  rw [fordFiniteTargetZeroRawProjection_map hdk hp psi a,
    fordFiniteTargetZeroRawProjection_map hdk hp psi b] at hpj
  exact hpj

theorem fordFiniteRawS3_card_le_targetZero
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Fintype.card (fordFiniteRawS3Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) ≤
    Fintype.card {t : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi t j = 0} := by
  exact Fintype.card_le_of_injective
    (f := fordFiniteRawS3ToTargetZero (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi)
    (fordFiniteRawS3ToTargetZero_injective (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi)

theorem fordFiniteRawFrequency_card_le_targetZero
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (hzero : ∀ j : Fin d, psi (Fin.castLE hdk j) = 0)
    (hq : ¬ p ∣ q) :
    Fintype.card (fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi) ≤
    Fintype.card {t : fordFiniteTargetPair (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi //
      ∀ j, fordFiniteTargetPairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi t j = 0} := by
  exact Fintype.card_le_of_injective
    (f := fun r => fordFiniteRawS3ToTargetZero hdk hp psi
      (fordFiniteRawFrequencyToS3 hdk hp psi hzero hq r))
    (fun a b hab =>
      fordFiniteRawFrequencyToS3_injective hdk hp psi hzero hq
        (fordFiniteRawS3ToTargetZero_injective hdk hp psi hab))

abbrev fordFiniteRawS4Carrier
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) : Type :=
  {r : fordFinitePair (L := 1) (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) hdk hp psi b //
    ∀ j, fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0}

instance fordFiniteRawS4CarrierFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) : Fintype (fordFiniteRawS4Carrier (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  classical
  dsimp [fordFiniteRawS4Carrier]
  infer_instance

lemma fixed_b_s4_card_eq
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (b : ZMod p) :
    Fintype.card (fordFiniteRawS4Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) =
    Fintype.card {r : fordFinitePair (L := 1) (p := p) (s := s) (k := k)
      (d := d) (Q := Q) (P := P) hdk hp psi b //
      ∀ j, fordFinitePairFrequency (L := 1) (p := p) (s := s) (k := k)
        (d := d) (Q := Q) (P := P) (q := q) hdk hp psi b r j = 0} := by
  rfl

end
end MAPFordP16SourceCountBridge

#print axioms MAPFordP16SourceCountBridge.fixed_b_s4_card_eq
#print axioms MAPFordP16SourceCountBridge.fordFiniteRawS3ToTargetZero_injective
#print axioms MAPFordP16SourceCountBridge.fordFiniteRawS3_card_le_targetZero
#print axioms MAPFordP16SourceCountBridge.fordFiniteRawFrequency_power_residue_eq
#print axioms MAPFordP16SourceCountBridge.fordFiniteRawFrequencyToS3_injective
#print axioms MAPFordP16SourceCountBridge.fordFiniteRawFrequency_card_le_targetZero
