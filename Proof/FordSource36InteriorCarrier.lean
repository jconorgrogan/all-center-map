import FordSource36TransportLight

open scoped BigOperators ZMod
namespace MAPFordSource36InteriorCarrier
noncomputable section
set_option maxHeartbeats 100000
open MAPFordP16FiniteFourierBridge MAPFordP16Source35Reparam
open MAPFordP16SourceCountBridge MAPFordP16Source35Triangular
open MAPFordP16LiteralResidueBridge

private lemma frequency_algebra {s : ℕ} (A B C : ℤ) (u v : Fin s → ℤ)
    (h : A - B + C * (∑ i, (u i - v i)) = 0) :
    A - B + (∑ i, C * u i) - (∑ i, C * v i) = 0 := by
  rw [Finset.sum_sub_distrib, mul_sub] at h
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  linarith only [h]

abbrev CoordinateRecord (k s : ℕ) :=
  ((Fin k → ℕ) × (Fin s → ℕ)) × ((Fin k → ℕ) × (Fin s → ℕ))

def sourceRecord {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (r : source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) : CoordinateRecord k s :=
  ((fun i => (r.1.1.1.1.1.1 i).val, fun i => (r.1.1.1.1.2 i).1.val),
    (fun i => (r.1.1.2.1 i).val, fun i => (r.1.1.1.2 i).1.val))

def rawRecord {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (r : fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) : CoordinateRecord k s :=
  ((fun i => (r.1.1.1.1 i).val, fun i => (r.1.1.2 i).1.val),
    (fun i => (r.1.2.1.1 i).val, fun i => (r.1.2.2 i).1.val))

lemma sourceRecord_injective {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Function.Injective (sourceRecord (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) := by
  intro a b h
  have hz := congrArg (fun t : CoordinateRecord k s => t.1.1) h
  have hu := congrArg (fun t : CoordinateRecord k s => t.1.2) h
  have hw := congrArg (fun t : CoordinateRecord k s => t.2.1) h
  have hv := congrArg (fun t : CoordinateRecord k s => t.2.2) h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · apply Subtype.ext
        funext i
        exact Fin.ext (congrFun hz i)
      · funext i
        apply Subtype.ext
        exact Fin.ext (congrFun hu i)
    · funext i
      apply Subtype.ext
      exact Fin.ext (congrFun hv i)
  · apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hw i)

/-- Explicit frequency conversion, checked independently of carrier construction. -/
lemma transport_frequency {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (r : source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c)
    (j : Fin k) :
    fordFiniteRawFrequency (Q := Q/p) (q := p*q) hdk hp
      (phiRow psi (q : ℤ) (c.val : ℤ))
      ((MAPFordSource36TransportLight.transportF hdk hp psi (q : ℤ) (c.val : ℤ) hzero r.1.1.1.1.1,
        interiorTuple c r.1.1.1.1.2 r.2.1),
       (MAPFordSource36TransportLight.transportF hdk hp psi (q : ℤ) (c.val : ℤ) hzero r.1.1.2,
        interiorTuple c r.1.1.1.2 r.2.2)) j = 0 := by
  unfold fordFiniteRawFrequency
  simp only [Pi.sub_apply, Pi.add_apply, MAPFordSource36TransportLight.transportF_val, interiorTuple,
    interiorPositiveX, fordQFrequencyAt]
  exact frequency_algebra
    (fordSourceFrequencyAt (phiRow psi (q : ℤ) (c.val : ℤ)) r.1.1.1.1.1.1 j)
    (fordSourceFrequencyAt (phiRow psi (q : ℤ) (c.val : ℤ)) r.1.1.2.1 j)
    (((p*q : ℕ) : ℤ)^(j.val+1))
    (fun i => ((r.1.1.1.1.2 i).1.val : ℤ)^(j.val+1))
    (fun i => ((r.1.1.1.2 i).1.val : ℤ)^(j.val+1)) (r.1.2 j)

theorem exists_raw_with_record {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (r : source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) :
    ∃ t : fordFiniteRawFrequencyCarrier (s := s) (Q := Q/p) (P := P) (q := p*q)
        hdk hp (phiRow psi (q : ℤ) (c.val : ℤ)),
      rawRecord hdk hp (phiRow psi (q : ℤ) (c.val : ℤ)) t =
      sourceRecord hdk hp psi c r := by
  refine ⟨⟨((MAPFordSource36TransportLight.transportF hdk hp psi (q : ℤ) (c.val : ℤ) hzero r.1.1.1.1.1,
        interiorTuple c r.1.1.1.1.2 r.2.1),
       (MAPFordSource36TransportLight.transportF hdk hp psi (q : ℤ) (c.val : ℤ) hzero r.1.1.2,
        interiorTuple c r.1.1.1.2 r.2.2)), transport_frequency hdk hp psi c hzero r⟩, ?_⟩
  simp only [rawRecord, sourceRecord, MAPFordSource36TransportLight.transportF_val,
    interiorTuple, interiorPositiveX]

def source36InteriorToRaw {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (r : source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) :
    fordFiniteRawFrequencyCarrier (s := s) (Q := Q/p) (P := P) (q := p*q)
      hdk hp (phiRow psi (q : ℤ) (c.val : ℤ)) :=
  Classical.choose (exists_raw_with_record (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi c hzero r)

lemma source36InteriorToRaw_record {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0)
    (r : source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) :
    rawRecord (p := p) (s := s) (k := k) (d := d) (Q := Q/p) (P := P) (q := p*q)
      hdk hp (phiRow psi (q : ℤ) (c.val : ℤ)) (source36InteriorToRaw hdk hp psi c hzero r) =
    sourceRecord (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi c r :=
  Classical.choose_spec (exists_raw_with_record (p := p) (s := s) (k := k) (d := d)
    (Q := Q) (P := P) (q := q) hdk hp psi c hzero r)

lemma source36InteriorToRaw_injective {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0) :
    Function.Injective (source36InteriorToRaw (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c hzero) := by
  intro a b h
  apply sourceRecord_injective (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P) (q := q) hdk hp psi c
  have hv := congrArg (rawRecord (p := p) (s := s) (k := k) (d := d) (Q := Q/p)
    (P := P) (q := p*q) hdk hp (phiRow psi (q : ℤ) (c.val : ℤ))) h
  rw [source36InteriorToRaw_record, source36InteriorToRaw_record] at hv
  exact hv

theorem source36Interior_card_le_rawFrequency_card {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p)
    (hzero : ∀ i : Fin k, i.val < d → psi i = 0) :
    Fintype.card (source36Interior (s := s) (Q := Q) (P := P) (q := q) hdk hp psi c) ≤
    Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q/p) (P := P) (q := p*q)
      hdk hp (phiRow psi (q : ℤ) (c.val : ℤ))) :=
  Fintype.card_le_of_injective
    (f := source36InteriorToRaw (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c hzero)
    (source36InteriorToRaw_injective (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi c hzero)

end
end MAPFordSource36InteriorCarrier
#print axioms MAPFordSource36InteriorCarrier.exists_raw_with_record
#print axioms MAPFordSource36InteriorCarrier.source36InteriorToRaw_injective
#print axioms MAPFordSource36InteriorCarrier.source36Interior_card_le_rawFrequency_card
