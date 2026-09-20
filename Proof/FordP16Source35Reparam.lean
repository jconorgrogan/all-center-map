import FordP16SourceHolder

open scoped BigOperators ZMod

namespace MAPFordP16Source35Reparam
noncomputable section
set_option maxHeartbeats 1000000

open MAPFordP16FiniteFourierBridge
open MAPFordP16SourceCountBridge

def negResidue {p : ℕ} [NeZero p] (b : ZMod p) : Fin p :=
  ⟨(-b).val, ZMod.val_lt (-b)⟩

lemma negResidue_cast {p : ℕ} [NeZero p] (b : ZMod p) :
    ((negResidue b).val : ZMod p) = -b := by
  exact ZMod.natCast_zmod_val (-b)

def shiftedU {p Q : ℕ} [NeZero p] (c : Fin p) : Type :=
  {u : Fin ((Q + c.val) / p + 1) // 1 ≤ u.val}

instance shiftedUFintype {p Q : ℕ} [NeZero p] (c : Fin p) :
    Fintype (shiftedU (p := p) (Q := Q) c) := by
  classical
  dsimp [shiftedU]
  infer_instance

lemma qCarrier_shift_dvd
    {p Q : ℕ} [NeZero p] (hp : p.Prime) (b : ZMod p)
    (x : fordFiniteQCarrier (p := p) (Q := Q) b) :
    p ∣ x.1.val + (negResidue b).val := by
  letI : Fact p.Prime := ⟨hp⟩
  have hcast : ((x.1.val + (negResidue b).val : ℕ) : ZMod p) = 0 := by
    rw [Nat.cast_add, x.2.2, negResidue_cast]
    abel
  rw [ZMod.natCast_eq_zero_iff] at hcast
  exact hcast

def qCarrierShift
    {p Q : ℕ} [NeZero p] (hp : p.Prime) (b : ZMod p)
    (x : fordFiniteQCarrier (p := p) (Q := Q) b) :
    shiftedU (p := p) (Q := Q) (negResidue b) := by
  let c := negResidue b
  let n := x.1.val + c.val
  have hxpos := x.2.1
  have hnpos : 0 < n := by dsimp [n]; omega
  have hdvd : p ∣ n := by simpa [n, c] using qCarrier_shift_dvd hp b x
  have hmod : n % p = 0 := Nat.mod_eq_zero_of_dvd hdvd
  have hquot : 0 < n / p := by
    exact Nat.div_pos (Nat.le_of_dvd hnpos hdvd) hp.pos
  have hupper : n / p ≤ (Q + c.val) / p := by
    apply Nat.div_le_div_right
    have hxle : x.1.val ≤ Q := by omega
    dsimp [n]
    omega
  refine ⟨⟨n / p, ?_⟩, hquot⟩
  exact Nat.lt_succ_of_le hupper

lemma qCarrierShift_value
    {p Q : ℕ} [NeZero p] (hp : p.Prime) (b : ZMod p)
    (x : fordFiniteQCarrier (p := p) (Q := Q) b) :
    (p : ℤ) * (qCarrierShift hp b x).1.val -
      ((negResidue b).val : ℤ) = (x.1.val : ℤ) := by
  have hdvd : p ∣ x.1.val + (negResidue b).val := qCarrier_shift_dvd hp b x
  have hmod : (x.1.val + (negResidue b).val) % p = 0 :=
    Nat.mod_eq_zero_of_dvd hdvd
  have hdecomp := Nat.mod_add_div (x.1.val + (negResidue b).val) p
  have hnat : p * ((x.1.val + (negResidue b).val) / p) -
      (negResidue b).val = x.1.val := by
    omega
  have hle : (negResidue b).val ≤
      p * ((x.1.val + (negResidue b).val) / p) := by omega
  have hcast :
      ((p * ((x.1.val + (negResidue b).val) / p) - (negResidue b).val : ℕ) : ℤ) =
        (x.1.val : ℤ) := by exact_mod_cast hnat
  rw [Int.ofNat_sub hle] at hcast
  dsimp [qCarrierShift]
  change (p : ℤ) * ((x.1.val + (negResidue b).val) / p) -
      ((negResidue b).val : ℤ) = (x.1.val : ℤ)
  simpa [Nat.cast_mul] using hcast

def source35Frequency
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (c : Fin p)
    (r : ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi) : Fin k → ℤ :=
  fordSourceFrequencyAt psi r.1.1.1.1 - fordSourceFrequencyAt psi r.2.1 +
    fun j => (q : ℤ) ^ (j.val + 1) *
      (∑ i : Fin s,
        (((p : ℤ) * (r.1.1.2 i).1.val - (c.val : ℤ)) ^ (j.val + 1) -
          ((p : ℤ) * (r.1.2 i).1.val - (c.val : ℤ)) ^ (j.val + 1)))

def source35Carrier
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) : Type :=
  {r : ((fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      (Fin s → shiftedU (p := p) (Q := Q) c)) ×
      fordFiniteFCarrier (p := p) (k := k) (d := d) (P := P) hdk hp psi //
    ∀ j, source35Frequency (q := q) hdk hp psi c r j = 0}

instance source35CarrierFintype
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (c : Fin p) :
    Fintype (source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q)
      (P := P) (q := q) hdk hp psi c) := by
  classical
  dsimp [source35Carrier]
  infer_instance

def rawS4ToSource35
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p)
    (r : fordFiniteRawS4Carrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) :
    source35Carrier (p := p) (s := s) (k := k) (d := d) (Q := Q) (P := P)
      (q := q) hdk hp psi (negResidue b) := by
  let c := negResidue b
  let z := r.1.1.1.1
  let w := r.1.2
  let x : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b := r.1.1.1.2
  let y : Fin s → fordFiniteQCarrier (p := p) (Q := Q) b := r.1.1.2
  let u : Fin s → shiftedU (p := p) (Q := Q) c :=
    fun i => qCarrierShift hp b (x i)
  let v : Fin s → shiftedU (p := p) (Q := Q) c :=
    fun i => qCarrierShift hp b (y i)
  refine ⟨(((z, u), v), w), ?_⟩
  intro j
  have hz := r.2 j
  change fordSourceFrequencyAt psi z.1 j - fordSourceFrequencyAt psi w.1 j +
      (fordQFrequencyAt (q := q) (fun i => (x i).1)) j -
        (fordQFrequencyAt (q := q) (fun i => (y i).1)) j = 0 at hz
  have hx : ∀ i : Fin s,
      (p : ℤ) * (u i).1.val - (c.val : ℤ) = ((x i).1.val : ℤ) := by
    intro i
    simpa [c] using qCarrierShift_value hp b (x i)
  have hy : ∀ i : Fin s,
      (p : ℤ) * (v i).1.val - (c.val : ℤ) = ((y i).1.val : ℤ) := by
    intro i
    simpa [c] using qCarrierShift_value hp b (y i)
  change fordSourceFrequencyAt psi z.1 j -
      fordSourceFrequencyAt psi w.1 j +
      (q : ℤ) ^ (j.val + 1) *
        (∑ i : Fin s,
            (((p : ℤ) * (u i).1.val - (c.val : ℤ)) ^ (j.val + 1) -
            ((p : ℤ) * (v i).1.val - (c.val : ℤ)) ^ (j.val + 1))) = 0
  simp_rw [hx, hy]
  change fordSourceFrequencyAt psi z.1 j -
      fordSourceFrequencyAt psi w.1 j +
      (q : ℤ) ^ (j.val + 1) *
        (∑ i : Fin s, (((x i).1.val : ℤ) ^ (j.val + 1) -
          ((y i).1.val : ℤ) ^ (j.val + 1))) = 0
  have hqexpand :
      (q : ℤ) ^ (j.val + 1) *
        (∑ i : Fin s, (((x i).1.val : ℤ) ^ (j.val + 1) -
          ((y i).1.val : ℤ) ^ (j.val + 1))) =
      fordQFrequencyAt (q := q) (fun i => (x i).1) j -
        fordQFrequencyAt (q := q) (fun i => (y i).1) j := by
    simp only [fordQFrequencyAt, fordQScalarFrequency]
    rw [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum]
  rw [hqexpand]
  linarith

lemma rawS4ToSource35_injective
    {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) (b : ZMod p) :
    Function.Injective (rawS4ToSource35 (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := q) hdk hp psi b) := by
  intro a b' hab
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · have hF := congrArg (fun z => z.1.1.1.1) hab
        dsimp [rawS4ToSource35] at hF
        exact hF
      · apply funext
        intro i
        have hu := congrArg (fun z => (z.1.1.1.2 i).1.val) hab
        have hxa := qCarrierShift_value hp _ (a.1.1.1.2 i)
        have hxb := qCarrierShift_value hp _ (b'.1.1.1.2 i)
        apply Subtype.ext
        apply Fin.ext
        have hu' :
            (qCarrierShift hp b (a.1.1.1.2 i)).1.val =
              (qCarrierShift hp b (b'.1.1.1.2 i)).1.val := by
          change (qCarrierShift hp b (a.1.1.1.2 i)).1.val =
            (qCarrierShift hp b (b'.1.1.1.2 i)).1.val at hu
          exact hu
        have hvalZ : ((a.1.1.1.2 i).1.val : ℤ) =
            ((b'.1.1.1.2 i).1.val : ℤ) := by
          calc
            _ = (p : ℤ) * (qCarrierShift hp b (a.1.1.1.2 i)).1.val -
                (negResidue b).val := hxa.symm
            _ = (p : ℤ) * (qCarrierShift hp b (b'.1.1.1.2 i)).1.val -
                (negResidue b).val := by rw [hu']
            _ = _ := hxb
        exact_mod_cast hvalZ
    · apply funext
      intro i
      have hu := congrArg (fun z => (z.1.1.2 i).1.val) hab
      have hxa := qCarrierShift_value hp _ (a.1.1.2 i)
      have hxb := qCarrierShift_value hp _ (b'.1.1.2 i)
      apply Subtype.ext
      apply Fin.ext
      have hu' :
          (qCarrierShift hp b (a.1.1.2 i)).1.val =
            (qCarrierShift hp b (b'.1.1.2 i)).1.val := by
        change (qCarrierShift hp b (a.1.1.2 i)).1.val =
          (qCarrierShift hp b (b'.1.1.2 i)).1.val at hu
        exact hu
      have hvalZ : ((a.1.1.2 i).1.val : ℤ) =
          ((b'.1.1.2 i).1.val : ℤ) := by
        calc
          _ = (p : ℤ) * (qCarrierShift hp b (a.1.1.2 i)).1.val -
              (negResidue b).val := hxa.symm
          _ = (p : ℤ) * (qCarrierShift hp b (b'.1.1.2 i)).1.val -
              (negResidue b).val := by rw [hu']
          _ = _ := hxb
      exact_mod_cast hvalZ
  · have hW := congrArg (fun z => z.1.2) hab
    dsimp [rawS4ToSource35] at hW
    exact hW

end
end MAPFordP16Source35Reparam

#print axioms MAPFordP16Source35Reparam.rawS4ToSource35_injective
