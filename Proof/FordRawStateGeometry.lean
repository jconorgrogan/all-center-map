import FordRawCongruenceToL

open scoped BigOperators
noncomputable section
namespace MAPFordRawStateGeometry
open MAPFordP16FiniteFourierBridge MAPFordP16SourceCountBridge MAPFordRawCongruenceToL

abbrev RawState {p s k d Q P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (phi : Fin k → Polynomial ℤ) :=
  fordFiniteFCarrier (p := p) (P := P) hdk hp phi × fordFiniteRawTuple (s := s) (Q := Q)

def total {p s k d Q P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (phi : Fin k → Polynomial ℤ) (q : ℕ)
    (a : RawState (s := s) (Q := Q) (P := P) hdk hp phi) : Fin k → ℤ :=
  fordSourceFrequencyAt phi a.1.1 + fordQFrequencyAt (q := p*q) (fun i => (a.2 i).1)

def residue {p s k d Q P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (phi : Fin k → Polynomial ℤ) (r : ℕ)
    (a : RawState (s := s) (Q := Q) (P := P) hdk hp phi) : Fin k → Fin (p^r) :=
  fun i => ⟨(a.1.1 i).val % (p^r), Nat.mod_lt _ (pow_pos hp.pos _)⟩

lemma residue_eq_iff {p s k d Q P : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (phi : Fin k → Polynomial ℤ) (r : ℕ)
    (a b : RawState (s := s) (Q := Q) (P := P) hdk hp phi) :
    residue hdk hp phi r a = residue hdk hp phi r b ↔
      ∀ i : Fin k, (a.1.1 i).val ≡ (b.1.1 i).val [MOD p^r] := by
  constructor
  · intro h i
    exact congrArg Fin.val (congrFun h i)
  · intro h
    funext i
    exact Fin.ext (h i)

lemma raw_frequency_iff_total {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ)
    (a b : RawState (s := s) (Q := Q) (P := P) hdk hp phi) :
    (∀ j, fordFiniteRawFrequency (q := p*q) hdk hp phi (a,b) j = 0) ↔
      total hdk hp phi q a = total hdk hp phi q b := by
  constructor
  · intro h
    funext j
    have hh := h j
    change fordSourceFrequencyAt phi a.1.1 j - fordSourceFrequencyAt phi b.1.1 j +
      fordQFrequencyAt (q := p*q) (fun i => (a.2 i).1) j -
      fordQFrequencyAt (q := p*q) (fun i => (b.2 i).1) j = 0 at hh
    change fordSourceFrequencyAt phi a.1.1 j + fordQFrequencyAt (q := p*q) (fun i => (a.2 i).1) j =
      fordSourceFrequencyAt phi b.1.1 j + fordQFrequencyAt (q := p*q) (fun i => (b.2 i).1) j
    linarith
  · intro h j
    have hh := congrFun h j
    change fordSourceFrequencyAt phi a.1.1 j + fordQFrequencyAt (q := p*q) (fun i => (a.2 i).1) j =
      fordSourceFrequencyAt phi b.1.1 j + fordQFrequencyAt (q := p*q) (fun i => (b.2 i).1) j at hh
    change fordSourceFrequencyAt phi a.1.1 j - fordSourceFrequencyAt phi b.1.1 j +
      fordQFrequencyAt (q := p*q) (fun i => (a.2 i).1) j -
      fordQFrequencyAt (q := p*q) (fun i => (b.2 i).1) j = 0
    linarith

def rawEquivCollision {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) :
    fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P) (q := p*q) hdk hp phi ≃
      {a : RawState (s := s) (Q := Q) (P := P) hdk hp phi × RawState (s := s) (Q := Q) (P := P) hdk hp phi //
        total hdk hp phi q a.1 = total hdk hp phi q a.2} :=
  { toFun := fun a => ⟨a.1, (raw_frequency_iff_total hdk hp phi _ _).mp a.2⟩
    invFun := fun a => ⟨a.1, (raw_frequency_iff_total hdk hp phi _ _).mpr a.2⟩
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl }

def restrictedEquivRawCongruent {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) :
    {a : RawState (s := s) (Q := Q) (P := P) hdk hp phi × RawState (s := s) (Q := Q) (P := P) hdk hp phi //
      total hdk hp phi q a.1 = total hdk hp phi q a.2 ∧
      residue hdk hp phi r a.1 = residue hdk hp phi r a.2} ≃
    RawCongruent (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi :=
  { toFun := fun a => ⟨⟨a.1, (raw_frequency_iff_total hdk hp phi _ _).mpr a.2.1⟩,
      (residue_eq_iff hdk hp phi r _ _).mp a.2.2⟩
    invFun := fun a => ⟨a.1.1, (raw_frequency_iff_total hdk hp phi _ _).mp a.1.2,
      (residue_eq_iff hdk hp phi r _ _).mpr a.2⟩
    left_inv := by intro a; rfl
    right_inv := by intro a; rfl }

end MAPFordRawStateGeometry
#print axioms MAPFordRawStateGeometry.rawEquivCollision
#print axioms MAPFordRawStateGeometry.restrictedEquivRawCongruent
