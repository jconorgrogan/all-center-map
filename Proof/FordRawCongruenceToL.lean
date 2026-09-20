import FordP16SourceCountBridge
import FordLemma32LiteralContract

open scoped BigOperators
noncomputable section
namespace MAPFordRawCongruenceToL
open MAPFordP16FiniteFourierBridge MAPFordP16SourceCountBridge
open MAPFordLemma32LiteralContract

instance lPointFinite {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Finite (LPoint s k P Q p q r phi) := by
  apply Finite.of_injective (fun a : LPoint s k P Q p q r phi => ((a.z,a.w),(a.u,a.v)))
  intro a b h
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl,rfl⟩,rfl,rfl⟩
  rfl

instance lPointFintype {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype (LPoint s k P Q p q r phi) := Fintype.ofFinite _

def RawCongruent {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) : Type :=
  {a : fordFiniteRawFrequencyCarrier (p := p) (s := s) (k := k) (d := d)
      (Q := Q) (P := P) (q := p*q) hdk hp phi //
    ∀ i : Fin k, (a.1.1.1.1 i).val ≡ (a.1.2.1.1 i).val [MOD p^r]}

instance rawCongruentFintype {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) :
    Fintype (RawCongruent (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi) := by
  classical
  dsimp [RawCongruent]
  infer_instance

def rawCongruentToL {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ)
    (a : RawCongruent (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi) :
    LPoint s k P Q p q r phi := by
  let x := a.1.1
  refine {
    z := x.1.1.1
    w := x.2.1.1
    u := fun i => (x.1.2 i).1
    v := fun i => (x.2.2 i).1
    z_pos := x.1.1.2.1
    w_pos := x.2.1.2.1
    u_pos := fun i => (x.1.2 i).2
    v_pos := fun i => (x.2.2 i).2
    congruence := a.2
    equation := ?_ }
  intro j
  have h := a.1.2 j
  change fordSourceFrequencyAt phi x.1.1.1 j - fordSourceFrequencyAt phi x.2.1.1 j +
    fordQFrequencyAt (q := p*q) (fun i => (x.1.2 i).1) j -
    fordQFrequencyAt (q := p*q) (fun i => (x.2.2 i).1) j = 0 at h
  simp only [fordSourceFrequencyAt, fordQFrequencyAt, fordQScalarFrequency,
    ← Finset.mul_sum] at h
  change (∑ i : Fin k, ((phi j).eval ((x.1.1.1 i).val : ℤ) -
      (phi j).eval ((x.2.1.1 i).val : ℤ))) +
    ((p : ℤ)*(q : ℤ))^(j.val+1) * (∑ i : Fin s,
      (((x.1.2 i).1.val : ℤ)^(j.val+1) - ((x.2.2 i).1.val : ℤ)^(j.val+1))) = 0
  simp only [Finset.sum_sub_distrib, mul_sub]
  simpa only [Nat.cast_mul, sub_eq_add_neg, add_assoc] using h

lemma rawCongruentToL_injective {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) :
    Function.Injective (rawCongruentToL (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi) := by
  intro a b h
  have hz := congrArg LPoint.z h
  have hw := congrArg LPoint.w h
  have hu := congrArg LPoint.u h
  have hv := congrArg LPoint.v h
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext hz
    · funext i
      exact Subtype.ext (congrFun hu i)
  · apply Prod.ext
    · exact Subtype.ext hw
    · funext i
      exact Subtype.ext (congrFun hv i)

theorem rawCongruent_card_le_L {p s k d Q P q r : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (phi : Fin k → Polynomial ℤ) :
    Fintype.card (RawCongruent (s := s) (Q := Q) (P := P) (q := q) (r := r) hdk hp phi) ≤
      Fintype.card (LPoint s k P Q p q r phi) :=
  Fintype.card_le_of_injective _ (rawCongruentToL_injective hdk hp phi)

end MAPFordRawCongruenceToL
#print axioms MAPFordRawCongruenceToL.rawCongruent_card_le_L
