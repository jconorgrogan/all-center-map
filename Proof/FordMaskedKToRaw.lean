import FordP16SourceCountBridge
import FordLemma32LiteralContract

open scoped BigOperators
noncomputable section
namespace MAPFordMaskedKToRaw
open MAPFordP16FiniteFourierBridge MAPFordP16SourceCountBridge
open MAPFordP16LiteralResidueBridge MAPFordLemma32LiteralContract

instance kPointFinite {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) :
    Finite (KPoint s k P Q psi q) := by
  apply Finite.of_injective (fun a : KPoint s k P Q psi q => ((a.z,a.w),(a.x,a.y)))
  intro a b h
  cases a
  cases b
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨⟨rfl,rfl⟩,rfl,rfl⟩
  rfl

instance kPointFintype {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) :
    Fintype (KPoint s k P Q psi q) := Fintype.ofFinite _

/-- The literal K solutions satisfying both source Jacobian masks. -/
def MaskedK {p s k d Q P q : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) :=
  {a : KPoint s k P Q psi q // fordPolynomialMask hdk hp psi a.z ∧
    fordPolynomialMask hdk hp psi a.w}

instance maskedKFintype {p s k d Q P q : ℕ} (hdk : d ≤ k) (hp : p.Prime)
    (psi : Fin k → Polynomial ℤ) :
    Fintype (MaskedK (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) := by
  classical
  dsimp [MaskedK]
  infer_instance

def maskedKToRaw {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ)
    (a : MaskedK (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) :
    fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi := by
  refine ⟨((⟨a.1.z,a.2.1⟩,fun i => ⟨a.1.x i,a.1.x_pos i⟩),
    (⟨a.1.w,a.2.2⟩,fun i => ⟨a.1.y i,a.1.y_pos i⟩)), ?_⟩
  intro j
  have h := a.1.equation j
  change fordSourceFrequencyAt psi a.1.z j - fordSourceFrequencyAt psi a.1.w j +
    fordQFrequencyAt (q := q) a.1.x j - fordQFrequencyAt (q := q) a.1.y j = 0
  simp only [fordSourceFrequencyAt, fordQFrequencyAt, fordQScalarFrequency,
    ← Finset.mul_sum]
  simp only [Finset.sum_sub_distrib, mul_sub] at h
  linarith only [h]

lemma maskedKToRaw_injective {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Function.Injective (maskedKToRaw (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) := by
  intro a b h
  have hz := congrArg (fun u => u.1.1.1.1) h
  have hw := congrArg (fun u => u.1.2.1.1) h
  have hx := congrArg (fun u => fun i => (u.1.1.2 i).1) h
  have hy := congrArg (fun u => fun i => (u.1.2.2 i).1) h
  change a.1.z = b.1.z at hz
  change a.1.w = b.1.w at hw
  change a.1.x = b.1.x at hx
  change a.1.y = b.1.y at hy
  apply Subtype.ext
  cases a with | mk a ha =>
    cases b with | mk b hb =>
      cases a
      cases b
      cases hz
      cases hw
      cases hx
      cases hy
      rfl

theorem maskedK_card_le_raw {p s k d Q P q : ℕ} [NeZero p]
    (hdk : d ≤ k) (hp : p.Prime) (psi : Fin k → Polynomial ℤ) :
    Fintype.card (MaskedK (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) ≤
      Fintype.card (fordFiniteRawFrequencyCarrier (s := s) (Q := Q) (P := P) (q := q) hdk hp psi) :=
  Fintype.card_le_of_injective _ (maskedKToRaw_injective hdk hp psi)

end MAPFordMaskedKToRaw
#print axioms MAPFordMaskedKToRaw.maskedK_card_le_raw
