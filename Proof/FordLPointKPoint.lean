import FordMaskedKToRaw
import FordRawCongruenceToL

open scoped BigOperators
open MAPFordLemma32LiteralContract

noncomputable section
namespace FordLPointKPoint

/-- The K-point carrier with the full source congruence mask carried as a subtype. -/
abbrev KPointWithCongruence
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :=
  {a : KPoint s k P Q phi (p * q) //
    ∀ i : Fin k, Nat.ModEq (p ^ r) (a.z i).val (a.w i).val}

instance kPointWithCongruenceFintype
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype (KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi) := by
  classical
  unfold KPointWithCongruence
  infer_instance

def lPointToKPoint
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : LPoint s k P Q p q r phi) :
    KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi := by
  refine ⟨{
    z := a.z
    w := a.w
    x := a.u
    y := a.v
    z_pos := a.z_pos
    w_pos := a.w_pos
    x_pos := a.u_pos
    y_pos := a.v_pos
    equation := a.equation }, ?_⟩
  exact a.congruence

def kPointToLPoint
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi) :
    LPoint s k P Q p q r phi := by
  refine {
    z := a.1.z
    w := a.1.w
    u := a.1.x
    v := a.1.y
    z_pos := a.1.z_pos
    w_pos := a.1.w_pos
    u_pos := a.1.x_pos
    v_pos := a.1.y_pos
    congruence := a.2
    equation := a.1.equation }

lemma lPointToKPoint_z
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : LPoint s k P Q p q r phi) (i : Fin k) :
    (lPointToKPoint phi a).1.z i = a.z i := by
  rfl

lemma lPointToKPoint_w
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : LPoint s k P Q p q r phi) (i : Fin k) :
    (lPointToKPoint phi a).1.w i = a.w i := by
  rfl

lemma kPointToLPoint_z
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi) (i : Fin k) :
    (kPointToLPoint phi a).z i = a.1.z i := by
  rfl

lemma kPointToLPoint_w
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi) (i : Fin k) :
    (kPointToLPoint phi a).w i = a.1.w i := by
  rfl

def lPointKPointEquiv
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    LPoint s k P Q p q r phi ≃
      KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi := by
  refine {
    toFun := lPointToKPoint phi
    invFun := kPointToLPoint phi
    left_inv := ?_
    right_inv := ?_ }
  · intro a
    cases a
    rfl
  · intro a
    apply Subtype.ext
    simp [lPointToKPoint, kPointToLPoint]

theorem lPoint_card_eq_kPointWithCongruence
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype.card (LPoint s k P Q p q r phi) =
      Fintype.card
        (KPointWithCongruence (s := s) (k := k) (P := P) (Q := Q)
          (p := p) (q := q) (r := r) phi) :=
  Fintype.card_congr (lPointKPointEquiv phi)

end FordLPointKPoint

#print axioms FordLPointKPoint.lPointKPointEquiv
#print axioms FordLPointKPoint.lPoint_card_eq_kPointWithCongruence
