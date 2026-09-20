import FordClassEnergyMoment
import FordGoodKEnergy
import FordLPointKPoint

open scoped BigOperators
open MAPFordLemma32LiteralContract
open FordBoundaryCountGeometry
open FordClassEnergyMoment

noncomputable section
namespace FordLPointClassEnergy

abbrev SourcePoint {P : ℕ} := FordKPointEnergy.SourcePoint (P := P)
abbrev PowerWord {s Q : ℕ} := FordKPointEnergy.PowerWord (s := s) (Q := Q)

/-- The residue class of a positive source coordinate, retained in the ambient
`Fin (P+1)` carrier so this remains well-typed even when the modulus is zero. -/
def positiveResidueClass {P p r : ℕ} (z : SourcePoint (P := P)) : Fin (P + 1) :=
  ⟨z.1.val % (p ^ r), by
    have hz := Nat.mod_le z.1.val (p ^ r)
    omega⟩

abbrev LClassEnergyZero
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :=
  ClassEnergyZero
    (fun x : PowerWord (s := s) (Q := Q) =>
      FordKPointEnergy.baseFreq (q := p * q) x)
    (fun z : SourcePoint (P := P) =>
      FordKPointEnergy.sourceFreq phi z)
    (fun z : SourcePoint (P := P) => positiveResidueClass (p := p) (r := r) z)
    k

instance lClassEnergyZeroFintype
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype (LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi) := by
  unfold LClassEnergyZero
  infer_instance

private lemma source_class_eq_of_modEq
    {P p r : ℕ} (z w : SourcePoint (P := P))
    (h : Nat.ModEq (p ^ r) z.1.val w.1.val) :
    positiveResidueClass (p := p) (r := r) z =
      positiveResidueClass (p := p) (r := r) w := by
  apply Fin.ext
  change z.1.val % (p ^ r) = w.1.val % (p ^ r) at h
  exact h

private lemma modEq_of_source_class_eq
    {P p r : ℕ} (z w : SourcePoint (P := P))
    (h : positiveResidueClass (p := p) (r := r) z =
      positiveResidueClass (p := p) (r := r) w) :
    Nat.ModEq (p ^ r) z.1.val w.1.val := by
  exact congrArg Fin.val h

def kPointClassEnergyEquiv
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    FordLPointKPoint.KPointWithCongruence
        (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi ≃
      LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi := by
  let E := FordKPointEnergy.kPointEnergyEquiv
    (s := s) (k := k) (P := P) (Q := Q) phi (p * q)
  let toFun : FordLPointKPoint.KPointWithCongruence
      (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi →
      LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi :=
    fun a => by
      refine ⟨E a.1, ?_⟩
      intro i
      apply source_class_eq_of_modEq
      calc
        ((E a.1).1.1.2 i).1.val % (p ^ r) = (a.1.z i).val % (p ^ r) := by rfl
        _ = (a.1.w i).val % (p ^ r) := by
          change (a.1.z i).val % (p ^ r) = (a.1.w i).val % (p ^ r)
          exact a.2 i
        _ = ((E a.1).1.2.2 i).1.val % (p ^ r) := by rfl
  let invFun : LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
      (p := p) (q := q) (r := r) phi →
      FordLPointKPoint.KPointWithCongruence
        (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi :=
    fun a => by
      let K := E.symm a.1
      refine ⟨K, ?_⟩
      intro i
      apply modEq_of_source_class_eq
      apply Fin.ext
      change (a.1.1.1.2 i).1.val % (p ^ r) =
        (a.1.1.2.2 i).1.val % (p ^ r)
      exact congrArg Fin.val (a.2 i)
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro a
    apply Subtype.ext
    exact E.left_inv a.1
  · intro a
    apply Subtype.ext
    exact E.right_inv a.1

def lPointClassEnergyEquiv
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    LPoint s k P Q p q r phi ≃
      LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
        (p := p) (q := q) (r := r) phi :=
  (FordLPointKPoint.lPointKPointEquiv phi).trans
    (kPointClassEnergyEquiv phi)

lemma lPointClassEnergyEquiv_z
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : LPoint s k P Q p q r phi) (i : Fin k) :
    ((lPointClassEnergyEquiv phi a).1.1.1.2 i).1 = a.z i := by
  rfl

lemma lPointClassEnergyEquiv_w
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ)
    (a : LPoint s k P Q p q r phi) (i : Fin k) :
    ((lPointClassEnergyEquiv phi a).1.1.2.2 i).1 = a.w i := by
  rfl

theorem lPoint_card_eq_classEnergy
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype.card (LPoint s k P Q p q r phi) =
      Fintype.card
        (LClassEnergyZero (s := s) (k := k) (P := P) (Q := Q)
          (p := p) (q := q) (r := r) phi) :=
  Fintype.card_congr (lPointClassEnergyEquiv phi)

end FordLPointClassEnergy

#print axioms FordLPointClassEnergy.kPointClassEnergyEquiv
#print axioms FordLPointClassEnergy.lPointClassEnergyEquiv
#print axioms FordLPointClassEnergy.lPoint_card_eq_classEnergy
