import FordKPointEnergy
import FordMaxEnergyInput

open scoped BigOperators
open MAPFordLemma32LiteralContract
open FordBoundaryCountGeometry

noncomputable section
namespace FordGoodKEnergy

abbrev GoodK {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :=
  {a : KPoint s k P Q psi q // Function.Injective a.z ∧ Function.Injective a.w}

abbrev GoodEnergy {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) :=
  {r : EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq psi z) k //
    Function.Injective r.1.1.2 ∧ Function.Injective r.1.2.2}

instance goodKFintype
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    Fintype (GoodK (s := s) (k := k) (P := P) (Q := Q) psi q) := by
  classical
  unfold GoodK
  infer_instance

instance goodEnergyFintype
    {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) :
    Fintype (GoodEnergy (s := s) (k := k) (P := P) (Q := Q) (q := q) psi) := by
  classical
  unfold GoodEnergy
  infer_instance

lemma energy_source_coord
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ)
    (a : KPoint s k P Q psi q) (i : Fin k) :
    ((FordKPointEnergy.kPointEnergyEquiv psi q a).1.1.2 i).1 = a.z i := by
  rfl

lemma energy_source_coord_right
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ)
    (a : KPoint s k P Q psi q) (i : Fin k) :
    ((FordKPointEnergy.kPointEnergyEquiv psi q a).1.2.2 i).1 = a.w i := by
  rfl

lemma inv_source_coord
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ)
    (r : EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq psi z) k) (i : Fin k) :
    ((FordKPointEnergy.kPointEnergyEquiv psi q).symm r).z i =
      (r.1.1.2 i).1 := by
  rfl

lemma inv_source_coord_right
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ)
    (r : EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq psi z) k) (i : Fin k) :
    ((FordKPointEnergy.kPointEnergyEquiv psi q).symm r).w i =
      (r.1.2.2 i).1 := by
  rfl

def goodKEnergyEquiv
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    GoodK (s := s) (k := k) (P := P) (Q := Q) psi q ≃ GoodEnergy (s := s) (k := k) (P := P) (Q := Q) (q := q) psi := by
  let toFun : GoodK (s := s) (k := k) (P := P) (Q := Q) psi q → GoodEnergy (s := s) (k := k) (P := P) (Q := Q) (q := q) psi :=
    fun a => by
      refine ⟨FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q a.1, ?_⟩
      constructor
      · intro i j h
        apply a.2.1
        calc
          a.1.z i = ((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q a.1).1.1.2 i).1 :=
            (energy_source_coord psi q a.1 i).symm
          _ = ((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q a.1).1.1.2 j).1 :=
            congrArg Subtype.val h
          _ = a.1.z j := energy_source_coord psi q a.1 j
      · intro i j h
        apply a.2.2
        calc
          a.1.w i = ((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q a.1).1.2.2 i).1 :=
            (energy_source_coord_right psi q a.1 i).symm
          _ = ((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q a.1).1.2.2 j).1 :=
            congrArg Subtype.val h
          _ = a.1.w j := energy_source_coord_right psi q a.1 j
  let invFun : GoodEnergy (s := s) (k := k) (P := P) (Q := Q) (q := q) psi → GoodK (s := s) (k := k) (P := P) (Q := Q) psi q :=
    fun a => by
      refine ⟨(FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).symm a.1, ?_⟩
      constructor
      · intro i j h
        apply a.2.1
        apply Subtype.ext
        calc
          (((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).symm a.1).z i) =
              (a.1.1.1.2 i).1 := inv_source_coord psi q a.1 i
          _ = (a.1.1.1.2 j).1 := h
          _ = (((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).symm a.1).z j) :=
            (inv_source_coord psi q a.1 j).symm
      · intro i j h
        apply a.2.2
        apply Subtype.ext
        calc
          (((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).symm a.1).w i) =
              (a.1.1.2.2 i).1 := inv_source_coord_right psi q a.1 i
          _ = (a.1.1.2.2 j).1 := h
          _ = (((FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).symm a.1).w j) :=
            (inv_source_coord_right psi q a.1 j).symm
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro a
    apply Subtype.ext
    exact (FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).left_inv a.1
  · intro a
    apply Subtype.ext
    exact (FordKPointEnergy.kPointEnergyEquiv (s := s) (k := k) (P := P) (Q := Q) psi q).right_inv a.1

theorem goodK_card_eq_goodEnergy
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    Fintype.card (GoodK (s := s) (k := k) (P := P) (Q := Q) psi q) =
      Fintype.card (GoodEnergy (s := s) (k := k) (P := P) (Q := Q) (q := q) psi) :=
  Fintype.card_congr (goodKEnergyEquiv psi q)

end FordGoodKEnergy

#print axioms FordGoodKEnergy.goodKEnergyEquiv
#print axioms FordGoodKEnergy.goodK_card_eq_goodEnergy
