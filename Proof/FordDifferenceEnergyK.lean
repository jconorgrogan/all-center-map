import FordDifferencePointBlockNorm
import FordKPointEnergy

open scoped BigOperators ZMod
noncomputable section
namespace MAPFordDifferenceEnergyK

open MAPFordDifferenceFamily MAPFordDifferencePointBlockNorm
open MAPFordP16FiniteFourierBridge MAPFordP16SourceCountBridge
open MAPFordLemma32LiteralContract
open FordBoundaryCountGeometry FordKPointEnergy

lemma sourceFreq_difference_eq_translated_sub_centering
    {k P : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (z : FordKPointEnergy.SourcePoint (P := P)) :
    FordKPointEnergy.sourceFreq (differencePsi psi h) z =
      fun j => pointTranslatedDifferenceFrequency psi h z j -
        pointCenteringFrequency psi h j := by
  simpa [FordKPointEnergy.sourceFreq, pointSourceFrequency] using
    (centeredDifferencePointFrequency_eq_translated_sub_centering psi h z)

def translated_energy_property_of_difference
    {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (r : EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq (differencePsi psi h) z) k) :
    EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        pointTranslatedDifferenceFrequency psi h z) k := by
  refine ⟨r.1, ?_⟩
  funext j
  have hr := congrFun r.2 j
  simp only [Pi.add_apply, Finset.sum_apply] at hr
  change FordKPointEnergy.baseFreq (q := q) r.val.1.1 j +
      ∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h)
        (r.val.1.2 i) j =
    FordKPointEnergy.baseFreq (q := q) r.val.2.1 j +
      ∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h)
        (r.val.2.2 i) j at hr
  simp only [Pi.add_apply, Finset.sum_apply]
  change FordKPointEnergy.baseFreq (q := q) r.val.1.1 j +
      ∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (r.val.1.2 i) j =
    FordKPointEnergy.baseFreq (q := q) r.val.2.1 j +
      ∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (r.val.2.2 i) j
  have hsum : ∀ v : Fin k → FordKPointEnergy.SourcePoint (P := P),
      (∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h) (v i) j) =
        (∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (v i) j) -
          (k : ℤ) * pointCenteringFrequency psi h j := by
    intro v
    simp_rw [sourceFreq_difference_eq_translated_sub_centering psi h]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hsum r.val.1.2, hsum r.val.2.2] at hr
  linarith

def difference_energy_property_of_translated
    {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (r : EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        pointTranslatedDifferenceFrequency psi h z) k) :
    EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq (differencePsi psi h) z) k := by
  refine ⟨r.1, ?_⟩
  funext j
  have hr := congrFun r.2 j
  simp only [Pi.add_apply, Finset.sum_apply] at hr
  change FordKPointEnergy.baseFreq (q := q) r.val.1.1 j +
      ∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (r.val.1.2 i) j =
    FordKPointEnergy.baseFreq (q := q) r.val.2.1 j +
      ∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (r.val.2.2 i) j at hr
  simp only [Pi.add_apply, Finset.sum_apply]
  change FordKPointEnergy.baseFreq (q := q) r.val.1.1 j +
      ∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h)
        (r.val.1.2 i) j =
    FordKPointEnergy.baseFreq (q := q) r.val.2.1 j +
      ∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h)
        (r.val.2.2 i) j
  have hsum : ∀ v : Fin k → FordKPointEnergy.SourcePoint (P := P),
      (∑ i : Fin k, FordKPointEnergy.sourceFreq (differencePsi psi h) (v i) j) =
        (∑ i : Fin k, pointTranslatedDifferenceFrequency psi h (v i) j) -
          (k : ℤ) * pointCenteringFrequency psi h j := by
    intro v
    simp_rw [sourceFreq_difference_eq_translated_sub_centering psi h]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hsum r.val.1.2, hsum r.val.2.2]
  linarith

def differenceEnergyEquiv
    {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ) :
    EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq (differencePsi psi h) z) k ≃
    EnergyZero
      (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
        FordKPointEnergy.baseFreq (q := q) x)
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        pointTranslatedDifferenceFrequency psi h z) k :=
  { toFun := translated_energy_property_of_difference psi h
    invFun := difference_energy_property_of_translated psi h
    left_inv := by intro r; apply Subtype.ext; rfl
    right_inv := by intro r; apply Subtype.ext; rfl }

theorem kpoint_card_eq_translated_difference_energy
    {s k P Q q : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ) :
    Fintype.card (KPoint s k P Q (differencePsi psi h) q) =
      Fintype.card (EnergyZero
        (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
          FordKPointEnergy.baseFreq (q := q) x)
        (fun z : FordKPointEnergy.SourcePoint (P := P) =>
          pointTranslatedDifferenceFrequency psi h z) k) := by
  calc
    Fintype.card (KPoint s k P Q (differencePsi psi h) q) =
        Fintype.card (EnergyZero
          (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
            FordKPointEnergy.baseFreq (q := q) x)
          (fun z : FordKPointEnergy.SourcePoint (P := P) =>
            FordKPointEnergy.sourceFreq (differencePsi psi h) z) k) :=
      FordKPointEnergy.kpoint_card_eq_energy (differencePsi psi h) q
    _ = Fintype.card (EnergyZero
        (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
          FordKPointEnergy.baseFreq (q := q) x)
        (fun z : FordKPointEnergy.SourcePoint (P := P) =>
          pointTranslatedDifferenceFrequency psi h z) k) :=
      Fintype.card_congr (differenceEnergyEquiv psi h)

end MAPFordDifferenceEnergyK

#print axioms MAPFordDifferenceEnergyK.kpoint_card_eq_translated_difference_energy
