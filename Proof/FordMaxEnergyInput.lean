import FordKPointEnergy
import FordFamilyMaxDouble
import FordCollisionThreeMoments

open scoped BigOperators
open MAPFordType MAPFordP16Source35Triangular MAPFordLemma32LiteralContract
open MAPFordFamilyDoubling FordCollisionThreeMoments
open FordBoundaryCountGeometry

noncomputable section
namespace FordMaxEnergyInput

def sourcePointEquiv (P : ℕ) :
    Fin P ≃ FordKPointEnergy.SourcePoint (P := P) :=
  { toFun := fun n => by
      have hn := n.isLt
      refine ⟨⟨n.val + 1, Nat.succ_lt_succ n.isLt⟩,
        Nat.succ_le_succ (Nat.zero_le n.val)⟩
    invFun := fun x => by
      have hx := x.2
      refine ⟨x.1.val - 1, by omega⟩
    left_inv := by
      intro n
      apply Fin.ext
      simp
    right_inv := by
      intro x
      have hx := x.2
      apply Subtype.ext
      apply Fin.ext
      simp
      omega }

theorem sourcePoint_card (P : ℕ) :
    Fintype.card (FordKPointEnergy.SourcePoint (P := P)) = P := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (sourcePointEquiv P)).symm

theorem exists_max_energy_input
    {s k d P Q q : ℕ} {T : ℤ}
    (m0 : ℕ) (psi0 : Fin k → Polynomial ℤ)
    (h0 : FordType k d T m0 (psiNatSucc psi0)) :
    ∃ (m : ℕ) (psi : Fin k → Polynomial ℤ),
      FordType k d T m (psiNatSucc psi) ∧
      FordType k d T (m + 1) (psiNatSucc (doublePsi psi)) ∧
      Fintype.card (KPoint s k P Q (doublePsi psi) q) ≤
        Fintype.card (KPoint s k P Q psi q) ∧
      Fintype.card
          (EnergyZero
            (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
              FordKPointEnergy.baseFreq (q := q) x)
            (FordCollisionThreeMoments.doubled
              (fun z : FordKPointEnergy.SourcePoint (P := P) =>
                FordKPointEnergy.sourceFreq psi z)) k) ≤
        Fintype.card
          (EnergyZero
            (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
              FordKPointEnergy.baseFreq (q := q) x)
            (fun z : FordKPointEnergy.SourcePoint (P := P) =>
              FordKPointEnergy.sourceFreq psi z) k) ∧
      ∀ (m' : ℕ) (psi' : Fin k → Polynomial ℤ),
        FordType k d T m' (psiNatSucc psi') →
          Fintype.card (KPoint s k P Q psi' q) ≤
            Fintype.card (KPoint s k P Q psi q) := by
  obtain ⟨m, psi, hpsi, hdouble, hKdouble, hKmax⟩ :=
    FordFamilyMaxDouble.exists_maximal_doubling_member
      (s := s) (k := k) (d := d) (P := P) (Q := Q) (q := q)
      (T := T) m0 psi0 h0
  have hg :
      (fun z : FordKPointEnergy.SourcePoint (P := P) =>
        FordKPointEnergy.sourceFreq (MAPFordFamilyDoubling.doublePsi psi) z) =
      FordCollisionThreeMoments.doubled
        (fun z : FordKPointEnergy.SourcePoint (P := P) =>
          FordKPointEnergy.sourceFreq psi z) := by
    funext z j
    exact FordKPointEnergy.sourceFreq_doublePsi psi z j
  have henergy :
      Fintype.card
          (EnergyZero
            (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
              FordKPointEnergy.baseFreq (q := q) x)
            (FordCollisionThreeMoments.doubled
              (fun z : FordKPointEnergy.SourcePoint (P := P) =>
                FordKPointEnergy.sourceFreq psi z)) k) ≤
        Fintype.card
          (EnergyZero
            (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
              FordKPointEnergy.baseFreq (q := q) x)
            (fun z : FordKPointEnergy.SourcePoint (P := P) =>
              FordKPointEnergy.sourceFreq psi z) k) := by
    rw [← hg]
    calc
      _ = Fintype.card (KPoint s k P Q (doublePsi psi) q) :=
        (FordKPointEnergy.kpoint_card_eq_energy (doublePsi psi) q).symm
      _ ≤ Fintype.card (KPoint s k P Q psi q) := hKdouble
      _ = _ := FordKPointEnergy.kpoint_card_eq_energy psi q
  exact ⟨m, psi, hpsi, hdouble, hKdouble, henergy, hKmax⟩

end FordMaxEnergyInput

#print axioms FordMaxEnergyInput.exists_max_energy_input
