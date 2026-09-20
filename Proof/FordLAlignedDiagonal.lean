import FordOffdiagTensor
import FordLPointClassEnergy
import FordClassEnergyDiagonal
import FordMaxEnergyInput

open scoped BigOperators
open MAPFordLemma32LiteralContract
open MAPFordP16SourceCountBridge
open FordBoundaryCountGeometry
open FordClassEnergyMoment
open FordClassEnergyDiagonal
open FordLPointClassEnergy
open FordKPointEnergy

namespace FordLAlignedDiagonal
noncomputable section
set_option maxHeartbeats 600000

abbrev LDiag (s k P Q p q r : ℕ) (phi : Fin k → Polynomial ℤ) :=
  {a : LPoint s k P Q p q r phi // ∃ i : Fin k, a.z i = a.w i}

instance lDiagFintype {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype (LDiag s k P Q p q r phi) := by
  classical
  unfold LDiag
  infer_instance

theorem lPoint_card_partition
    {s k P Q p q r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Fintype.card (LPoint s k P Q p q r phi) =
      Fintype.card (LDiag s k P Q p q r phi) +
        Fintype.card (FordOffdiagTensor.LOffdiag s k P Q p q r phi) := by
  classical
  have hcomp := Fintype.card_subtype_compl
    (α := LPoint s k P Q p q r phi)
    (p := fun a => ∃ i : Fin k, a.z i = a.w i)
  have hcomp' :
      Fintype.card (FordOffdiagTensor.LOffdiag s k P Q p q r phi) =
        Fintype.card (LPoint s k P Q p q r phi) -
          Fintype.card (LDiag s k P Q p q r phi) := by
    have hdiag :
        Fintype.card {a : LPoint s k P Q p q r phi //
          ∃ i : Fin k, a.z i = a.w i} =
          Fintype.card (LDiag s k P Q p q r phi) := by rfl
    let eoff :
        {a : LPoint s k P Q p q r phi //
          ¬ ∃ i : Fin k, a.z i = a.w i} ≃
          FordOffdiagTensor.LOffdiag s k P Q p q r phi :=
      { toFun := fun a => ⟨a.1, by
            intro i hi
            exact a.2 ⟨i, hi⟩⟩
        invFun := fun a => ⟨a.1, by
            intro h
            rcases h with ⟨i, hi⟩
            exact a.2 i hi⟩
        left_inv := by intro a; rfl
        right_inv := by intro a; rfl }
    have hoff := Fintype.card_congr eoff
    rw [hdiag, hoff] at hcomp
    exact hcomp
  have hcomp'' :
      Fintype.card (FordOffdiagTensor.LOffdiag s k P Q p q r phi) =
        Fintype.card (LPoint s k P Q p q r phi) -
          Fintype.card (LDiag s k P Q p q r phi) := by
    simpa [LDiag] using hcomp
  have hle := Fintype.card_subtype_le
    (fun a : LPoint s k P Q p q r phi => ∃ i : Fin k, a.z i = a.w i)
  symm
  rw [hcomp'']
  exact Nat.add_sub_of_le hle

/-- The aligned diagonal deletes the common source coordinate and lands in the
`n = k-1` class energy carrier. -/
theorem lDiag_card_le_classEnergy
    {s k P Q p q r : ℕ} (hk : 1 ≤ k)
    (phi : Fin k → Polynomial ℤ) :
    Fintype.card (LDiag s k P Q p q r phi) ≤
      k * P * Fintype.card
        (ClassEnergyZero
          (fun x : FordKPointEnergy.PowerWord (s := s) (Q := Q) =>
            FordKPointEnergy.baseFreq (q := p * q) x)
          (fun z : FordKPointEnergy.SourcePoint (P := P) =>
            FordKPointEnergy.sourceFreq phi z)
          (fun z : FordKPointEnergy.SourcePoint (P := P) =>
            FordLPointClassEnergy.positiveResidueClass (p := p) (r := r) z)
          (k - 1)) := by
  classical
  let f : FordKPointEnergy.PowerWord (s := s) (Q := Q) → Fin k → ℤ :=
    FordKPointEnergy.baseFreq (q := p * q)
  let g : FordKPointEnergy.SourcePoint (P := P) → Fin k → ℤ :=
    FordKPointEnergy.sourceFreq phi
  let cls : FordKPointEnergy.SourcePoint (P := P) → Fin (P + 1) :=
    FordLPointClassEnergy.positiveResidueClass (p := p) (r := r)
  let F := FordLPointClassEnergy.lPointClassEnergyEquiv
    (s := s) (k := k) (P := P) (Q := Q) (p := p) (q := q) (r := r) phi
  have hkadd : k - 1 + 1 = k := Nat.sub_add_cancel hk
  let AlignedK : Type :=
    {r : ClassEnergyZero f g cls k //
      ∃ i : Fin k, r.1.1.1.2 i = r.1.1.2.2 i}
  let toAligned : LDiag s k P Q p q r phi →
      AlignedK := by
    intro a
    refine ⟨F a.1, ?_⟩
    rcases a.2 with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply Subtype.ext
    have hz := FordLPointClassEnergy.lPointClassEnergyEquiv_z phi a.1 i
    have hw := FordLPointClassEnergy.lPointClassEnergyEquiv_w phi a.1 i
    exact hz.trans (hi.trans hw.symm)
  have hinj : Function.Injective toAligned := by
    intro a b hab
    apply Subtype.ext
    apply F.injective
    simpa [toAligned] using congrArg (fun z : AlignedK => z.1) hab
  have hcard := Fintype.card_le_of_injective toAligned hinj
  have hdiag := FordClassEnergyDiagonal.alignedDiag_card_le f g cls (n := k - 1)
  change Fintype.card {r : ClassEnergyZero f g cls (k - 1 + 1) //
      ∃ i : Fin (k - 1 + 1), r.1.1.1.2 i = r.1.1.2.2 i} ≤
    (k - 1 + 1) * Fintype.card (FordKPointEnergy.SourcePoint (P := P)) *
      Fintype.card (ClassEnergyZero f g cls (k - 1)) at hdiag
  rw [hkadd] at hdiag
  change Fintype.card AlignedK ≤ _ at hdiag
  calc
    Fintype.card (LDiag s k P Q p q r phi) ≤
        Fintype.card AlignedK := hcard
    _ ≤ k * Fintype.card (FordKPointEnergy.SourcePoint (P := P)) *
        Fintype.card (ClassEnergyZero f g cls (k - 1)) := hdiag
    _ = k * P * Fintype.card (ClassEnergyZero f g cls (k - 1)) := by
      rw [FordMaxEnergyInput.sourcePoint_card]

end
end FordLAlignedDiagonal

#print axioms FordLAlignedDiagonal.lPoint_card_partition
#print axioms FordLAlignedDiagonal.lDiag_card_le_classEnergy
