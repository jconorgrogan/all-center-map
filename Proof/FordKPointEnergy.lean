import FordMaskedKToRaw
import FordBoundaryCountGeometry
import FordFamilyDoubling

open scoped BigOperators
open MAPFordLemma32LiteralContract MAPFordP16SourceCountBridge
open MAPFordP16FiniteFourierBridge
open FordBoundaryCountGeometry
open Polynomial

noncomputable section
namespace FordKPointEnergy

abbrev PowerWord {s Q : ℕ} := fordFiniteRawTuple (s := s) (Q := Q)
abbrev SourcePoint {P : ℕ} := fordFinitePositiveX (Q := P)

def baseFreq {s k Q q : ℕ} (x : PowerWord (s := s) (Q := Q)) : Fin k → ℤ :=
  fordQFrequencyAt (q := q) (fun i => (x i).1)

def sourceFreq {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (z : SourcePoint (P := P)) : Fin k → ℤ :=
  fun j => (psi j).eval (z.1.val : ℤ)

private lemma kpoint_to_energy
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ)
    (a : KPoint s k P Q psi q) :
    (let x : PowerWord (s := s) (Q := Q) := fun i => ⟨a.x i, a.x_pos i⟩
     let y : PowerWord (s := s) (Q := Q) := fun i => ⟨a.y i, a.y_pos i⟩
     let z : Fin k → SourcePoint (P := P) := fun i => ⟨a.z i, a.z_pos i⟩
     let w : Fin k → SourcePoint (P := P) := fun i => ⟨a.w i, a.w_pos i⟩
     ∀ j : Fin k, baseFreq (q := q) x j + ∑ i, sourceFreq psi (z i) j =
       baseFreq (q := q) y j + ∑ i, sourceFreq psi (w i) j) := by
  dsimp
  intro j
  simp only [baseFreq, sourceFreq, fordQFrequencyAt, fordQScalarFrequency,
    fordSourceFrequencyAt]
  rw [← Finset.mul_sum]
  have h := a.equation j
  change (∑ i : Fin k, ((psi j).eval ((a.z i).val : ℤ) -
      (psi j).eval ((a.w i).val : ℤ))) +
      (q : ℤ) ^ (j.val + 1) *
        (∑ i : Fin s, (((a.x i).val : ℤ) ^ (j.val + 1) -
          ((a.y i).val : ℤ) ^ (j.val + 1))) = 0 at h
  simp only [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum] at h ⊢
  linarith

def kPointEnergyEquiv
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    KPoint s k P Q psi q ≃
      EnergyZero
        (fun x : PowerWord (s := s) (Q := Q) => baseFreq (q := q) x)
        (fun z : SourcePoint (P := P) => sourceFreq psi z) k := by
  let toFun : KPoint s k P Q psi q →
      EnergyZero
        (fun x : PowerWord (s := s) (Q := Q) => baseFreq (q := q) x)
        (fun z : SourcePoint (P := P) => sourceFreq psi z) k := fun a => by
    let x : PowerWord (s := s) (Q := Q) := fun i => ⟨a.x i, a.x_pos i⟩
    let y : PowerWord (s := s) (Q := Q) := fun i => ⟨a.y i, a.y_pos i⟩
    let z : Fin k → SourcePoint (P := P) := fun i => ⟨a.z i, a.z_pos i⟩
    let w : Fin k → SourcePoint (P := P) := fun i => ⟨a.w i, a.w_pos i⟩
    refine ⟨((x, z), (y, w)), ?_⟩
    have h := kpoint_to_energy psi q a
    funext j
    simpa [x, y, z, w, baseFreq, sourceFreq] using h j
  let invFun : EnergyZero
      (fun x : PowerWord (s := s) (Q := Q) => baseFreq (q := q) x)
      (fun z : SourcePoint (P := P) => sourceFreq psi z) k →
      KPoint s k P Q psi q := fun r => by
    let state := r.val
    let x : PowerWord (s := s) (Q := Q) := state.1.1
    let z : Fin k → SourcePoint (P := P) := state.1.2
    let y : PowerWord (s := s) (Q := Q) := state.2.1
    let w : Fin k → SourcePoint (P := P) := state.2.2
    refine ⟨(fun i => (z i).1), (fun i => (w i).1),
      (fun i => (x i).1), (fun i => (y i).1),
      (fun i => (z i).2), (fun i => (w i).2),
      (fun i => (x i).2), (fun i => (y i).2), ?_⟩
    intro j
    have h := congrFun r.property j
    simp only [Pi.add_apply, Finset.sum_apply] at h
    change baseFreq (q := q) x j + ∑ i, sourceFreq psi (z i) j =
      baseFreq (q := q) y j + ∑ i, sourceFreq psi (w i) j at h
    simp only [baseFreq, sourceFreq, fordQFrequencyAt,
      fordQScalarFrequency, fordSourceFrequencyAt] at h
    rw [← Finset.mul_sum] at h
    change (∑ i : Fin k, ((psi j).eval ((z i).1.val : ℤ) -
        (psi j).eval ((w i).1.val : ℤ))) +
        (q : ℤ) ^ (j.val + 1) *
          (∑ i : Fin s, (((x i).1.val : ℤ) ^ (j.val + 1) -
            ((y i).1.val : ℤ) ^ (j.val + 1))) = 0
    simp only [Finset.sum_sub_distrib]
    simp only [mul_sub, Finset.mul_sum] at h ⊢
    linarith
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro a
    cases a
    rfl
  · intro r
    apply Subtype.ext
    cases r
    rfl

theorem kpoint_card_eq_energy
    {s k P Q : ℕ} (psi : Fin k → Polynomial ℤ) (q : ℕ) :
    Fintype.card (KPoint s k P Q psi q) =
    Fintype.card (EnergyZero
      (fun x : PowerWord (s := s) (Q := Q) => baseFreq (q := q) x)
      (fun z : SourcePoint (P := P) => sourceFreq psi z) k) :=
  Fintype.card_congr (kPointEnergyEquiv psi q)

lemma sourceFreq_doublePsi
    {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (z : SourcePoint (P := P)) (j : Fin k) :
    sourceFreq (MAPFordFamilyDoubling.doublePsi psi) z j =
      2 * sourceFreq psi z j := by
  simp [sourceFreq, MAPFordFamilyDoubling.doublePsi]

end FordKPointEnergy

#print axioms FordKPointEnergy.kPointEnergyEquiv
#print axioms FordKPointEnergy.kpoint_card_eq_energy
#print axioms FordKPointEnergy.sourceFreq_doublePsi
