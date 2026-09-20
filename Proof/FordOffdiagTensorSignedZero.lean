import FordOffdiagTensorFibers
import FordSignedMixedCount
import FordDifferencePointBlockNorm
import FordPositiveHeightFamily
import FordKPointEnergy

open scoped BigOperators
open FordDifferencePairs MAPFordLemma32LiteralContract FordOffdiagTensor FordOffdiagTensorFibers
open FordSignedMixedCount
open MAPFordDifferencePointBlockNorm
open FordPositiveHeightFamily
noncomputable section
set_option autoImplicit false
namespace FordOffdiagTensorSignedZero

abbrev PowerWord (s Q : ℕ) := FordKPointEnergy.PowerWord (s := s) (Q := Q)
abbrev SourcePoint (P : ℕ) := FordKPointEnergy.SourcePoint (P := P)
abbrev Height (P p r : ℕ) := PositiveHeight P (Modulus p r)

abbrev baseFrequency {s k Q p q : ℕ} :
    PowerWord s Q → Fin k → ℤ :=
  FordKPointEnergy.baseFreq (q := p * q)

abbrev translatedFrequency {k P p r : ℕ} (phi : Fin k → Polynomial ℤ) :
    Height P p r → SourcePoint P → Fin k → ℤ :=
  fun h z => pointTranslatedDifferenceFrequency phi (shift h) z

def positiveFinToSource {P : ℕ} (x : PositiveFin P) : SourcePoint P :=
  ⟨x.1, by have hx := x.2; omega⟩

def sourceToPositiveFin {P : ℕ} (x : SourcePoint P) : PositiveFin P :=
  ⟨x.1, by have hx := x.2; omega⟩

lemma sourceToPositiveFin_toSource {P : ℕ} (x : SourcePoint P) :
    positiveFinToSource (sourceToPositiveFin x) = x := by
  apply Subtype.ext
  rfl

lemma positiveFinToSource_toPositiveFin {P : ℕ} (x : PositiveFin P) :
    sourceToPositiveFin (positiveFinToSource x) = x := by
  apply Subtype.ext
  rfl

def tensorFiberState {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    {hm : 0 < Modulus p r} {σ : Fin k → Bool}
    {η : Fin k → Height P p r}
    (x : TensorFiber s k P Q p q r phi hm σ η) :
    SignedState (PowerWord s Q) (SourcePoint P) k :=
  (((fun i => ⟨x.1.u i, by have hi := x.1.u_pos i; omega⟩),
    (fun i => ⟨x.1.v i, by have hi := x.1.v_pos i; omega⟩)),
    (fun i => positiveFinToSource (x.1.base i)))

lemma tensorFiberState_signedFrequency_zero
    {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    {hm : 0 < Modulus p r} {σ : Fin k → Bool}
    {η : Fin k → Height P p r}
    (x : TensorFiber s k P Q p q r phi hm σ η) :
    ∀ j, signedFrequency (baseFrequency (s := s) (k := k) (Q := Q) (p := p) (q := q))
      (translatedFrequency (k := k) (P := P) (p := p) (r := r) phi) η σ
      (tensorFiberState x) j = 0 := by
  intro j
  have heq := x.1.equation j
  simp only [signedFrequency, tensorFiberState, translatedFrequency, baseFrequency,
    FordKPointEnergy.baseFreq, MAPFordP16FiniteFourierBridge.fordQFrequencyAt,
    MAPFordP16FiniteFourierBridge.fordQScalarFrequency,
    MAPFordDifferencePointBlockNorm.pointTranslatedDifferenceFrequency,
    FordPositiveHeightFamily.shift, positiveFinToSource,
    Pi.add_apply, Finset.sum_apply] at *
  have hσ : ∀ i : Fin k, σ i = x.1.sign i := by
    intro i
    exact congrFun x.2.1 i |>.symm
  have hη : ∀ i : Fin k, (η i).1.val = (x.1.height i).1.val := by
    intro i
    exact congrFun x.2.2 i |>.symm ▸ rfl
  simp only [hσ, hη]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [← mul_sub]
  norm_num [Nat.cast_mul] at heq ⊢
  ring_nf at heq ⊢
  convert heq using 1 <;> ring

def tensorFiberToSignedZero {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) (σ : Fin k → Bool) (η : Fin k → Height P p r) :
    TensorFiber s k P Q p q r phi hm σ η ≃
      SignedZero (baseFrequency (s := s) (k := k) (Q := Q) (p := p) (q := q))
        (translatedFrequency (k := k) (P := P) (p := p) (r := r) phi) η σ := by
  let toFun : TensorFiber s k P Q p q r phi hm σ η →
      SignedZero (baseFrequency (s := s) (k := k) (Q := Q) (p := p) (q := q))
        (translatedFrequency (k := k) (P := P) (p := p) (r := r) phi) η σ := fun x =>
    ⟨tensorFiberState x, tensorFiberState_signedFrequency_zero x⟩
  let invFun : SignedZero (baseFrequency (s := s) (k := k) (Q := Q) (p := p) (q := q))
        (translatedFrequency (k := k) (P := P) (p := p) (r := r) phi) η σ →
      TensorFiber s k P Q p q r phi hm σ η := fun z => by
    let a : TensorPoint s k P Q p q r phi hm := {
      sign := σ
      height := η
      base := fun i => sourceToPositiveFin (z.1.2 i)
      u := fun i => (z.1.1.1 i).1
      v := fun i => (z.1.1.2 i).1
      u_pos := fun i => by have hi := (z.1.1.1 i).2; omega
      v_pos := fun i => by have hi := (z.1.1.2 i).2; omega
      equation := ?_ }
    · exact ⟨a, rfl, rfl⟩
    · intro j
      have hz := z.2 j
      simp only [signedFrequency, translatedFrequency, baseFrequency,
        FordKPointEnergy.baseFreq, MAPFordP16FiniteFourierBridge.fordQFrequencyAt,
        MAPFordP16FiniteFourierBridge.fordQScalarFrequency,
        MAPFordDifferencePointBlockNorm.pointTranslatedDifferenceFrequency,
        FordPositiveHeightFamily.shift, sourceToPositiveFin, Pi.add_apply,
        Finset.sum_apply] at hz ⊢
      rw [Finset.sum_sub_distrib, mul_sub, Finset.mul_sum, Finset.mul_sum]
      norm_num [Nat.cast_mul] at hz ⊢
      ring_nf at hz ⊢
      exact hz
  refine { toFun := toFun, invFun := invFun, left_inv := ?_, right_inv := ?_ }
  · intro x
    apply Subtype.ext
    simp [invFun, toFun, tensorFiberState, positiveFinToSource, sourceToPositiveFin]
    congr
    · exact x.2.1.symm
    · exact x.2.2.symm
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext <;> funext i <;> rfl
    · funext i
      rfl

theorem tensorFiber_card_eq_signedZero
    {s k P Q p q r : ℕ} {phi : Fin k → Polynomial ℤ}
    (hm : 0 < Modulus p r) (σ : Fin k → Bool) (η : Fin k → Height P p r) :
    Fintype.card (TensorFiber s k P Q p q r phi hm σ η) =
      Fintype.card (SignedZero
        (baseFrequency (s := s) (k := k) (Q := Q) (p := p) (q := q))
        (translatedFrequency (k := k) (P := P) (p := p) (r := r) phi) η σ) :=
  Fintype.card_congr (tensorFiberToSignedZero hm σ η)

end FordOffdiagTensorSignedZero

#print axioms FordOffdiagTensorSignedZero.tensorFiberToSignedZero
#print axioms FordOffdiagTensorSignedZero.tensorFiber_card_eq_signedZero
