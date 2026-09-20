import FordDifferenceFamily
import FordP16FiniteFourierBridge
import FordP16SourceCountBridge

open scoped BigOperators ZMod ComplexConjugate
noncomputable section
namespace MAPFordDifferencePointBlockNorm

open MAPFordDifferenceFamily MAPFordP16FiniteFourierBridge
open MAPFordP16SourceCountBridge

abbrev positivePoint (P : ℕ) := fordFinitePositiveX (Q := P)

def pointSourceFrequency {k P : ℕ} (psi : Fin k → Polynomial ℤ)
    (z : positivePoint P) : Fin k → ℤ :=
  fun j => (psi j).eval (z.1.val : ℤ)

def pointTranslatedDifferenceFrequency {k P : ℕ}
    (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (z : positivePoint P) : Fin k → ℤ :=
  fun j => (psi j).eval ((z.1.val : ℤ) + h) -
    (psi j).eval (z.1.val : ℤ)

def pointCenteringFrequency {k : ℕ} (psi : Fin k → Polynomial ℤ)
    (h : ℤ) : Fin k → ℤ :=
  fun j => (psi j).eval h - (psi j).eval 0

def fordPointFourierBlock {A : Type*} [Fintype A]
    {L k : ℕ} [NeZero L] (alpha : Fin k → ZMod L)
    (freq : A → Fin k → ℤ) : ℂ :=
  ∑ a : A, fordIntegerCharTerm alpha (freq a)

def centeredDifferencePointBlock {L k : ℕ} [NeZero L]
    (P : ℕ) (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (alpha : Fin k → ZMod L) : ℂ :=
  fordPointFourierBlock alpha
    (fun z : positivePoint P => pointSourceFrequency (differencePsi psi h) z)

def translatedDifferencePointBlock {L k : ℕ} [NeZero L]
    (P : ℕ) (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (alpha : Fin k → ZMod L) : ℂ :=
  fordPointFourierBlock alpha
    (fun z : positivePoint P => pointTranslatedDifferenceFrequency psi h z)

lemma centeredDifferencePointFrequency_eq_translated_sub_centering
    {k P : ℕ} (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (z : positivePoint P) :
    pointSourceFrequency (differencePsi psi h) z =
      fun j => pointTranslatedDifferenceFrequency psi h z j -
        pointCenteringFrequency psi h j := by
  funext j
  simpa [pointSourceFrequency, pointTranslatedDifferenceFrequency,
    pointCenteringFrequency, differencePsi] using
    (MAPFordDifferenceFamily.centered_difference_eval_sub
      (psi j) h (z.1.val : ℤ))

lemma centeredDifferencePointBlock_eq_translated_mul_phase
    {L k P : ℕ} [NeZero L]
    (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (alpha : Fin k → ZMod L) :
    centeredDifferencePointBlock P psi h alpha =
      translatedDifferencePointBlock P psi h alpha *
        fordIntegerCharTerm alpha (fun j => -pointCenteringFrequency psi h j) := by
  unfold centeredDifferencePointBlock translatedDifferencePointBlock
  rw [show (fun z : positivePoint P =>
      pointSourceFrequency (differencePsi psi h) z) =
      (fun z : positivePoint P =>
        fun j => pointTranslatedDifferenceFrequency psi h z j -
          pointCenteringFrequency psi h j) by
    funext z
    exact centeredDifferencePointFrequency_eq_translated_sub_centering psi h z]
  simp only [fordPointFourierBlock]
  calc
    (∑ z : positivePoint P,
        fordIntegerCharTerm alpha
          (fun j => pointTranslatedDifferenceFrequency psi h z j -
            pointCenteringFrequency psi h j)) =
      ∑ z : positivePoint P,
        fordIntegerCharTerm alpha (pointTranslatedDifferenceFrequency psi h z) *
          fordIntegerCharTerm alpha (fun j => -pointCenteringFrequency psi h j) := by
      apply Finset.sum_congr rfl
      intro z hz
      have hfreq : (fun j => pointTranslatedDifferenceFrequency psi h z j -
          pointCenteringFrequency psi h j) =
          (fun j => pointTranslatedDifferenceFrequency psi h z j +
            (-pointCenteringFrequency psi h j)) := by
        funext j
        ring
      rw [hfreq, ← char_term_add]
    _ = (∑ z : positivePoint P,
        fordIntegerCharTerm alpha (pointTranslatedDifferenceFrequency psi h z)) *
          fordIntegerCharTerm alpha (fun j => -pointCenteringFrequency psi h j) := by
      rw [Finset.sum_mul]

theorem norm_centeredDifferencePointBlock_eq_norm_translatedDifferencePointBlock
    {L k P : ℕ} [NeZero L]
    (psi : Fin k → Polynomial ℤ) (h : ℤ)
    (alpha : Fin k → ZMod L) :
    ‖centeredDifferencePointBlock P psi h alpha‖ =
      ‖translatedDifferencePointBlock P psi h alpha‖ := by
  rw [centeredDifferencePointBlock_eq_translated_mul_phase, norm_mul]
  have hphase : ‖fordIntegerCharTerm alpha
      (fun j => -pointCenteringFrequency psi h j)‖ = 1 := by
    simp [fordIntegerCharTerm]
  rw [hphase, mul_one]

theorem norm_fordPointFourierBlock_neg
    {A : Type*} [Fintype A] {L k : ℕ} [NeZero L]
    (alpha : Fin k → ZMod L) (freq : A → Fin k → ℤ) :
    ‖fordPointFourierBlock alpha (fun a j => -freq a j)‖ =
      ‖fordPointFourierBlock alpha freq‖ := by
  have hstar : star (fordPointFourierBlock alpha freq) =
      fordPointFourierBlock alpha (fun a j => -freq a j) := by
    unfold fordPointFourierBlock
    rw [star_sum]
    apply Finset.sum_congr rfl
    intro a ha
    exact char_term_neg alpha (freq a)
  calc
    ‖fordPointFourierBlock alpha (fun a j => -freq a j)‖ =
        ‖star (fordPointFourierBlock alpha freq)‖ := by rw [hstar]
    _ = ‖fordPointFourierBlock alpha freq‖ := by simp

end MAPFordDifferencePointBlockNorm

#print axioms MAPFordDifferencePointBlockNorm.norm_centeredDifferencePointBlock_eq_norm_translatedDifferencePointBlock
#print axioms MAPFordDifferencePointBlockNorm.norm_fordPointFourierBlock_neg
