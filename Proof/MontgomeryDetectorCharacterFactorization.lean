import MontgomeryHybridCharacterSampling
import AppendixA4PostA5SetAdapter

/-!
# Character factorization of the Montgomery detector shell

The finite detector produced after the contour shift has one character twist
and an otherwise common coefficient sequence.  This is the exact algebraic
connector needed before applying a fixed-modulus hybrid character mean-value
theorem.  In particular, the dependence on `chi` is not hidden in an opaque
coefficient.
-/

namespace MAPMontgomeryDetectorCharacterFactorization

open scoped BigOperators
open CGLProofDAG MontgomeryVaughanFiniteReduction
open MAPAppendixA4GammaEndpoint MAPAppendixA4PostA5SetAdapter
open MAPMollifierCoefficientIdentity MAPMRTLemma210DyadicMeanSquare

noncomputable section

/-- The detector coefficient after fixing the real part, with the character
twist removed. -/
def untwistedDetectorCommonCoefficient
    (U N : ℕ) (Y sigma : ℝ) (n : ℕ) : ℂ :=
  (Real.rpow n (-sigma) : ℂ) *
    if n ∈ Finset.Ico (U + 1) (N + 1) then
      (Real.exp (-((n : ℝ) / Y)) : ℂ) * mollifierCoeff U n
    else 0

/-- Exact pointwise factorization: every dependence on the character is the
single standard twist `chi n`. -/
theorem detectorCommonCoefficient_eq_untwisted_mul_character
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U N : ℕ) (Y sigma : ℝ) (n : ℕ) :
    detectorCommonCoefficient chi U N Y sigma n =
      untwistedDetectorCommonCoefficient U N Y sigma n * chi n := by
  classical
  unfold detectorCommonCoefficient detectorFourierBaseCoefficient
    detectorCoeff untwistedDetectorCommonCoefficient
  by_cases hn : n ∈ Finset.Ico (U + 1) (N + 1)
  · simp only [hn, if_pos, Pi.mul_apply]
    ring
  · simp [hn]

/-- Hence the fixed-real-part detector polynomial is literally the character
packet accepted by the certified hybrid sampling theorem. -/
theorem dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (U N : ℕ) (Y sigma : ℝ) (D : ℕ) (t : ℝ) :
    dirichletPolynomial (detectorCommonCoefficient chi U N Y sigma) D t =
      characterPacketPolynomial q (dyadicSupport D)
        (untwistedDetectorCommonCoefficient U N Y sigma) chi t := by
  rw [dirichletPolynomial_eq]
  unfold characterPacketPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  rw [detectorCommonCoefficient_eq_untwisted_mul_character]

/-- The sharp variable-character sampling estimate now applies directly to
the detector coefficients, with one common energy and no extra factor of the
modulus on the length term. -/
theorem sum_character_detectorPolynomial_sample_norm_sq_le
    {q D U N : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T : ℝ} (hT : 0 ≤ T)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, 0 ≤ t ∧ t ≤ T) :
    (∑ chi : DirichletCharacter ℂ q,
        ∑ t ∈ W chi,
          ‖dirichletPolynomial
            (detectorCommonCoefficient chi U N Y sigma) D t‖ ^ 2) ≤
      3 * ((q : ℝ) * (T + 1) + 8 * Real.pi * (D : ℝ)) *
        coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D := by
  simpa only [
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
    MAPMontgomeryHybridCharacterSampling.sum_character_sample_norm_sq_le
      hD (untwistedDetectorCommonCoefficient U N Y sigma) hT W hsep hheight

/-- Large-value form of the same exact connector. -/
theorem sum_character_detector_card_le_of_large_values
    {q D U N : ℕ} [NeZero q] (hD : 1 ≤ D)
    (Y sigma : ℝ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (W : DirichletCharacter ℂ q → Finset ℝ)
    (hsep : ∀ chi, OneSeparated (W chi))
    (hheight : ∀ chi, ∀ t ∈ W chi, 0 ≤ t ∧ t ≤ T)
    (hlarge : ∀ chi, ∀ t ∈ W chi,
      V ≤ ‖dirichletPolynomial
        (detectorCommonCoefficient chi U N Y sigma) D t‖) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 2 ≤
      3 * ((q : ℝ) * (T + 1) + 8 * Real.pi * (D : ℝ)) *
        coefficientEnergy
          (untwistedDetectorCommonCoefficient U N Y sigma) D := by
  apply MAPMontgomeryHybridCharacterSampling.sum_character_card_le_of_large_values
    hD (untwistedDetectorCommonCoefficient U N Y sigma) hT hV W hsep hheight
  intro chi t ht
  simpa only [
      dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket] using
    hlarge chi t ht

end
end MAPMontgomeryDetectorCharacterFactorization

#print axioms MAPMontgomeryDetectorCharacterFactorization.detectorCommonCoefficient_eq_untwisted_mul_character
#print axioms MAPMontgomeryDetectorCharacterFactorization.dirichletPolynomial_detectorCommonCoefficient_eq_characterPacket
#print axioms MAPMontgomeryDetectorCharacterFactorization.sum_character_detectorPolynomial_sample_norm_sq_le
#print axioms MAPMontgomeryDetectorCharacterFactorization.sum_character_detector_card_le_of_large_values
