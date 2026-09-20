import MRTProposition61TypeIILemma210InstantiationV3
import MRTProposition61TypeD1Factorization
import MRTCorollary25TypeD1IntegratedWeld

/-!
# Literal Type-II full-polynomial weld

This file identifies the untruncated two-factor polynomial produced by
Corollary 2.5 with the two dyadic norm fields to which Lemma 2.10 is applied.
The sharp source cutoff is deliberately absent here: it is removed by the
certified Perron transfer before this theorem is used.
-/

namespace MRTProposition61TypeIIFullNormWeldV3

open scoped BigOperators
open MeasureTheory
open MixedMeanFrontend MontgomeryVaughanFiniteReduction
open MAPMRTLemma210OrthogonalityReduction
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTProposition61TypeD1Factorization
open MAPHBPerronSourceData
open MRTProposition61TypeIIFirstInequalityV3
open MRTProposition61TypeIILemma210InstantiationV3

noncomputable section

/-- The finite polynomial used in the Lemma-2.10 interface is exactly the
source dyadic factor polynomial on the critical line. -/
theorem typeIIDyadicPolynomial_eq_halfLine
    {q N : ℕ} (hN : 1 ≤ N) {f : ℕ → ℂ}
    (hf : SupportedNatDyadic N f)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    typeIIDyadicPolynomial q N f chi t =
      halfLineDirichletPolynomial (N : ℝ) 2
        (characterTwist (fun n ↦ chi n) f) t := by
  rw [halfLineDirichletPolynomial_eq_longFactor hN hf]
  unfold typeIIDyadicPolynomial twistedFinitePolynomial criticalDyadicCoefficient
    longFactor dirichletPoly MixedMeanMajorantWeld.invSqrtCoeff
    MontgomeryVaughanFiniteReduction.dyadicSupport
  apply Finset.sum_congr rfl
  intro n hn
  unfold characterTwist twistedPhase mellinPhase
  congr 1
  · ring
  · congr 1
    push_cast
    ring

/-- Norm form of `typeIIDyadicPolynomial_eq_halfLine`. -/
theorem typeIIDyadicNormField_eq_halfLine
    {q N : ℕ} (hN : 1 ≤ N) {f : ℕ → ℂ}
    (hf : SupportedNatDyadic N f)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    typeIIDyadicNormField q N f chi t =
      ‖halfLineDirichletPolynomial (N : ℝ) 2
        (characterTwist (fun n ↦ chi n) f) t‖ := by
  unfold typeIIDyadicNormField
  rw [typeIIDyadicPolynomial_eq_halfLine hN hf]

/-- The full convolution norm after Perron removal is the product of the
exact two Lemma-2.10 norm fields. -/
theorem typeD1FullNorm_eq_typeIINormFields
    {q N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    typeD1FullNorm (N : ℝ) (M : ℝ)
        (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
        alpha beta chi t =
      typeIIDyadicNormField q N alpha chi t *
        typeIIDyadicNormField q M beta chi t := by
  unfold typeD1FullNorm
  rw [norm_halfLineDirichletPolynomial_convolution_eq_mul
    (by exact_mod_cast hN) (by exact_mod_cast hM)
    (fun m n ↦ by simp)
    (supportedDyadic_coe_of_supportedNatDyadic halpha)
    (supportedDyadic_coe_of_supportedNatDyadic hbeta)]
  rw [typeIIDyadicNormField_eq_halfLine hN halpha,
    typeIIDyadicNormField_eq_halfLine hM hbeta]

/-- The moving character mass of the full convolution is literally the
`factoredTypeIIMass` consumed by the deterministic Type-II Cauchy step. -/
theorem characterMovingMass_typeD1FullNorm_eq_factoredTypeIIMass
    {q N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (U t : ℝ) :
    characterMovingMass
        (typeD1FullNorm (N : ℝ) (M : ℝ)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta) U t =
      factoredTypeIIMass
        (typeIIDyadicNormField q N alpha)
        (typeIIDyadicNormField q M beta) U t := by
  unfold characterMovingMass factoredTypeIIMass
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro s hs
  exact typeD1FullNorm_eq_typeIINormFields
    hN hM halpha hbeta chi s

/-- Premise-free Lemma-2.10 bound for the exact untruncated convolution mass
appearing on the main side of certified Perron removal. -/
theorem typeD1FullNorm_outerMass_le_lemma210
    {q N M : ℕ} [NeZero q]
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (alpha beta : ℕ → ℂ)
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    {a b U : ℝ} (hab : a ≤ b) (hU : 0 ≤ U) :
    (∫ t in a..b,
      (characterMovingMass
        (typeD1FullNorm (N : ℝ) (M : ℝ)
          (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
          alpha beta) U t) ^ 2) ≤
      2 * U *
        (((q : ℝ) * (2 * U) + 8 * Real.pi * (N : ℝ)) *
          coefficientEnergy (criticalDyadicCoefficient alpha) N) *
        (((q : ℝ) * (b - a + 2 * U) + 8 * Real.pi * (M : ℝ)) *
          coefficientEnergy (criticalDyadicCoefficient beta) M) := by
  simp_rw [characterMovingMass_typeD1FullNorm_eq_factoredTypeIIMass
    hN hM halpha hbeta]
  exact typeII_outerMass_le_lemma210 hN hM alpha beta hab hU

end
end MRTProposition61TypeIIFullNormWeldV3

#print axioms MRTProposition61TypeIIFullNormWeldV3.typeIIDyadicPolynomial_eq_halfLine
#print axioms MRTProposition61TypeIIFullNormWeldV3.typeD1FullNorm_outerMass_le_lemma210
