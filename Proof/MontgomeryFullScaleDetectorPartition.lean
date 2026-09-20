import MontgomeryFullScaleTypeIFamily
import MontgomeryMixedMomentTypeII
import MontgomeryLowStripContinuousSourceSplit
import PrincipalZetaDetectorDichotomy
namespace MAPMontgomeryFullScaleDetectorPartition
open scoped BigOperators
open Complex
open MAPAppendixA4DetectorDichotomy MAPAppendixA4PostA5SetAdapter
open MAPAppendixA4RecenteredGammaRepair MAPMontgomeryLowStripContinuousSourceSplit
noncomputable section

def arithmeticFamily {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
    (U N : ℕ) (Y V : ℝ) : DirichletCharacter ℂ q → Finset ℂ := by
  classical
  exact fun chi =>
  (W chi).filter (fun rho => V ≤ ‖arithmeticDetectorBlock chi U N rho Y‖)

def centralFamily {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
    (U : ℕ) (Y B V : ℝ) : DirichletCharacter ℂ q → Finset ℂ := by
  classical
  exact fun chi =>
  (W chi).filter (fun rho => V ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖)

theorem nonprincipal_fullScale_detector_family_cover
    {q : ℕ} [NeZero q] (W : DirichletCharacter ℂ q → Finset ℂ)
    {U : ℕ} (hU : 1 ≤ U) {Y R V : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R) (hB : 1 ≤ detectorVerticalCutoff R)
    (hchi : ∀ chi rho, rho ∈ W chi → chi ≠ 1)
    (hzero : ∀ chi rho, rho ∈ W chi → DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ chi rho, rho ∈ W chi → 1/2 < rho.re)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 1)
    (hbudget : ∀ chi rho, rho ∈ W chi →
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤ Real.exp (-(1/Y))) :
    (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) ≤
      (∑ chi : DirichletCharacter ℂ q,
        ((arithmeticFamily W U (detectorArithmeticCutoff Y R) Y V chi).card : ℝ)) +
      (∑ chi : DirichletCharacter ℂ q,
        ((centralFamily W U Y (detectorVerticalCutoff R) V chi).card : ℝ)) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro chi hchimem
  have hcover : W chi ⊆ arithmeticFamily W U (detectorArithmeticCutoff Y R) Y V chi ∪
      centralFamily W U Y (detectorVerticalCutoff R) V chi := by
    intro rho hrho
    have h := post_A5_quantitative_detector_dichotomy_polynomial_height chi (hchi chi rho hrho)
      hU (hzero chi rho hrho) (hbetaLow chi rho hrho) (hbetaHigh chi rho hrho) hY hUN hB
      (hbudget chi rho hrho)
    rcases h with hI | hII
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrho,hI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho,hII⟩)
  exact_mod_cast (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)

/-- Principal source partition above the explicit residue cutoff; it uses
exactly the pole-subtracted detector, not an ambient nonprincipal adapter. -/
theorem principal_fullScale_detector_cover
    (W : Finset ℂ) {U : ℕ} (hU : 1 ≤ U) {Y R V c : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R) (hB : 1 ≤ detectorVerticalCutoff R)
    (hzero : ∀ rho ∈ W, MAPPrincipalZetaFixedStrip.principalRegularized rho = 0)
    (hbetaLow : ∀ rho ∈ W, 1/2 < rho.re) (hbetaHigh : ∀ rho ∈ W, rho.re ≤ 1)
    (hresidue : ∀ rho ∈ W, ‖MAPPrincipalZetaDetectorPoleRemoval.principalDetectorResidue rho U Y‖ ≤ c)
    (hbudget : ∀ rho ∈ W,
      MAPPrincipalZetaDetectorDichotomy.principalPoleSubtractedPaperScaleError U rho Y R + c+V+V ≤
        Real.exp (-(1/Y))) :
    W.card ≤
      (W.filter (fun rho => V ≤ ‖arithmeticDetectorBlock (1 : DirichletCharacter ℂ 1) U
        (detectorArithmeticCutoff Y R) rho Y‖)).card +
      (W.filter (fun rho => V ≤ ‖normalizedCentralGammaIntegral (1 : DirichletCharacter ℂ 1)
        U rho Y (detectorVerticalCutoff R)‖)).card := by
  classical
  apply (Finset.card_le_card (t :=
    W.filter (fun rho => V ≤ ‖arithmeticDetectorBlock (1 : DirichletCharacter ℂ 1) U
      (detectorArithmeticCutoff Y R) rho Y‖) ∪
    W.filter (fun rho => V ≤ ‖normalizedCentralGammaIntegral (1 : DirichletCharacter ℂ 1)
      U rho Y (detectorVerticalCutoff R)‖)) ?_).trans (Finset.card_union_le _ _)
  intro rho hrho
  have h := MAPPrincipalZetaDetectorDichotomy.principal_post_A5_quantitative_detector_dichotomy_of_residue_bound
    hU (hzero rho hrho) (hbetaLow rho hrho) (hbetaHigh rho hrho) hY hUN hB
    (hresidue rho hrho) (hbudget rho hrho)
  rcases h with hI | hII
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrho,hI⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho,hII⟩)
end
end MAPMontgomeryFullScaleDetectorPartition
#print axioms MAPMontgomeryFullScaleDetectorPartition.nonprincipal_fullScale_detector_family_cover
#print axioms MAPMontgomeryFullScaleDetectorPartition.principal_fullScale_detector_cover
