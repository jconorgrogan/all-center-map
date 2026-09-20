import MontgomeryLowStripContinuousTypeII
import MontgomeryLowStripSourceSplit
import PostA5LongSpacingAssembly

/-!
# Retained-integral Montgomery low-strip split

This module splices the quantitative Appendix A.4 detector dichotomy into the
continuous Type-II route.  Unlike the older source split, its Type-II fiber
retains the normalized central Gamma integral and therefore never assumes a
discrete fourth moment or extracts a critical-line point.
-/

namespace MAPMontgomeryLowStripContinuousSourceSplit

open Set Complex
open scoped BigOperators
open CGLProofDAG MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter MAPAppendixA4RecenteredGammaRepair
open PostA5LongSpacingAssembly
open PostA5CrowdingDeterministic DirichletZeros MAPAPZeroDensityCert
open MAPMontgomeryLowStripContinuousTypeII

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The literal retained-integral Type-II fiber of the detector partition. -/
def lowStripCentralTypeIISet
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (Y R V : ℝ) (Z : Finset ℂ) : Finset ℂ := by
  classical
  exact Z.filter fun rho =>
    V ≤ ‖normalizedCentralGammaIntegral chi U rho Y
      (detectorVerticalCutoff R)‖

theorem mem_lowStripCentralTypeIISet_iff
    (chi : DirichletCharacter ℂ q) (U : ℕ)
    (Y R V : ℝ) (Z : Finset ℂ) (rho : ℂ) :
    rho ∈ lowStripCentralTypeIISet chi U Y R V Z ↔
      rho ∈ Z ∧
      V ≤ ‖normalizedCentralGammaIntegral chi U rho Y
        (detectorVerticalCutoff R)‖ := by
  simp [lowStripCentralTypeIISet]

/-- Pointwise low-strip detector split retaining the central integral. -/
theorem detector_to_typeI_or_centralTypeII_lowStrip
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y R V : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤
        Real.exp (-(1 / Y))) :
    V ≤ ‖arithmeticDetectorBlock chi U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      V ≤ ‖normalizedCentralGammaIntegral chi U rho Y
        (detectorVerticalCutoff R)‖ := by
  exact post_A5_quantitative_detector_dichotomy_polynomial_height
    chi hchi hU hrho (by linarith) (by linarith) hY hUN hB hbudget

/-- Finite zero-set partition with one common Type-I dyadic shell and the
retained-integral Type-II fiber. -/
theorem zeroSet_common_dyadic_or_centralTypeII_lowStrip
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R V : ℝ} (hY : 1 ≤ Y)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 7 / 10)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤
        Real.exp (-(1 / Y))) :
    ∃ j : Fin (detectorDyadicCount (detectorArithmeticCutoff Y R)),
      ∃ S : Finset ℂ,
        S ⊆ postA5TypeISet chi U Y R V Z ∧
        (postA5TypeISet chi U Y R V Z).card ≤
          detectorDyadicCount (detectorArithmeticCutoff Y R) * S.card ∧
        (∀ rho ∈ S,
          V ≤ detectorDyadicCount (detectorArithmeticCutoff Y R) *
            ‖arithmeticDetectorDyadicBlock chi U
              (detectorArithmeticCutoff Y R) rho Y j‖) ∧
        Z.card ≤ (postA5TypeISet chi U Y R V Z).card +
          (lowStripCentralTypeIISet chi U Y R V Z).card := by
  classical
  let ZI := postA5TypeISet chi U Y R V Z
  let ZII := lowStripCentralTypeIISet chi U Y R V Z
  have hsubset : Z ⊆ ZI ∪ ZII := by
    intro rho hrhoZ
    rcases detector_to_typeI_or_centralTypeII_lowStrip chi hchi hdelta hU
        (hzero rho hrhoZ) (hbetaLow rho hrhoZ) (hbetaHigh rho hrhoZ)
        hY hUN hB (hbudget rho hrhoZ) with hI | hII
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrhoZ, hI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrhoZ, hII⟩)
  have hcard : Z.card ≤ ZI.card + ZII.card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hlarge : ∀ rho ∈ ZI,
      V ≤ ‖arithmeticDetectorBlock chi U
        (detectorArithmeticCutoff Y R) rho Y‖ := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).2
  obtain ⟨j, S, hS, hcardI, hblock⟩ :=
    exists_common_arithmeticDetectorDyadicBlock chi hU hUN hlarge
  refine ⟨j, S, hS, hcardI, hblock, ?_⟩
  simpa [ZI, ZII] using hcard

/-- Per-character `3B` thinning of the retained central-integral fiber.  The
only loss is the already certified local A.5 crowding cap and the explicit
residue-color count. -/
theorem exists_threeBSeparated_centralTypeII
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {sigma T : ℝ} (hsigma : 1 / 2 ≤ sigma) (hT : 0 ≤ T)
    {U : ℕ} {Y R V B : ℝ} (hB : 0 ≤ B) :
    ∃ S : Finset ℂ,
      S ⊆ lowStripCentralTypeIISet chi U Y R V
        (zeroSupport chi sigma T) ∧
      (∀ rho ∈ S, ∀ rho' ∈ S, rho ≠ rho' →
        3 * B ≤ |rho.im - rho'.im|) ∧
      (lowStripCentralTypeIISet chi U Y R V
        (zeroSupport chi sigma T)).card ≤
        longSpacingColorCount B * certifiedA5CrowdingNatCap q T * S.card := by
  let ZII := lowStripCentralTypeIISet chi U Y R V
    (zeroSupport chi sigma T)
  apply exists_threeBSeparated_representatives ZII hB
  intro n hn
  have hsub :
      (ZII.filter fun rho => Int.floor rho.im = n) ⊆
        ((zeroSupport chi sigma T).filter fun rho => Int.floor rho.im = n) := by
    intro rho hrho
    have hz := Finset.mem_filter.mp hrho
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hz.1).1, hz.2⟩
  exact (Finset.card_le_card hsub).trans
    (zeroSupport_floorBin_card_le_crowdingNatCap chi hchi hsigma hT
      (by
        rcases Finset.mem_image.mp hn with ⟨rho, hrho, rfl⟩
        exact Finset.mem_image.mpr
          ⟨rho, (Finset.mem_filter.mp hrho).1, rfl⟩))

/-- Exact adapter from a simultaneously selected `3B`-spaced retained-
integral family to the premise-free Ramachandra Type-II budget.  Membership
in the central fiber supplies the zero, height, real-part, and detector lower
bound data; no pointwise or discrete fourth moment is introduced. -/
theorem centralTypeII_selected_budget_ramachandra
    (W : DirichletCharacter ℂ q → Finset ℂ)
    {delta sigma T Y R V : ℝ} {U : ℕ}
    (hdelta : 0 < delta) (hY : 1 ≤ Y)
    (hB : 0 < detectorVerticalCutoff R)
    (hT : 0 ≤ T) (hTB : 3 ≤ T + detectorVerticalCutoff R)
    (hV : 0 ≤ V) (hsigmaDelta : 1 / 2 + delta ≤ sigma)
    (hsub : ∀ chi, W chi ⊆
      lowStripCentralTypeIISet chi U Y R V (zeroSupport chi sigma T))
    (hnonprincipal : ∀ chi rho, rho ∈ W chi → chi ≠ 1)
    (hbetaHigh : ∀ chi rho, rho ∈ W chi → rho.re ≤ 7 / 10)
    (hsep : ∀ chi rho, rho ∈ W chi → ∀ rho', rho' ∈ W chi →
      rho ≠ rho' →
        3 * detectorVerticalCutoff R ≤ |rho.im - rho'.im|) :
    ∃ C₆ : ℝ, 0 < C₆ ∧
      (∑ chi : DirichletCharacter ℂ q, ((W chi).card : ℝ)) * V ^ 4 ≤
        ((MAPMontgomeryLowStripGamma.lowStripGammaConstant delta / Real.pi) *
            Real.rpow Y (1 / 2 - sigma) * (2 * Real.sqrt U)) ^ 4 *
          (∫ u in (-(detectorVerticalCutoff R))..(detectorVerticalCutoff R),
            MAPMRTCorollary25Minkowski.perronWeight u) ^ 3 *
          (C₆ *
            RamachandraTheorem6ShiftedStripSource.ramachandraTheorem6K2Scale
              q (T + detectorVerticalCutoff R)) := by
  apply continuous_typeII_family_budget_ramachandra W hdelta hY hB hT hTB hV
  · exact hnonprincipal
  · intro chi rho hrhoW
    have hz : rho ∈ zeroSupport chi sigma T :=
      (Finset.mem_filter.mp (hsub chi hrhoW)).1
    have hreg := regularizedLFunction_eq_zero_of_mem_zeroSupport
      chi sigma T hz
    simpa [regularizedLFunction, hnonprincipal chi rho hrhoW] using hreg
  · intro chi rho hrhoW
    have hz : rho ∈ zeroSupport chi sigma T :=
      (Finset.mem_filter.mp (hsub chi hrhoW)).1
    have hrect := PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
      chi sigma T hz
    exact hsigmaDelta.trans hrect.1.1
  · exact hbetaHigh
  · intro chi rho hrhoW
    have hz : rho ∈ zeroSupport chi sigma T :=
      (Finset.mem_filter.mp (hsub chi hrhoW)).1
    exact (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
      chi sigma T hz).1.1
  · intro chi rho hrhoW
    have hz : rho ∈ zeroSupport chi sigma T :=
      (Finset.mem_filter.mp (hsub chi hrhoW)).1
    exact abs_le.mpr
      (PrimitiveExplicitFormulaSpine.mem_zeroRectangle_of_mem_zeroSupport
        chi sigma T hz).2
  · exact hsep
  · intro chi rho hrhoW
    exact (Finset.mem_filter.mp (hsub chi hrhoW)).2

end
end MAPMontgomeryLowStripContinuousSourceSplit

#print axioms MAPMontgomeryLowStripContinuousSourceSplit.detector_to_typeI_or_centralTypeII_lowStrip
#print axioms MAPMontgomeryLowStripContinuousSourceSplit.zeroSet_common_dyadic_or_centralTypeII_lowStrip
#print axioms MAPMontgomeryLowStripContinuousSourceSplit.exists_threeBSeparated_centralTypeII
#print axioms MAPMontgomeryLowStripContinuousSourceSplit.centralTypeII_selected_budget_ramachandra
