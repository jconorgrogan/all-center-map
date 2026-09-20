import LowStripGammaKernel
import PostA5TypeIIFourthMoment
import AppendixA4PostA5SetAdapter
import AppendixA4RecenteredGammaRepair

/-!
# Source-normalized Montgomery low-strip detector split

The existing low-strip detector wrapper uses one common threshold on both
branches.  Montgomery's fourth-moment branch needs the sharper normalization
retaining `Y^(beta-1/2) / sqrt U`.  This file derives that pointwise form from
the certified contour detector and lifts it to a finite zero-set partition.
-/

namespace MAPMontgomeryLowStripSourceSplit

open Set Complex
open scoped BigOperators
open CGLProofDAG MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter MAPMontgomeryLowStripGamma
open MAPAppendixA4RecenteredGammaRepair

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The low-strip pointwise detector with the precise Type-II normalization
needed before a fourth-moment estimate. -/
theorem detector_to_typeI_or_sourceTypeII_lowStrip
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 + delta ≤ rho.re)
    (hbetaHigh : rho.re ≤ 7 / 10)
    {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R + V + V ≤
        Real.exp (-(1 / Y))) :
    V ≤ ‖arithmeticDetectorBlock chi U
        (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V /
            ((lowStripGammaConstant delta / 2) *
              Real.rpow Y (1 / 2 - rho.re) *
              (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
  rcases
      post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value_polynomial_height
        chi hchi hU hrho (by linarith) (by linarith) hY hUN hB
          (a := V) (b := V) hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)
    let D : ℝ := (1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)
    let W : ℝ := 2 * Real.sqrt U
    let E : ℝ := (lowStripGammaConstant delta / 2) *
      Real.rpow Y (1 / 2 - rho.re) * W
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hBpos : 0 < detectorVerticalCutoff R := zero_lt_one.trans_le hB
    have hmasspos : 0 <
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R) :=
      truncatedGammaLeftKernelMass_pos (by linarith) (by linarith)
        hYpos hBpos
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hWpos : 0 < W := by
      dsimp [W]
      have hUpos : (0 : ℝ) < U := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
      positivity
    have hEpos : 0 < E := by
      dsimp [E]
      have hC := lowStripGammaConstant_pos hdelta
      positivity
    have hDle :
        D ≤ (lowStripGammaConstant delta / 2) *
          Real.rpow Y (1 / 2 - rho.re) := by
      have hmass := truncatedGammaLeftKernelMass_le_lowStrip
        hdelta hbetaLow hbetaHigh hY (by linarith : 0 ≤ detectorVerticalCutoff R)
      dsimp [D]
      calc
        (1 / (2 * Real.pi)) *
            truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R) ≤
          (1 / (2 * Real.pi)) *
            (lowStripGammaConstant delta * Real.pi *
              Real.rpow Y (1 / 2 - rho.re)) := by
          exact mul_le_mul_of_nonneg_left hmass (by positivity)
        _ = (lowStripGammaConstant delta / 2) *
            Real.rpow Y (1 / 2 - rho.re) := by
          field_simp [ne_of_gt Real.pi_pos]
    have hDE : D * W ≤ E := by
      dsimp [E]
      exact mul_le_mul_of_nonneg_right hDle hWpos.le
    have hsre : s.re = 1 / 2 := by dsimp [s]; simp
    have hM := PostA5TypeIIFourthMoment.norm_mollifier_criticalLine_le_two_sqrt
      chi U hsre
    have hproduct : V / D ≤
        ‖DirichletCharacter.LFunction chi s *
          MAPMollifierCoefficientIdentity.mollifier chi U s‖ := by
      simpa [D, s] using htlarge
    have hLraw := PostA5TypeIIFourthMoment.norm_lower_of_product
      hWpos hproduct hM
    have hL : V / (D * W) ≤ ‖DirichletCharacter.LFunction chi s‖ := by
      simpa [div_div] using hLraw
    refine ⟨t, ht, ?_⟩
    have hquot : V / E ≤ V / (D * W) :=
      (div_le_div_iff_of_pos_left hV hEpos (mul_pos hDpos hWpos)).2 hDE
    exact hquot.trans (by simpa [E, W, s] using hL)

/-- The actual low-strip Type-II fiber carrying the beta-dependent critical
line lower bound. -/
def lowStripSourceTypeIISet
    (chi : DirichletCharacter ℂ q) (delta : ℝ) (U : ℕ)
    (Y R V : ℝ) (Z : Finset ℂ) : Finset ℂ := by
  classical
  exact Z.filter fun rho =>
    ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
        (detectorVerticalCutoff R),
      V /
          ((lowStripGammaConstant delta / 2) *
            Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) ≤
        ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖

theorem mem_lowStripSourceTypeIISet_iff
    (chi : DirichletCharacter ℂ q) (delta : ℝ) (U : ℕ)
    (Y R V : ℝ) (Z : Finset ℂ) (rho : ℂ) :
    rho ∈ lowStripSourceTypeIISet chi delta U Y R V Z ↔
      rho ∈ Z ∧
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V /
            ((lowStripGammaConstant delta / 2) *
              Real.rpow Y (1 / 2 - rho.re) *
              (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
  simp [lowStripSourceTypeIISet]

/-- Finite zero-set lift of the source-normalized low-strip split.  One
Type-I dyadic shell is common, while the Type-II fiber retains the precise
critical-line normalization. -/
theorem zeroSet_common_dyadic_or_sourceTypeII_lowStrip
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {delta : ℝ} (hdelta : 0 < delta)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R V : ℝ} (hY : 1 ≤ Y) (hV : 0 < V)
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
          (lowStripSourceTypeIISet chi delta U Y R V Z).card := by
  classical
  let ZI := postA5TypeISet chi U Y R V Z
  let ZII := lowStripSourceTypeIISet chi delta U Y R V Z
  have hsubset : Z ⊆ ZI ∪ ZII := by
    intro rho hrho
    rcases detector_to_typeI_or_sourceTypeII_lowStrip
        chi hchi hdelta hU (hzero rho hrho) (hbetaLow rho hrho)
        (hbetaHigh rho hrho) hY hV hUN hB (hbudget rho hrho) with hI | hII
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hrho, hI⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hrho, hII⟩)
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

end
end MAPMontgomeryLowStripSourceSplit

#print axioms MAPMontgomeryLowStripSourceSplit.detector_to_typeI_or_sourceTypeII_lowStrip
#print axioms MAPMontgomeryLowStripSourceSplit.mem_lowStripSourceTypeIISet_iff
#print axioms MAPMontgomeryLowStripSourceSplit.zeroSet_common_dyadic_or_sourceTypeII_lowStrip
