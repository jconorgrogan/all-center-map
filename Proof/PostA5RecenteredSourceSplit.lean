import AppendixA4RecenteredGammaRepair
import AppendixA4PostA5SetAdapter
import PostA5TypeIIFourthMoment

/-!
# Source-normalized Type-II split for the recentered detector

The bridge-facing repaired adapter uses a common threshold on both branches.
For the direct fourth-moment route one must instead retain the literal
`Y^(beta-1/2) / sqrt U` gain.  This module derives that stronger Type-II
alternative directly from the repaired polynomial-height Gamma dichotomy and
lifts it to the same finite common-dyadic Type-I partition.
-/

namespace PostA5RecenteredSourceSplit

open Set Complex
open scoped BigOperators
open CGLProofDAG MAPAppendixA4DetectorDichotomy
open MAPAppendixA4PostA5SetAdapter MAPAppendixA4RecenteredGammaRepair

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Repaired polynomial-height version of the source-normalized pointwise
Type-II alternative.  The sharp `2*sqrt U` mollifier bound is what retains the
published fourth-moment exponent. -/
theorem post_A5_detector_to_typeI_or_sourceTypeII_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
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
            (29 * Real.rpow Y (1 / 2 - rho.re) *
              (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
  rcases
      post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value_polynomial_height
        chi hchi hU hrho (by linarith) hbetaHigh hY hUN hB hbudget with
      hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)
    let D : ℝ := (1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)
    let W : ℝ := 2 * Real.sqrt U
    let E : ℝ := 29 * Real.rpow Y (1 / 2 - rho.re) * W
    have hYpos : 0 < Y := zero_lt_one.trans_le hY
    have hBpos : 0 < detectorVerticalCutoff R := zero_lt_one.trans_le hB
    have hmasspos : 0 <
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R) :=
      truncatedGammaLeftKernelMass_pos (by linarith) hbetaHigh hYpos hBpos
    have hDpos : 0 < D := by dsimp [D]; positivity
    have hWpos : 0 < W := by
      dsimp [W]
      have hUpos : (0 : ℝ) < U := by
        exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hU)
      positivity
    have hEpos : 0 < E := by dsimp [E]; positivity
    have hDle : D ≤ 29 * Real.rpow Y (1 / 2 - rho.re) := by
      have h := normalized_truncatedGammaLeftKernelMass_le_uniform
        hbetaLow hbetaHigh 0 hY (zero_le_one.trans hB)
      simpa [D] using h
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

/-- The actual finite Type-II fiber carrying the source-normalized lower
bound. -/
def postA5SourceTypeIISet
    (chi : DirichletCharacter ℂ q) (U : ℕ) (Y R V : ℝ)
    (Z : Finset ℂ) : Finset ℂ := by
  classical
  exact Z.filter fun rho =>
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V / (29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖

theorem mem_postA5SourceTypeIISet_iff
    (chi : DirichletCharacter ℂ q) (U : ℕ) (Y R V : ℝ)
    (Z : Finset ℂ) (rho : ℂ) :
    rho ∈ postA5SourceTypeIISet chi U Y R V Z ↔
      rho ∈ Z ∧
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R))
          (detectorVerticalCutoff R),
        V / (29 * Real.rpow Y (1 / 2 - rho.re) *
            (2 * Real.sqrt U)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * Complex.I)‖ := by
  simp [postA5SourceTypeIISet]

/-- Finite repaired handoff with the common Type-I dyadic shell and the
source-normalized Type-II fiber kept separate. -/
theorem post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII_polynomial_height
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {kappa eta : ℝ} (hkappa : 0 < kappa) (heta : 0 < eta)
    {U : ℕ} (hU : 1 ≤ U)
    {Z : Finset ℂ} {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hzero : ∀ rho ∈ Z, DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : ∀ rho ∈ Z, 7 / 10 ≤ rho.re)
    (hbetaHigh : ∀ rho ∈ Z, rho.re ≤ 1)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : ∀ rho ∈ Z,
      detectorTruncationErrorEnvelopePolynomialHeight q U rho Y R +
          Real.rpow R (-inputLoss kappa eta) +
          Real.rpow R (-inputLoss kappa eta) ≤
        Real.exp (-(1 / Y))) :
    ∃ j : Fin (detectorDyadicCount (detectorArithmeticCutoff Y R)),
      ∃ S : Finset ℂ,
        S ⊆ postA5TypeISet chi U Y R
          (Real.rpow R (-inputLoss kappa eta)) Z ∧
        (postA5TypeISet chi U Y R
          (Real.rpow R (-inputLoss kappa eta)) Z).card ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) * S.card ∧
        (∀ rho ∈ S,
          Real.rpow R (-inputLoss kappa eta) ≤
            detectorDyadicCount (detectorArithmeticCutoff Y R) *
              ‖arithmeticDetectorDyadicBlock chi U
                (detectorArithmeticCutoff Y R) rho Y j‖) ∧
        Z.card ≤
          (postA5TypeISet chi U Y R
            (Real.rpow R (-inputLoss kappa eta)) Z).card +
          (postA5SourceTypeIISet chi U Y R
            (Real.rpow R (-inputLoss kappa eta)) Z).card := by
  classical
  let V := Real.rpow R (-inputLoss kappa eta)
  let ZI := postA5TypeISet chi U Y R V Z
  let ZII := postA5SourceTypeIISet chi U Y R V Z
  have hsubset : Z ⊆ ZI ∪ ZII := by
    intro rho hrho
    have hVpos : 0 < V := by
      dsimp [V]
      exact Real.rpow_pos_of_pos hR _
    rcases post_A5_detector_to_typeI_or_sourceTypeII_polynomial_height
        chi hchi hU (hzero rho hrho) (hbetaLow rho hrho)
        (hbetaHigh rho hrho) hY hVpos hUN hB
        (by simpa [V] using hbudget rho hrho) with hI | hII
    · exact Finset.mem_union_left _
        (Finset.mem_filter.mpr ⟨hrho, hI⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hrho, hII⟩)
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
  simpa [ZI, ZII, V] using hcard

end
end PostA5RecenteredSourceSplit

#print axioms PostA5RecenteredSourceSplit.post_A5_detector_to_typeI_or_sourceTypeII_polynomial_height
#print axioms PostA5RecenteredSourceSplit.mem_postA5SourceTypeIISet_iff
#print axioms PostA5RecenteredSourceSplit.post_A5_budgeted_zeroSet_common_dyadic_or_sourceTypeII_polynomial_height
