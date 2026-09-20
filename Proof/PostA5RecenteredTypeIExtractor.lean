import PostA5TypeIOrdinateRecentering
import PostA5TypeIFourierTailAbsorption

/-!
# Recentered Type-I extraction with the Fourier tail discharged

This is the literal consumer of the arbitrary-moment tail theorem.  It
supplies both Fourier hypotheses of the collar-aware recentering theorem at
the project radius `H=T^h`, leaving no Fourier or ordinate bookkeeping
premise.
-/

namespace PostA5RecenteredTypeIExtractor

open Filter Set MeasureTheory
open scoped BigOperators FourierTransform
open CGLProofDAG MAPAppendixA4PostA5SetAdapter SchwartzMap
open PostA5TypeIFourierAssembly PostA5TypeIOrdinateRecentering
open PostA5TypeIFourierTailAbsorption

noncomputable section

/-- The collar-aware common polynomial extractor with its uniform central
Fourier mass and complement tail both discharged.  Every dependence on the
zero real part, the selected shell, and the multiplicity function remains
literal in the statement. -/
theorem eventually_exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar_inputLoss
    (kappa eta e h : ℝ)
    (hkappa : 0 < kappa) (heta : 0 < eta) (he : 0 < e) (hh : 0 < h) :
    ∀ᶠ T : ℝ in Filter.atTop,
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
        (U N : ℕ) (Y sigma V : ℝ)
        (j : Fin (detectorDyadicCount N))
        (S : Finset ℂ) (weight : ℂ → ℕ) (C M : ℕ),
        4 ≤ T → 1 ≤ U → 0 < Y → 0 < V →
        Real.rpow T (-inputLoss kappa eta) ≤ V →
        (∀ rho ∈ S, sigma ≤ rho.re) →
        (∀ rho ∈ S, rho.re ≤ 1) →
        7 / 10 ≤ sigma → sigma ≤ 4 / 5 →
        ((2 ^ (j : ℕ) : ℕ) : ℝ) ≤ T →
        (detectorDyadicCount N : ℝ) ≤ 2 * T →
        2 * Real.pi * Real.rpow T h ≤ C →
        (∀ rho ∈ S, |rho.im| ≤ T) →
        (∀ rho ∈ S,
          V ≤ detectorDyadicCount N *
            ‖arithmeticDetectorDyadicBlock chi U N rho Y j‖) →
        (∀ m : ℤ,
          ∑ rho ∈ S with Int.floor rho.im = m, weight rho ≤ M) →
        ∃ (b : ℕ → ℂ) (W : Finset ℝ),
          (∀ n, ‖b n‖ =
            ‖detectorCommonCoefficient chi U N Y sigma n‖) ∧
          OneSeparated W ∧
          (∀ t ∈ W, 0 ≤ t ∧ t ≤ T) ∧
          (∀ t ∈ W,
            V / (4 * (24 * Real.rpow T h) * detectorDyadicCount N) ≤
              ‖dirichletPolynomial b (2 ^ (j : ℕ)) t‖) ∧
          ∑ rho ∈ S, weight rho ≤
            4 * (shiftedFloorWindowCount C * M) * W.card +
              2 * (C + 1) * M := by
  filter_upwards
      [eventually_exists_fourierMoment_detectorCommonCoefficient_mul_fourierTail_le_inputLoss
        kappa eta e h hkappa heta he hh] with T htail
  intro q _inst chi U N Y sigma V j S weight C M hT hU hY hV hVlower
    hbetaLow hbetaHigh hsigmaLow hsigmaHigh hDT hJ hC hheight hblock hsource
  have hTpos : 0 < T := by linarith
  have hApos : 0 < 24 * Real.rpow T h := by
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hTpos _)
  apply exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar
    chi hU Y sigma j S weight hC hheight hApos hV
  · intro rho hrho
    have hrhoS : rho ∈ S := Finset.filter_subset _ _ hrho
    have ha0 : 0 ≤ rho.re - sigma := sub_nonneg.mpr (hbetaLow rho hrhoS)
    have ha3 : rho.re - sigma ≤ 3 / 10 := by
      linarith [hbetaHigh rho hrhoS]
    exact integral_norm_fourier_detectorRealPartCutoff_Icc_le
      Nat.one_le_two_pow ha0 ha3
      (Real.rpow_nonneg hTpos.le h)
  · intro rho hrho
    have hrhoS : rho ∈ S := Finset.filter_subset _ _ hrho
    exact htail q chi U N Y sigma rho j V hT hY
      hsigmaLow hsigmaHigh
      (hbetaLow rho hrhoS)
      (hbetaHigh rho hrhoS)
      hDT hJ hVlower
  · exact hblock
  · exact hsource

end
end PostA5RecenteredTypeIExtractor

#print axioms PostA5RecenteredTypeIExtractor.eventually_exists_typeI_commonPolynomial_oneSeparated_recentered_with_collar_inputLoss
