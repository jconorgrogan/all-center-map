import GuthMaynardJIterationEllRestrictionWeld
import GuthMaynardLemma92SelectedDeltaWeld
import GuthMaynardLemma92VariableEllRadiusWeld

/-!
# Large first-Poisson ell cover to the selected Lemma 9.2 producer

This module composes the exact Fourier-decay ell restriction with the
selected-range second-Poisson theorem.  It keeps the two analytically distinct
tails separate: the first is the discarded large-ell contribution, and the
second is the determinant/second-Poisson tail already bounded by `T^-100`.
-/

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Exact discarded-ell cost for the source dyadic specialization. -/
def sourceLemma92EllTailCost
    (ellRange : Finset ℤ) (M : ℕ)
    (T S eta C delta : ℝ) (j : ℕ) : ℝ :=
  (ellRange.card : ℝ) * (2 * T ^ delta) *
    (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
      (C * T ^ eta *
        (T / ((M : ℝ) *
          (T / (M : ℝ) - T ^ delta / (M : ℝ)))) ^ j * S)) ^ 2)

/-- Exact discarded-ell cost with an independent detector radius. -/
def sourceLemma92EllTailCostRadius
    (ellRange : Finset ℤ) (M : ℕ)
    (T S eta C delta R : ℝ) (j : ℕ) : ℝ :=
  (ellRange.card : ℝ) * (2 * T ^ delta) *
    (((4 * (M : ℝ) + 3) * (2 * (M : ℝ)) *
      (C * T ^ eta *
        (T / ((M : ℝ) *
          (R * T / (M : ℝ) - T ^ delta / (M : ℝ)))) ^ j * S)) ^ 2)

/-- A large first-Poisson ell range is reduced to the literal short bump
range consumed by `sigmaIIFinite_selectedPositiveDyadic_concreteBumps_delta_le`,
with both source tails explicit. -/
theorem sigmaIIFinite_largeEll_selectedPositiveDyadic_delta_le
    {T S F delta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange ellRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q j : ℕ) (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hBT : T ^ delta < T)
    {etaTail Ctail : ℝ} (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hthreshold : 25 * sourceLemma92Decay q * integerQuadraticMass ≤
      T ^ (delta * (q : ℝ) - 107)) :
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T (M : ℝ) (T ^ delta) ≤
      ((2 * T ^ delta * sourceLemma92Sup0) * (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * T ^ delta)))
              (affineSmoothing T
                (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
              (sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100)) +
        sourceLemma92EllTailCost ellRange M T S etaTail Ctail delta j
      ∧ sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100 ≤
        T⁻¹ ^ 100 := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := (Real.rpow_pos_of_pos hTpos delta).le
  have hell := sigmaIIFinite_const_one_le_sourceBump_add_ellTail
    ellRange mRange
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) hM hmRange
    j hTpos hf.bound_nonneg hCtail hB0 hBT hFourierTail
  obtain ⟨hsmall, hsecondTail⟩ :=
    sigmaIIFinite_selectedPositiveDyadic_concreteBumps_delta_le
      hf hM mRange hmRange q hT hF0 hF hMhi hB0 hthreshold
  constructor
  · calc
      sigmaIIFinite ellRange mRange (fun _ => 1)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T (M : ℝ) (T ^ delta) ≤
        sigmaIIFinite (sourceBumpEllRange M T 1) mRange
            (fun x => sourceBump 1 zero_lt_one x)
            (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
            (M : ℝ) T (M : ℝ) (T ^ delta) +
          sourceLemma92EllTailCost ellRange M T S etaTail Ctail delta j := by
            simpa [sourceLemma92EllTailCost, mul_assoc] using hell
      _ ≤ (((2 * T ^ delta * sourceLemma92Sup0) * (2 : ℝ) ^ 2 * (M : ℝ)) *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * T ^ delta)))
                (affineSmoothing T
                  (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
          ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
            |(m2 : ℝ) * (m2' : ℝ)| *
              (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
                (sourceLemma92SecondPoissonCDelta T F delta M q / T ^ 100))) +
          sourceLemma92EllTailCost ellRange M T S etaTail Ctail delta j :=
            add_le_add hsmall le_rfl
  · exact hsecondTail

/-- Correct source-shaped composition with an independent subpower
ell-detector radius.  Unlike the radius-one diagnostic above, choosing
`R=T^κ` makes the discarded-ell factor power-saving. -/
theorem sigmaIIFinite_largeEll_selectedPositiveDyadic_variableRadius_le
    {T S F delta : ℝ} {f : ℝ → ℝ}
    (hf : SourceAdmissibleProfile T S F f)
    {M : ℕ} (hM : 0 < M) (mRange ellRange : Finset ℤ)
    (hmRange : mRange ⊆ sourcePositiveDyadicRange M)
    (q j : ℕ) {R Csecond etaTail Ctail : ℝ}
    (hR : 0 < R) (hRone : 1 ≤ R)
    (hT : 1 ≤ T) (hF0 : 0 ≤ F) (hF : F ≤ T)
    (hMhi : (M : ℝ) ≤ T ^ 4)
    (hBRT : T ^ delta < R * T)
    (hCsecond : 0 ≤ Csecond) (hCtail : 0 ≤ Ctail)
    (hFourierTail : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        Ctail * T ^ etaTail * (T / |z|) ^ j * S)
    (hsecondBudget :
      ((T / (M : ℝ)) *
          (R * sourceBumpFourierConstant 1 zero_lt_one (q + 2)) *
          ((1 + (4 * (M : ℝ) * F) / ((M : ℝ) / T)) ^ 2 *
            max 1 (((M : ℝ) / T) ^ 2) * integerQuadraticMass) * T ^ 100 ≤
        Csecond * (T ^ delta) ^ q)) :
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T (M : ℝ) (T ^ delta) ≤
      ((2 * T ^ delta *
          (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
          (2 : ℝ) ^ 2 * (M : ℝ)) *
          Real.sqrt ((∫ u : ℝ, f u ^ 2) *
            sourceAffineJ
              (sourceAffineConfigs (sourcePositiveDyadicRange M)
                (sourceLemma92JRange M T F (2 * T ^ delta)))
              (affineSmoothing T
                (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
        ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
          |(m2 : ℝ) * (m2' : ℝ)| *
            (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
              (Csecond / T ^ 100)) +
        sourceLemma92EllTailCostRadius ellRange M T S etaTail Ctail
          delta R j := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hB0 : 0 ≤ T ^ delta := (Real.rpow_pos_of_pos hTpos delta).le
  have hell := sigmaIIFinite_const_one_le_sourceBump_radius_add_ellTail
    ellRange mRange
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) hM hmRange
    j hTpos hf.bound_nonneg hCtail hB0 hR hBRT hFourierTail
  have hsmall := sigmaIIFinite_selectedPositiveDyadic_variableEllRadius_le
    hf hM mRange hmRange q hR hRone hT hF0 hF hMhi hB0
    hCsecond hsecondBudget
  calc
    sigmaIIFinite ellRange mRange (fun _ => 1)
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        (M : ℝ) T (M : ℝ) (T ^ delta) ≤
      sigmaIIFinite (sourceBumpEllRange M T R) mRange
          (fun x => sourceBump R hR x)
          (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
          (M : ℝ) T (M : ℝ) (T ^ delta) +
        sourceLemma92EllTailCostRadius ellRange M T S etaTail Ctail
          delta R j := by
            simpa [sourceLemma92EllTailCostRadius, mul_assoc] using hell
    _ ≤ (((2 * T ^ delta *
            (R * sourceBumpFourierConstant 1 zero_lt_one 0)) *
            (2 : ℝ) ^ 2 * (M : ℝ)) *
            Real.sqrt ((∫ u : ℝ, f u ^ 2) *
              sourceAffineJ
                (sourceAffineConfigs (sourcePositiveDyadicRange M)
                  (sourceLemma92JRange M T F (2 * T ^ delta)))
                (affineSmoothing T
                  (fun z => sourceBump (T ^ delta) (by positivity) z) f)) +
          ∑ m2 ∈ mRange, ∑ m2' ∈ mRange,
            |(m2 : ℝ) * (m2' : ℝ)| *
              (((∫ u : ℝ, |f u|) ^ 2 * (2 * T ^ delta)) *
                (Csecond / T ^ 100))) +
        sourceLemma92EllTailCostRadius ellRange M T S etaTail Ctail
          delta R j := add_le_add hsmall le_rfl

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sigmaIIFinite_largeEll_selectedPositiveDyadic_delta_le
#print axioms GuthMaynardJIteration.sigmaIIFinite_largeEll_selectedPositiveDyadic_variableRadius_le
