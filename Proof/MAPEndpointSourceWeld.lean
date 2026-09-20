import MAPEndpointIntegrationScaffold
import APAlignedShortIntervalConnector
import APAlignedComponentShortInterval
import MRTProposition51Constructor
import MAPFarSourceWeldScaffold
import PsiEndpointImprimitiveAdapters

/-!
# Source-level weld for the reliable MAP endpoint

This module composes the closest existing constructors for three of the four
public endpoint premises.  The constants in the MRT and far-source interfaces
are synchronized at `1`, the AP interface is constructed from its weighted
zero-mass and literal contour-tail inputs, and the far-source interface is
constructed from the literal padded-source budget.

No published statement is promoted to a proof here: every analytic source
input remains an explicit theorem parameter.
-/

namespace MAPEndpointSourceWeld

open PrimePairEndpoints
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51Constructor MAPMRTProposition51Supported
open MAPFixedScaleAPZeroRoute MAPAPAlignedTailToRemainderTransfer
open MAPAPAlignedShortIntervalConnector MAPFarSourceWeldScaffold
open MAPAPAlignedComponentSource

noncomputable section

/-- Source-level endpoint constructor after eliminating the packaged AP,
Proposition 5.1, and far-source premises.

The remaining parameters are the pointwise twisted Mangoldt theorem and the
literal analytic leaves feeding the three existing constructors. -/
theorem fullUnconditionalMAPEndpoint_of_sourceLeaves
    (hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (h27 : APWeightedZeroMassLogSaving)
    (hAPTail : AlignedAPExplicitFormulaTailFamilySquare)
    {Chard : ℝ}
    (hChard : 0 < Chard)
    (hHard : ∀ (p : Proposition51Input),
      Proposition51Admissible 1 1 p →
      1 < |p.beta| * p.H → p.eta < 1 / 100 →
      proposition51Energy p ≤ Chard *
        (1 / (|p.beta| ^ 2 * p.H ^ 2) *
            proposition51I p.X p.H p.f p.beta p.eta +
          ordinaryError p.X p.H p.f p.beta p.eta))
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    FullUnconditionalMAPEndpoint := by
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_alignedTail
      h27 hAPTail
  have hP51 : MRTProposition51 1 1 :=
    mrtProposition51_of_hard_branch hChard hHard
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget hFarBudget
  exact
    MAPEndpointIntegrationScaffold.fullUnconditionalMAPEndpoint_of_remaining_activeLeaves
      hSW hAP hP51 hFar

/-- Fully source-facing endpoint constructor: none of the four packaged
premises of `fullUnconditionalMAPEndpoint_of_remaining_activeLeaves` remains.

The twisted Mangoldt input is restricted to primitive characters; the
imprimitive correction is supplied by the compiled deterministic adapter. -/
theorem fullUnconditionalMAPEndpoint_of_primitive_sourceLeaves
    (hPrimitive :
      ∀ A B : ℕ, ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
          ∀ X : ℝ, X0 ≤ X →
          ∀ q : ℕ, 1 ≤ q →
            (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
          ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
            ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
                MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
              C * X / (Real.log X) ^ A)
    (h27 : APWeightedZeroMassLogSaving)
    (hAPTail : AlignedAPExplicitFormulaTailFamilySquare)
    {Chard : ℝ}
    (hChard : 0 < Chard)
    (hHard : ∀ (p : Proposition51Input),
      Proposition51Admissible 1 1 p →
      1 < |p.beta| * p.H → p.eta < 1 / 100 →
      proposition51Energy p ≤ Chard *
        (1 / (|p.beta| ^ 2 * p.H ^ 2) *
            proposition51I p.X p.H p.f p.beta p.eta +
          ordinaryError p.X p.H p.f p.beta p.eta))
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    FullUnconditionalMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      hPrimitive
  exact fullUnconditionalMAPEndpoint_of_sourceLeaves
    hSW h27 hAPTail hChard hHard hFarBudget

/-- Most literal current release constructor.  The aligned Perron tail is no
longer packaged: its six source components are exposed as one family-square
estimate, with the principal and imprimitive deterministic reductions supplied
by `APAlignedComponentSource`. -/
theorem fullUnconditionalMAPEndpoint_of_primitive_componentLeaves
    (hPrimitive :
      ∀ A B : ℕ, ∃ C X0 : ℝ,
        0 < C ∧ 2 ≤ X0 ∧
          ∀ X : ℝ, X0 ≤ X →
          ∀ q : ℕ, 1 ≤ q →
            (q : ℝ) ≤ (Real.log X) ^ B →
          ∀ chi : DirichletCharacter ℂ q, chi.IsPrimitive →
          ∀ t : ℝ, t ∈ Set.Icc X (2 * X) →
            ‖APFoundation.twistedMangoldtSum chi (Finset.Icc 1 ⌊t⌋₊) -
                MAPSiegelWalfiszCharacterReduction.characterMain chi t‖ ≤
              C * X / (Real.log X) ^ A)
    (h27 : APWeightedZeroMassLogSaving)
    (hComponents : AlignedComponentFamilySquare)
    {Chard : ℝ}
    (hChard : 0 < Chard)
    (hHard : ∀ (p : Proposition51Input),
      Proposition51Admissible 1 1 p →
      1 < |p.beta| * p.H → p.eta < 1 / 100 →
      proposition51Energy p ≤ Chard *
        (1 / (|p.beta| ^ 2 * p.H ^ 2) *
            proposition51I p.X p.H p.f p.beta p.eta +
          ordinaryError p.X p.H p.f p.beta p.eta))
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    FullUnconditionalMAPEndpoint := by
  exact fullUnconditionalMAPEndpoint_of_primitive_sourceLeaves
    hPrimitive h27
    (alignedTailFamilySquare_of_componentFamilySquare hComponents)
    hChard hHard hFarBudget

end
end MAPEndpointSourceWeld

#print axioms MAPEndpointSourceWeld.fullUnconditionalMAPEndpoint_of_sourceLeaves
#print axioms MAPEndpointSourceWeld.fullUnconditionalMAPEndpoint_of_primitive_sourceLeaves
#print axioms MAPEndpointSourceWeld.fullUnconditionalMAPEndpoint_of_primitive_componentLeaves
