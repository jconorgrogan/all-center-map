import MAPLambdaEndpointSourceWeld
import PrimitiveTwistedMangoldtCertified

/-!
# Source-facing certified MAP endpoint alignment weld

`MAPLambdaEndpointSourceWeld` exposes the narrow MAP-specific source surface,
but its public theorem lands in the older `FullUnconditionalMAPEndpoint`, whose
Q4 component is only one-sided.  This module proves the deterministic statement
adapter to the manuscript-faithful `CertifiedMAPEndpoint` without changing or
asserting any analytic source input.
-/

namespace MAPSourceFacingCertifiedEndpointAlignmentWeld

open PrimePairEndpoints
open MAPAllCenterNearFarTransfer MAPNearCollarGallagher
open MAPMRTCorollary53Source MAPFarSourceWeldScaffold
open MAPSubmissionRouteOptimizer
open MAPFixedScaleAPZeroRoute MAPAPAlignedTailToRemainderTransfer
open MAPAPAlignedShortIntervalConnector
open MAPAPDirectAlignedTailClosure MAPAPDirectAlignedShortInterval

noncomputable section

/-- The manuscript's local-MAP quantifier surface, including its requirement
that both logarithmic cutoff exponents are positive integers.  The legacy
`AllCenterLocalMAP` definition uses natural-number exponents without recording
that positivity. -/
def PositiveCutoffAllCenterLocalMAP : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∃ B D : ℕ, 1 ≤ B ∧ 1 ≤ D ∧
      ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
        ∀ X H : ℝ, X₀ ≤ X →
          Real.rpow X (2 / 15 + ε) ≤ H →
          ∀ center : UnitAddCircle,
            (∫ α in centeredArc H center ∩ minorArcs X B D,
                ‖primeExponentialSum X α‖ ^ 2
                  ∂AddCircle.haarAddCircle) ≤
              C * X * Real.rpow (Real.log X) (-A)

/-- Positivity of the manuscript cutoffs is a deterministic strengthening of
the legacy public statement: enlarge both cutoffs to at least one and raise the
scale threshold so minor-arc monotonicity applies. -/
theorem positiveCutoffAllCenterLocalMAP_of_allCenterLocalMAP
    (hMAP : AllCenterLocalMAP) : PositiveCutoffAllCenterLocalMAP := by
  intro A ε hA hε
  obtain ⟨B, D, C, X₀, hC, hX₀, hbound⟩ := hMAP A ε hA hε
  let B' := max B 1
  let D' := max D 1
  let X₀' := max X₀ (Real.exp 1)
  have hBpos : 1 ≤ B' := le_max_right _ _
  have hDpos : 1 ≤ D' := le_max_right _ _
  have hX₀'two : 2 ≤ X₀' := hX₀.trans (le_max_left _ _)
  refine ⟨B', D', hBpos, hDpos, C, X₀', hC, hX₀'two, ?_⟩
  intro X H hXX₀' hH center
  have hXX₀ : X₀ ≤ X := (le_max_left X₀ (Real.exp 1)).trans hXX₀'
  have hXexp : Real.exp 1 ≤ X :=
    (le_max_right X₀ (Real.exp 1)).trans hXX₀'
  have hXpos : 0 < X := (Real.exp_pos 1).trans_le hXexp
  have hlog : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hXexp
  have hold := hbound X H hXX₀ hH center
  rw [← FejerMAPInterfaceWeld.integral_minorWeight_centeredArc] at hold ⊢
  exact
    (FejerMAPInterfaceWeld.integral_minorWeight_anti_cutoffs hXpos hlog
      (le_max_left B 1) (le_max_left D 1) center).trans hold

/-- Forgetting cutoff positivity recovers the legacy public local-MAP surface. -/
theorem allCenterLocalMAP_of_positiveCutoffAllCenterLocalMAP
    (hMAP : PositiveCutoffAllCenterLocalMAP) : AllCenterLocalMAP := by
  intro A ε hA hε
  obtain ⟨B, D, _hB, _hD, C, X₀, hC, hX₀, hbound⟩ := hMAP A ε hA hε
  exact ⟨B, D, C, X₀, hC, hX₀, hbound⟩

/-- Exact equivalence between the legacy and positive-cutoff local-MAP
surfaces. -/
theorem positiveCutoffAllCenterLocalMAP_iff_allCenterLocalMAP :
    PositiveCutoffAllCenterLocalMAP ↔ AllCenterLocalMAP := by
  exact ⟨allCenterLocalMAP_of_positiveCutoffAllCenterLocalMAP,
    positiveCutoffAllCenterLocalMAP_of_allCenterLocalMAP⟩

/-- The manuscript-faithful certified endpoint projects deterministically to
the exact positive-cutoff local-MAP surface consumed by the Palomar release
candidate. -/
theorem positiveCutoffAllCenterLocalMAP_of_certifiedMAPEndpoint
    (hEndpoint : CertifiedMAPEndpoint) : PositiveCutoffAllCenterLocalMAP :=
  positiveCutoffAllCenterLocalMAP_of_allCenterLocalMAP hEndpoint.1

/-- The MAP-specific hard-range route lands directly in the manuscript-faithful
four-component endpoint.  The hypotheses are exactly the four live analytic
families after the deterministic per-rational near-collar theorem has been
discharged. -/
theorem certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
    (hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hAP : APFoundation.SimultaneousShortIntervalAP)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarSource : MAPFarSourceReduction 1 1) :
    CertifiedMAPEndpoint := by
  have hNear : SelectableCanonicalNearCollarEstimate :=
    selectableCanonicalNearCollarEstimate_of_gallagher_ap
      (nearCollarGallagherTransfer_of_perRational
        MAPNearCollarGallagher.perRationalNearCollarTransfer_proved) hAP
  have hFar : CanonicalFarAnnulusEstimate :=
    canonicalFarAnnulusEstimate_of_mapLambda_halfRange_source
      (mapLambdaCorollary53HalfRange_of_hardRange hHard) hFarSource
  exact
    MAPCriticalPathWeld.certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_nearFar
      hSW
      (MAPEndpointIntegrationScaffold.canonicalNearFarEstimates_of_selectableNear_far
        hNear hFar)

/-- Certified counterpart of the current narrow source-facing release wrapper.
It keeps every unresolved analytic source leaf explicit and strengthens only the
deterministic endpoint landing from one-sided Q4+ to the literal two-sided Q4
family. -/
theorem certifiedMAPEndpoint_of_mapLambda_primitive_sourceLeaves
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
    (hAPContour : AlignedLeftHorizontalFamilySquare)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint := by
  have hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi :=
    MAPPsiEndpointImprimitiveAdapters.uniformTwistedMangoldtPsi_of_primitive
      hPrimitive
  have hAP : APFoundation.SimultaneousShortIntervalAP :=
    simultaneousShortIntervalAP_of_weightedZeroMass_of_leftHorizontal
      h27 hAPContour
  have hFar : MAPFarSourceReduction 1 1 :=
    mapFarSourceReduction_one_of_uniformLiteralPaddedFarBudget hFarBudget
  exact certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves hSW hAP hHard hFar

/-- Source-facing endpoint after the primitive twisted-Mangoldt binder has
been discharged internally.  Only the AP zero-mass/contour pair and the
hard/far MAP leaves remain. -/
theorem certifiedMAPEndpoint_of_mapLambda_sourceLeaves
    (h27 : APWeightedZeroMassLogSaving)
    (hAPContour : AlignedLeftHorizontalFamilySquare)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarBudget : UniformLiteralPaddedFarBudget) :
    CertifiedMAPEndpoint :=
  certifiedMAPEndpoint_of_mapLambda_primitive_sourceLeaves
    MAPPrimitiveTwistedMangoldtCertified.primitiveTwistedMangoldtPsi
    h27 hAPContour hHard hFarBudget

end
end MAPSourceFacingCertifiedEndpointAlignmentWeld

#print axioms MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambdaHard_activeLeaves
#print axioms MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambda_primitive_sourceLeaves
#print axioms MAPSourceFacingCertifiedEndpointAlignmentWeld.certifiedMAPEndpoint_of_mapLambda_sourceLeaves
#print axioms MAPSourceFacingCertifiedEndpointAlignmentWeld.positiveCutoffAllCenterLocalMAP_iff_allCenterLocalMAP
#print axioms MAPSourceFacingCertifiedEndpointAlignmentWeld.positiveCutoffAllCenterLocalMAP_of_certifiedMAPEndpoint
