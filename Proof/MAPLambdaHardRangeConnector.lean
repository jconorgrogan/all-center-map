import MAPEndpointIntegrationScaffold
import MRTProposition51FirstAnalytic
import MRTProposition51Constructor

/-!
# MAP-only hard-range connector for the far annulus

The public endpoint uses MRT Proposition 5.1 only after specializing the
coefficient to `mapMangoldtCoeff X` and applying one additive twist.  This
module records that strictly weaker consumer boundary.  It combines the
premise-free easy regime with a MAP-only hard-regime estimate and then feeds
the existing far-source reduction.

No source estimate is asserted here.
-/

namespace MAPSubmissionRouteOptimizer

open PrimePairEndpoints
open MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer MAPNearCollarGallagher
open MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51FirstAnalytic
open MAPMRTProposition51Constructor

noncomputable section

/-- The exact hard-range inequality needed by the MAP far-annulus consumer.
Unlike `MRTProposition51`, it quantifies only the literal MAP Mangoldt input. -/
def MAPLambdaCorollary53HardRange : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (X H beta eta : ℝ) (q a : ℕ),
      let p := mapCorollary53Input X H q a beta eta
      ∀ (hp : Corollary53Admissible 1 1 p),
        H ≤ X / 2 →
        1 < |beta| * H → eta < 1 / 100 →
        sourceEnergy p ≤ C *
          (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
            ordinaryError p.X p.H p.f p.beta p.eta)

/-- MAP-only half-range Corollary 5.3.  This is the largest MRT conclusion
actually consumed after rational-center selection. -/
def MAPLambdaCorollary53HalfRange : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (X H beta eta : ℝ) (q a : ℕ),
      let p := mapCorollary53Input X H q a beta eta
      ∀ (hp : Corollary53Admissible 1 1 p),
        H ≤ X / 2 →
        sourceEnergy p ≤ C *
          (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
            ordinaryError p.X p.H p.f p.beta p.eta)

/-- The compiled easy branch upgrades a MAP-only hard-range proof to the
complete MAP-only half-range estimate. -/
theorem mapLambdaCorollary53HalfRange_of_hardRange
    (hHard : MAPLambdaCorollary53HardRange) :
    MAPLambdaCorollary53HalfRange := by
  obtain ⟨Chard, hChard, hhard⟩ := hHard
  refine ⟨Chard + 2560000, by positivity, ?_⟩
  intro X H beta eta q a
  dsimp only
  intro hp hHalf
  let p := mapCorollary53Input X H q a beta eta
  have hp51 : Proposition51Admissible 1 1
      (MAPMRTProposition51Supported.twistedProposition51Input p) :=
    MAPMRTProposition51Supported.twistedProposition51Input_admissible hp hHalf
  have hmainNonneg :
      0 ≤ stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 := by
    have hI :=
      proposition51I_nonneg_of_admissible hp51
    change 0 ≤ proposition51I p.X p.H
      (additiveTwist p.q p.a p.f) p.beta p.eta at hI
    have hscale : 0 ≤ 1 / (|p.beta| ^ 2 * p.H ^ 2) := by positivity
    exact (mul_nonneg hscale hI).trans
      (MAPMRTProposition51Supported.proposition51_main_le_stationaryMain
        MAPMRTLemma29Proof.mrtLemma29Supported_proof hp)
  have herrorNonneg :
      0 ≤ ordinaryError p.X p.H p.f p.beta p.eta := by
    exact ordinaryError_nonneg
  have hrhsNonneg :
      0 ≤ stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
        ordinaryError p.X p.H p.f p.beta p.eta :=
    add_nonneg hmainNonneg herrorNonneg
  by_cases hcase : 1 < |beta| * H ∧ eta < 1 / 100
  · have hh := hhard X H beta eta q a hp hHalf hcase.1 hcase.2
    exact hh.trans (mul_le_mul_of_nonneg_right
      (by linarith : Chard ≤ Chard + 2560000) hrhsNonneg)
  · have heasy : |beta| * H ≤ 1 ∨ 1 / 100 ≤ eta := by
      rcases not_and_or.mp hcase with hsmall | hetaLarge
      · exact Or.inl (le_of_not_gt hsmall)
      · exact Or.inr (le_of_not_gt hetaLarge)
    have he := proposition51_easy_regime
      p.X p.H p.beta p.eta (additiveTwist p.q p.a p.f)
      (lt_of_lt_of_le zero_lt_one hp51.1)
      hp51.2.2.2.2.2.2.1 hp51.2.2.1.le heasy
    have heSource : sourceEnergy p ≤
        2560000 * ordinaryError p.X p.H p.f p.beta p.eta := by
      rw [← MAPMRTProposition51Supported.proposition51Energy_twisted_eq_sourceEnergy p]
      rw [← MAPMRTProposition51Supported.ordinaryError_additiveTwist
        p.X p.H p.beta p.eta p.q p.a p.f]
      exact he
    exact heSource.trans (by
      have hordinaryLe : ordinaryError p.X p.H p.f p.beta p.eta ≤
          stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hp.2.2.1 +
            ordinaryError p.X p.H p.f p.beta p.eta := by linarith
      nlinarith [mul_nonneg hChard.le hrhsNonneg])

/-- The MAP-only half-range theorem and the existing source reduction imply
the literal far conjunct, without constructing generic `MRTProposition51`. -/
theorem canonicalFarAnnulusEstimate_of_mapLambda_halfRange_source
    (hMRT : MAPLambdaCorollary53HalfRange)
    (hsource : MAPFarSourceReduction 1 1) :
    CanonicalFarAnnulusEstimate := by
  obtain ⟨Cmrt, hCmrt, hcor⟩ := hMRT
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, Cred, X₀, hCred, hX₀, hred⟩ :=
    hsource A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cmrt * Cred, X₀, mul_pos hCmrt hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hfar⟩ := hred X hXX₀
  refine ⟨hlog, ?_⟩
  intro center hcenter
  obtain ⟨q, a, beta, hq, hqQ, ha, hacop, hcenterEq, hbeta,
      hfarWidth, hp, hcircle, hRHS⟩ := hfar center hcenter
  let Q := (Real.log X) ^ B
  let H := baseAperture epsilon X
  let eta := 1 / Real.sqrt Q
  let p := mapCorollary53Input X H q a beta eta
  have hXone : 1 ≤ X := by linarith
  have hHalf : H ≤ X / 2 := by
    exact MAPMRTProposition51Supported.baseAperture_le_half_of_one_le hXone
  have hcorP : sourceEnergy p ≤ Cmrt *
      (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
        ordinaryError p.X p.H p.f p.beta p.eta) :=
    hcor X H beta eta q a hp hHalf
  calc
    (∫ alpha in centeredArc (baseAperture epsilon X) center,
        ‖primeExponentialSum X alpha‖ ^ 2
          ∂AddCircle.haarAddCircle) ≤ sourceEnergy p := hcircle
    _ ≤ Cmrt *
        (stationaryMainTerm p.X p.H p.q p.f p.beta p.eta hq +
          ordinaryError p.X p.H p.f p.beta p.eta) := hcorP
    _ ≤ Cmrt * (Cred * X * Real.rpow (Real.log X) (-A)) :=
      mul_le_mul_of_nonneg_left hRHS hCmrt.le
    _ = (Cmrt * Cred) * X * Real.rpow (Real.log X) (-A) := by ring

/-- Endpoint constructor replacing generic Proposition 5.1 by its exact
MAP-Mangoldt hard-range consumer. -/
theorem fullUnconditionalMAPEndpoint_of_mapLambdaHard_activeLeaves
    (hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hAP : APFoundation.SimultaneousShortIntervalAP)
    (hHard : MAPLambdaCorollary53HardRange)
    (hFarSource : MAPFarSourceReduction 1 1) :
    FullUnconditionalMAPEndpoint := by
  have hNear : SelectableCanonicalNearCollarEstimate :=
    selectableCanonicalNearCollarEstimate_of_gallagher_ap
      (nearCollarGallagherTransfer_of_perRational
        MAPNearCollarGallagher.perRationalNearCollarTransfer_proved) hAP
  have hFar : CanonicalFarAnnulusEstimate :=
    canonicalFarAnnulusEstimate_of_mapLambda_halfRange_source
      (mapLambdaCorollary53HalfRange_of_hardRange hHard) hFarSource
  exact MAPCriticalPathWeld.fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_nearFar
    hSW (MAPEndpointIntegrationScaffold.canonicalNearFarEstimates_of_selectableNear_far
      hNear hFar)

end
end MAPSubmissionRouteOptimizer

#print axioms MAPSubmissionRouteOptimizer.mapLambdaCorollary53HalfRange_of_hardRange
#print axioms MAPSubmissionRouteOptimizer.canonicalFarAnnulusEstimate_of_mapLambda_halfRange_source
#print axioms MAPSubmissionRouteOptimizer.fullUnconditionalMAPEndpoint_of_mapLambdaHard_activeLeaves
