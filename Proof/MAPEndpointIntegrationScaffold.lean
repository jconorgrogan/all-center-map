import MAPCriticalPathWeld
import NearCollarGallagherFiniteUnion
import MRTProposition51Supported
import GallagherPowerVariation
import PerRationalNearCollarDeterministic

/-!
# Conditional integration scaffold for the reliable MAP endpoint

This file adds no analytic proposition or axiom.  It contains only deterministic
transport and staging theorems whose parameters are existing source interfaces.
-/

namespace MAPEndpointIntegrationScaffold

open MeasureTheory Set
open PrimePairEndpoints MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer
open MAPNearCollarGallagher MAPMRTCorollary53Source MAPMRTProposition51Source
open MAPMRTProposition51Supported
open MAPMajorArcWeld

noncomputable section

/-- Increasing the logarithmic denominator exponent enlarges the inner collar.
This is the deterministic transport needed to synchronize an existential far
cutoff with the cutoff-selectable near theorem. -/
theorem innerRationalCollars_mono_denominatorExponent
    {epsilon X : ℝ} {B₁ B₂ Cc : ℕ}
    (hlog : 1 ≤ Real.log X) (hB : B₁ ≤ B₂) :
    innerRationalCollars epsilon X B₁ Cc ⊆
      innerRationalCollars epsilon X B₂ Cc := by
  intro center hcenter
  rcases hcenter with ⟨q, a, hq, hqcap, ha, hacop, hdist⟩
  exact ⟨q, a, hq, hqcap.trans (pow_le_pow_right₀ hlog hB),
    ha, hacop, hdist⟩

/-- Synchronize the separately exposed near and far branch conclusions.

The far branch chooses `B` existentially.  We replace it by `max B 1`, use
collar monotonicity for the far mask, choose a fresh (far-irrelevant) `D` large
enough for the selectable near theorem, and retain the far `Cc`. -/
theorem canonicalNearFarEstimates_of_selectableNear_far
    (hNear : SelectableCanonicalNearCollarEstimate)
    (hFar : CanonicalFarAnnulusEstimate) :
    CanonicalNearFarEstimates := by
  intro A epsilon hA hepsilon
  obtain ⟨Bfar, _Dfar, Cc, Cfar, Xfar, hCfar, hXfar, hfar⟩ :=
    hFar A epsilon hA hepsilon
  let B : ℕ := max Bfar 1
  let D : ℕ := ⌈A + 2 * (B : ℝ) + 10⌉₊
  have hBone : 1 ≤ B := by
    dsimp [B]
    omega
  have hBfar : Bfar ≤ B := by
    dsimp [B]
    exact le_max_left _ _
  have hD : A + 2 * (B : ℝ) ≤ (D : ℝ) := by
    dsimp [D]
    exact (by linarith [Nat.le_ceil (A + 2 * (B : ℝ) + 10)])
  obtain ⟨Cnear, Xnear, hCnear, hXnear, hnear⟩ :=
    hNear A epsilon B D Cc hA hepsilon hBone hD
  let C : ℝ := Cnear + Cfar
  let X₀ : ℝ := max Xnear Xfar
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hX₀ : 2 ≤ X₀ := hXnear.trans (le_max_left _ _)
  refine ⟨B, D, Cc, C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀
  have hXXnear : Xnear ≤ X := (le_max_left Xnear Xfar).trans hXX₀
  have hXXfar : Xfar ≤ X := (le_max_right Xnear Xfar).trans hXX₀
  obtain ⟨hlogNear, hnearBound⟩ := hnear X hXXnear
  obtain ⟨hlogFar, hfarBound⟩ := hfar X hXXfar
  have hXnonneg : 0 ≤ X := by linarith
  have htargetNonneg :
      0 ≤ X * Real.rpow (Real.log X) (-A) :=
    mul_nonneg hXnonneg (Real.rpow_nonneg (by linarith) _)
  refine ⟨hlogNear, ?_, ?_⟩
  · exact hnearBound.trans (by
      calc
        Cnear * X * Real.rpow (Real.log X) (-A) =
            Cnear * (X * Real.rpow (Real.log X) (-A)) := by ring
        _ ≤ (Cnear + Cfar) *
            (X * Real.rpow (Real.log X) (-A)) :=
          mul_le_mul_of_nonneg_right (by linarith) htargetNonneg
        _ = C * X * Real.rpow (Real.log X) (-A) := by
          dsimp [C]
          ring)
  · intro center hcenter
    have hnotFar :
        center ∉ innerRationalCollars epsilon X Bfar Cc := by
      intro hsmall
      exact hcenter
        (innerRationalCollars_mono_denominatorExponent hlogFar hBfar hsmall)
    exact (hfarBound center hnotFar).trans (by
      calc
        Cfar * X * Real.rpow (Real.log X) (-A) =
            Cfar * (X * Real.rpow (Real.log X) (-A)) := by ring
        _ ≤ (Cnear + Cfar) *
            (X * Real.rpow (Real.log X) (-A)) :=
          mul_le_mul_of_nonneg_right (by linarith) htargetNonneg
        _ = C * X * Real.rpow (Real.log X) (-A) := by
          dsimp [C]
          ring)

/-- Exact cancellation showing why the currently exposed signed-sliding
endpoint error does not by itself construct the integrated-power family.

After Gallagher's `4/y²` factor and the square-root arc-length factor are
squared together, the endpoint summand
`y² * (Q² * y * log(X)²)` loses every power of the selectable width `D`.
The remaining `Q² log(X)²` grows with the denominator cutoff. -/
theorem endpointSlidingLoss_cancels_arcWidth
    {X : ℝ} (B D : ℕ) (hX : 1 < X) :
    (2 * paperArcRadius X D) *
        (4 / paperGallagherWindow X D ^ 2 *
          (paperGallagherWindow X D ^ 2 *
            (collarQ X B ^ 2 * paperGallagherWindow X D *
              (Real.log X) ^ 2))) =
      collarQ X B ^ 2 * (Real.log X) ^ 2 := by
  have hX0 : X ≠ 0 := ne_of_gt (zero_lt_one.trans hX)
  have hlog0 : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
  unfold paperArcRadius paperGallagherWindow collarQ
  field_simp
  ring

/-- Leaf-level staging theorem for the reliable pointwise-major-arc route.
Every premise is an existing named source interface; all intervening near/far
synchronization and endpoint composition is proved here or in root modules. -/
theorem fullUnconditionalMAPEndpoint_of_uniformTwisted_activeLeaves
    (hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hPerRational : PerRationalNearCollarTransfer)
    (hAP : APFoundation.SimultaneousShortIntervalAP)
    {cBetaEta cEta : ℝ}
    (hP51 : MRTProposition51 cBetaEta cEta)
    (hFarSource : MAPFarSourceReduction cBetaEta cEta) :
    FullUnconditionalMAPEndpoint := by
  have hNear : SelectableCanonicalNearCollarEstimate :=
    selectableCanonicalNearCollarEstimate_of_gallagher_ap
      (nearCollarGallagherTransfer_of_perRational hPerRational) hAP
  have hFar : CanonicalFarAnnulusEstimate :=
    MAPMRTProposition51Supported.canonicalFarAnnulusEstimate_of_proposition51_lemma29_source
      hP51 hFarSource
  exact MAPCriticalPathWeld.fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_nearFar
    hSW (canonicalNearFarEstimates_of_selectableNear_far hNear hFar)

/-- Reliable endpoint after the per-rational near-collar theorem has been
inhabited.  MRT Lemma 2.9 is discharged internally by its support-corrected
proof; the remaining hypotheses are the pointwise major-arc estimate, the
simultaneous AP theorem, Proposition 5.1, and the far source reduction. -/
theorem fullUnconditionalMAPEndpoint_of_remaining_activeLeaves
    (hSW : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hAP : APFoundation.SimultaneousShortIntervalAP)
    {cBetaEta cEta : ℝ}
    (hP51 : MRTProposition51 cBetaEta cEta)
    (hFarSource : MAPFarSourceReduction cBetaEta cEta) :
    FullUnconditionalMAPEndpoint :=
  fullUnconditionalMAPEndpoint_of_uniformTwisted_activeLeaves
    hSW perRationalNearCollarTransfer_proved hAP hP51 hFarSource

end
end MAPEndpointIntegrationScaffold

#print axioms MAPEndpointIntegrationScaffold.innerRationalCollars_mono_denominatorExponent
#print axioms MAPEndpointIntegrationScaffold.canonicalNearFarEstimates_of_selectableNear_far
#print axioms MAPEndpointIntegrationScaffold.endpointSlidingLoss_cancels_arcWidth
#print axioms MAPEndpointIntegrationScaffold.fullUnconditionalMAPEndpoint_of_uniformTwisted_activeLeaves
#print axioms MAPEndpointIntegrationScaffold.fullUnconditionalMAPEndpoint_of_remaining_activeLeaves
