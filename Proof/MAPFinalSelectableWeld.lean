import ModelOverlapEnergy
import MAPFinalDeterministicConnector
import PrimePolynomialEnergyFromPointwise
import SWEnvelopeLogCollapse
import SiegelWalfiszCharacterReduction

/-!
# Final deterministic major-arc remainder weld

The sole input below is the square-energy approximation of the actual prime
polynomial major contribution by its continuous model.  Continuous-kernel
truncation, the exact Ramanujan tail, support boundary, and the
`|h| * singularSeries` overlap correction are all discharged by compiled
theorems.
-/

namespace MAPFinalSelectableWeld

open PrimePairEndpoints

noncomputable section

theorem connector_majorOverlapErrorEnergy_eq_modelOverlapEnergy
    (X H h₀ : ℝ) (B D : ℕ) :
    MAPFinalDeterministicConnector.majorOverlapErrorEnergy X H h₀ B D =
      MAPModelOverlapEnergy.majorOverlapErrorEnergy X H h₀ B D := by
  rfl

/-- Complete deterministic major/support remainder family from the one
source-facing prime-polynomial model-energy input. -/
theorem selectableDeterministicRemainderFamily_of_primePolynomialModel
    (hPrime :
      MAPModelOverlapEnergy.SelectablePrimePolynomialModelErrorEnergyFamily) :
    AllCenterEndpointPublicWeld.SelectableDeterministicRemainderFamily := by
  apply MAPFinalDeterministicConnector.selectableRemainder_of_selectableMajorOverlapError
  intro A ε hA hε B₀ D₀
  obtain ⟨B, D, hB, hD, C, X₀, hC, hX₀, hbound⟩ :=
    MAPModelOverlapEnergy.selectableMajorOverlapEnergy_of_primePolynomialModel
      hPrime A ε hA hε B₀ D₀
  refine ⟨B, D, hB, hD, C, X₀, hC, (by linarith), ?_⟩
  intro X H h₀ hXX₀ hlegal
  rw [connector_majorOverlapErrorEnergy_eq_modelOverlapEnergy]
  exact hbound X H h₀ hXX₀ hlegal

/-- Uniform Siegel--Walfisz is sufficient for every deterministic major-arc,
continuous-kernel, Ramanujan-tail, support-boundary, and overlap remainder in
the all-center endpoint. -/
theorem selectableDeterministicRemainderFamily_of_siegelWalfisz
    (hSW : MAPPointwiseMajorArc.UniformSiegelWalfiszPsi) :
    AllCenterEndpointPublicWeld.SelectableDeterministicRemainderFamily := by
  apply selectableDeterministicRemainderFamily_of_primePolynomialModel
  apply MAPPrimePolynomialEnergyFromPointwise.selectablePrimePolynomialModelErrorEnergy_of_pointwise
  exact SWEnvelopeLogCollapse.uniformPrimePolynomialLogSaving_of_siegelWalfisz hSW

/-- Source-facing form: the uniform twisted Mangoldt estimate is the sole
analytic premise of the deterministic major-arc sector. -/
theorem selectableDeterministicRemainderFamily_of_uniformTwistedMangoldtPsi
    (hTwisted : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi) :
    AllCenterEndpointPublicWeld.SelectableDeterministicRemainderFamily := by
  exact selectableDeterministicRemainderFamily_of_siegelWalfisz
    (MAPSiegelWalfiszCharacterReduction.uniformSiegelWalfiszPsi_of_uniformTwistedMangoldtPsi
      hTwisted)

/-- Once the source-facing twisted Mangoldt theorem is supplied, the exact
all-center endpoint (including the two-sided Q4 and density-one conclusions)
is equivalent to the local all-center MAP statement. -/
theorem certifiedMAPEndpoint_iff_allCenterLocalMAP_of_uniformTwistedMangoldtPsi
    (hTwisted : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi) :
    CertifiedMAPEndpoint ↔ AllCenterLocalMAP := by
  exact AllCenterEndpointPublicWeld.certifiedMAPEndpoint_iff_allCenterLocalMAP
    (selectableDeterministicRemainderFamily_of_uniformTwistedMangoldtPsi hTwisted)

/-- Direct all-center/Q4 endpoint constructor from the two remaining
source-facing analytic inputs. -/
theorem certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
    (hTwisted : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hMAP : AllCenterLocalMAP) :
    CertifiedMAPEndpoint :=
  (certifiedMAPEndpoint_iff_allCenterLocalMAP_of_uniformTwistedMangoldtPsi
    hTwisted).2 hMAP

/-- Compatibility projection to the package's original headline endpoint. -/
theorem fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
    (hTwisted : MAPSiegelWalfiszCharacterReduction.UniformTwistedMangoldtPsi)
    (hMAP : AllCenterLocalMAP) :
    FullUnconditionalMAPEndpoint :=
  PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
      hTwisted hMAP)

end
end MAPFinalSelectableWeld

#print axioms MAPFinalSelectableWeld.selectableDeterministicRemainderFamily_of_primePolynomialModel
#print axioms MAPFinalSelectableWeld.selectableDeterministicRemainderFamily_of_siegelWalfisz
#print axioms MAPFinalSelectableWeld.selectableDeterministicRemainderFamily_of_uniformTwistedMangoldtPsi
#print axioms MAPFinalSelectableWeld.certifiedMAPEndpoint_iff_allCenterLocalMAP_of_uniformTwistedMangoldtPsi
#print axioms MAPFinalSelectableWeld.certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
#print axioms MAPFinalSelectableWeld.fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
