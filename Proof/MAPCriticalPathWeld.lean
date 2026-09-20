import MAPFinalSelectableWeld
import AllCenterApertureTransfer
import AllCenterNearFarTransfer
import MajorArcIntegratedPowerWeld

/-!
# Current exact MAP critical path

This file composes the newly certified one-aperture-to-all-aperture transfer
with the already certified major-arc, boundary, variance, Q4, and density-one
weld.  It makes the remaining analytic obligations smaller and literal:

* the uniform twisted-Mangoldt estimate feeding Siegel--Walfisz; and
* the base-aperture near/far estimate supplied by Proposition 2.2 plus the
  Gallagher--MRT argument.

Neither obligation is asserted here.
-/

namespace MAPCriticalPathWeld

open PrimePairEndpoints
open MAPSiegelWalfiszCharacterReduction
open MAPAllCenterApertureTransfer
open MAPAllCenterNearFarTransfer

/-- Energy-facing form of the critical path.  This is strictly weaker than
the pointwise `UniformTwistedMangoldtPsi` route: it accepts exactly the
prime-polynomial-to-continuous-model square energy consumed by the already
certified deterministic major-arc connector. -/
theorem certifiedMAPEndpoint_of_primePolynomialModel_baseAperture
    (hPrime :
      MAPModelOverlapEnergy.SelectablePrimePolynomialModelErrorEnergyFamily)
    (hbase : BaseApertureAllCenterEstimate) :
    CertifiedMAPEndpoint := by
  exact AllCenterEndpointPublicWeld.certifiedMAPEndpoint_of_allCenterLocalMAP
    (MAPFinalSelectableWeld.selectableDeterministicRemainderFamily_of_primePolynomialModel
      hPrime)
    (allCenterLocalMAP_of_baseAperture hbase)

/-- Public conjunction returned by the same energy-facing route. -/
theorem fullUnconditionalMAPEndpoint_of_primePolynomialModel_baseAperture
    (hPrime :
      MAPModelOverlapEnergy.SelectablePrimePolynomialModelErrorEnergyFamily)
    (hbase : BaseApertureAllCenterEstimate) :
    FullUnconditionalMAPEndpoint := by
  exact PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_primePolynomialModel_baseAperture hPrime hbase)

/-- Near/far specialization of the energy-facing route.  A future
AP/Gallagher `L²` connector can target `hPrime` directly and thereby avoid the
separate pointwise Siegel--Walfisz/Abel spine. -/
theorem certifiedMAPEndpoint_of_primePolynomialModel_nearFar
    (hPrime :
      MAPModelOverlapEnergy.SelectablePrimePolynomialModelErrorEnergyFamily)
    (hNF : CanonicalNearFarEstimates) :
    CertifiedMAPEndpoint := by
  exact certifiedMAPEndpoint_of_primePolynomialModel_baseAperture hPrime
    (canonicalScaleLocalMAP_of_nearFarEstimates hNF)

/-- Public conjunction returned by the energy-facing near/far route. -/
theorem fullUnconditionalMAPEndpoint_of_primePolynomialModel_nearFar
    (hPrime :
      MAPModelOverlapEnergy.SelectablePrimePolynomialModelErrorEnergyFamily)
    (hNF : CanonicalNearFarEstimates) :
    FullUnconditionalMAPEndpoint := by
  exact PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_primePolynomialModel_nearFar hPrime hNF)

/-- Shortest shared-input route: an integrated square-power discrepancy on
the paper rational arcs, together with the same near/far estimates used for
the minor arcs, gives the certified endpoint.  This route does not require
pointwise `UniformTwistedMangoldtPsi`. -/
theorem certifiedMAPEndpoint_of_integratedMajorPower_nearFar
    (hIntegrated :
      MAPMajorArcIntegratedPowerWeld.SelectableIntegratedMajorPowerVariationFamily)
    (hNF : CanonicalNearFarEstimates) :
    CertifiedMAPEndpoint := by
  exact certifiedMAPEndpoint_of_primePolynomialModel_nearFar
    (MAPMajorArcIntegratedPowerWeld.selectablePrimePolynomialModelErrorEnergy_of_integratedPower
      hIntegrated) hNF

/-- Public conjunction from the shared integrated-power route. -/
theorem fullUnconditionalMAPEndpoint_of_integratedMajorPower_nearFar
    (hIntegrated :
      MAPMajorArcIntegratedPowerWeld.SelectableIntegratedMajorPowerVariationFamily)
    (hNF : CanonicalNearFarEstimates) :
    FullUnconditionalMAPEndpoint := by
  exact PrimePairEndpoints.certifiedMAPEndpoint_implies_fullUnconditionalMAPEndpoint
    (certifiedMAPEndpoint_of_integratedMajorPower_nearFar hIntegrated hNF)

/-- The current shortest honest route to the certified MAP endpoint. -/
theorem certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_baseAperture
    (hSW : UniformTwistedMangoldtPsi)
    (hbase : BaseApertureAllCenterEstimate) :
    CertifiedMAPEndpoint := by
  exact
    MAPFinalSelectableWeld.certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
      hSW (allCenterLocalMAP_of_baseAperture hbase)

/-- The same critical path, returning the literal public conjunction in
`FullMAP.lean`. -/
theorem fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_baseAperture
    (hSW : UniformTwistedMangoldtPsi)
    (hbase : BaseApertureAllCenterEstimate) :
    FullUnconditionalMAPEndpoint := by
  exact
    MAPFinalSelectableWeld.fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
      hSW (allCenterLocalMAP_of_baseAperture hbase)

/-- The literal near/far route to the certified endpoint.  Its second premise
contains exactly the two analytic branch conclusions (3.2) and (3.3)--(3.7),
with one common set of cutoffs. -/
theorem certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_nearFar
    (hSW : UniformTwistedMangoldtPsi)
    (hNF : CanonicalNearFarEstimates) :
    CertifiedMAPEndpoint := by
  exact
    MAPFinalSelectableWeld.certifiedMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
      hSW (allCenterLocalMAP_of_nearFarEstimates hNF)

/-- Public conjunction returned by the same literal near/far route. -/
theorem fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_nearFar
    (hSW : UniformTwistedMangoldtPsi)
    (hNF : CanonicalNearFarEstimates) :
    FullUnconditionalMAPEndpoint := by
  exact
    MAPFinalSelectableWeld.fullUnconditionalMAPEndpoint_of_uniformTwistedMangoldtPsi_allCenterLocalMAP
      hSW (allCenterLocalMAP_of_nearFarEstimates hNF)

end MAPCriticalPathWeld
