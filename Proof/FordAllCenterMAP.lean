import FordPrimitiveRegularHighSaving
import GuthMaynardActualEndpointWeakTheta
import MAPSourceFacingCertifiedEndpointAlignmentWeld

noncomputable section
namespace FordAllCenterMAP

/-- The complete four-component endpoint with all analytic sources supplied. -/
theorem certifiedMAPEndpoint : PrimePairEndpoints.CertifiedMAPEndpoint := by
  apply GuthMaynardActualEndpointWeakTheta.certifiedMAPEndpoint_of_anyFixedTheta
  exact ⟨19 / 20, by norm_num,
    FordPrimitiveRegularHighSaving.primitiveRegularHighSavingAt_nineteen_twentieths⟩

/-- All Fourier centers share cutoffs and constants chosen before X and H. -/
theorem allCenterLocalMAP : PrimePairEndpoints.AllCenterLocalMAP :=
  certifiedMAPEndpoint.1

/-- The manuscript-facing statement has positive fixed major-arc cutoffs. -/
theorem positiveCutoffAllCenterLocalMAP :
    MAPSourceFacingCertifiedEndpointAlignmentWeld.PositiveCutoffAllCenterLocalMAP :=
  MAPSourceFacingCertifiedEndpointAlignmentWeld.positiveCutoffAllCenterLocalMAP_of_certifiedMAPEndpoint
    certifiedMAPEndpoint

end FordAllCenterMAP
#print axioms FordAllCenterMAP.certifiedMAPEndpoint
#print axioms FordAllCenterMAP.allCenterLocalMAP
#print axioms FordAllCenterMAP.positiveCutoffAllCenterLocalMAP
