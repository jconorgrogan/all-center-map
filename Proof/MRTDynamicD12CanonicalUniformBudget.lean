import MRTDynamicD12GlobalScalarBridgeV3
import MRTDynamicD12CanonicalProducer
import MRTProposition61D12OnlyUniformCertificateV3

/-!
# Canonical D12 normalized-budget integration

The canonical producer supplies the exact eventual per-bag contract consumed by
the global scalar bridge.  This file exposes the resulting unconditional D12
budget and its direct active-packet consumer; it makes no claim about the
remaining packet fields or the final MAP endpoint.
-/

namespace MRTDynamicD12CanonicalUniformBudget

open MRTDynamicD12GlobalScalarBridgeV3
open MRTDynamicD12CanonicalProducer
open MRTProposition61D12OnlyUniformCertificateV3
open MRTProposition61HighCertificateBridgeV3

noncomputable section

set_option maxHeartbeats 2000000

theorem uniform_d12_normalized_budget_of_canonical_producer :
    ∀ (delta : ℝ) (hdelta : 0 < delta), delta ≤ 1 / 240 →
      UniformD12NormalizedBudget delta hdelta := by
  intro delta hdelta hdeltaUpper
  refine uniformD12NormalizedBudget_of_canonical_perbag ?_ delta hdelta hdeltaUpper
  intro d epsilon hd he hdu
  exact exists_d12_canonical_perbag d epsilon hd hdu he

/-- The verified D12 budget can be inserted into the existing active-packet
bridge.  This theorem leaves the other certificate slots explicit through the
bridge type and does not promote the result to a final MAP endpoint. -/
theorem uniform_active_packet_bridge_of_canonical_producer :
    MRTProposition61HighCertificateBridgeV3.UniformActivePacketCertificateBridge := by
  apply uniform_active_bridge_of_d12_only
  intro delta hdelta hdeltaUpper
  exact uniform_d12_normalized_budget_of_canonical_producer delta hdelta hdeltaUpper

end
end MRTDynamicD12CanonicalUniformBudget

#print axioms MRTDynamicD12CanonicalUniformBudget.uniform_d12_normalized_budget_of_canonical_producer
#print axioms MRTDynamicD12CanonicalUniformBudget.uniform_active_packet_bridge_of_canonical_producer
