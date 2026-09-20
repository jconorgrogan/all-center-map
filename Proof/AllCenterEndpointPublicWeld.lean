import CertifiedMAPEndpointFinalWeld

/-!
# Minimal public all-center endpoint weld

The translated singular-series square mean, Fejer transfer, cutoff
synchronization, variance-to-Q4 conversion, and density-one implication are
already proved in the imported MAP tree.  This file gives the remaining
deterministic major/support estimate a name and packages the endpoint as an
equivalence with `AllCenterLocalMAP` once that estimate is available.
-/

namespace AllCenterEndpointPublicWeld

open PrimePairEndpoints MAPVarianceTransferWeld

noncomputable section

/-- The exact selectable-cutoff deterministic major/support remainder family.
The order of quantifiers is manuscript-faithful: the cutoffs may be enlarged
after the requested saving and lower cutoff bounds are fixed, but are then
uniform in the scale, radius, and real center. -/
def SelectableDeterministicRemainderFamily : Prop :=
  ∀ A ε : ℝ, 0 < A → 0 < ε →
    ∀ B₀ D₀ : ℕ,
      ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
        ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            deterministicRemainderEnergy X H h₀ B D ≤
              C * H * X ^ 2 * Real.rpow (Real.log X) (-A)

/-- With the exact deterministic remainder family supplied, the corrected
four-component endpoint has precisely the same logical content as the
all-center local MAP theorem.  Every other downstream obligation is discharged
by the imported kernel-checked transfer and singular-square theorems. -/
theorem certifiedMAPEndpoint_iff_allCenterLocalMAP
    (hRemainder : SelectableDeterministicRemainderFamily) :
    CertifiedMAPEndpoint ↔ AllCenterLocalMAP := by
  constructor
  · intro hEndpoint
    exact hEndpoint.1
  · intro hMAP
    exact
      CertifiedMAPEndpointFinalWeld.certifiedMAPEndpoint_of_localMAP_selectableRemainder
        hMAP hRemainder

/-- Direct implication form for callers that already have the all-center MAP
proof term. -/
theorem certifiedMAPEndpoint_of_allCenterLocalMAP
    (hRemainder : SelectableDeterministicRemainderFamily)
    (hMAP : AllCenterLocalMAP) :
    CertifiedMAPEndpoint :=
  (certifiedMAPEndpoint_iff_allCenterLocalMAP hRemainder).2 hMAP

end

end AllCenterEndpointPublicWeld
