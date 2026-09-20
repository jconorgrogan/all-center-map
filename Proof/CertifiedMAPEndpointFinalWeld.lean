import MAPVarianceTransferCutoffWeld
import SingularSeriesSquareMean

/-!
# Final cutoff-faithful MAP endpoint weld

This file discharges the translated singular-series square-mean premise in the
variance/Q4 endpoint assembly.  The only remaining hypotheses are the actual
all-center local-MAP family and the manuscript-faithful selectable deterministic
remainder family.  It does not assert that either remaining family is inhabited.
-/

namespace CertifiedMAPEndpointFinalWeld

open PrimePairEndpoints MAPHarmonicEndpoint
open MAPVarianceTransferWeld

noncomputable section

/-- The public two-sided Q4 family from precisely the two remaining analytic
inputs: all-center local MAP and a selectable-cutoff deterministic remainder
estimate.  The translated singular-square input is unconditional. -/
theorem q4TwoSidedFamily_of_localMAP_selectableRemainder
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                deterministicRemainderEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    Q4TwoSidedFamily := by
  have hVariance :=
    MAPVarianceTransferCutoffWeld.varianceFamily_of_allCenterLocalMAP_and_selectable_remainder
      hMAP hRemainder
  exact q4TwoSidedFamily_of_variance_and_singularSquare hVariance
    SingularSeriesSquareMean.translated_singularSquare_input

/-- Final all-center cutoff-faithful endpoint.  The exact zero-shift deletion,
translated ceiling/floor window, and parameter order are inherited from the
kernel-checked variance and singular-square modules. -/
theorem certifiedMAPEndpoint_of_localMAP_selectableRemainder
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B₀ D₀ : ℕ,
          ∃ B D : ℕ, B₀ ≤ B ∧ D₀ ≤ D ∧
            ∃ C X₀ : ℝ, 0 < C ∧ 2 ≤ X₀ ∧
              ∀ X H h₀ : ℝ, X₀ ≤ X →
                LegalParameters ε X H h₀ →
                deterministicRemainderEnergy X H h₀ B D ≤
                  C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    CertifiedMAPEndpoint := by
  exact
    MAPVarianceTransferCutoffWeld.certifiedMAPEndpoint_of_localMAP_selectableRemainder_singularSquare
      hMAP hRemainder SingularSeriesSquareMean.translated_singularSquare_input

/-- Stronger uniform-cutoff variant, retained as a compatibility adapter for
the original variance-transfer surface.  The selectable theorem above is the
manuscript-faithful public endpoint. -/
theorem certifiedMAPEndpoint_of_localMAP_uniformRemainder
    (hMAP : AllCenterLocalMAP)
    (hRemainder :
      ∀ A ε : ℝ, 0 < A → 0 < ε →
        ∀ B D : ℕ, ∃ C X₀ : ℝ,
          0 < C ∧ 2 ≤ X₀ ∧
          ∀ X H h₀ : ℝ, X₀ ≤ X →
            LegalParameters ε X H h₀ →
            deterministicRemainderEnergy X H h₀ B D ≤
              C * H * X ^ 2 * Real.rpow (Real.log X) (-A)) :
    CertifiedMAPEndpoint := by
  exact
    MAPVarianceTransferWeld.certifiedMAPEndpoint_of_localMAP_uniformRemainder_singularSquare
      hMAP hRemainder SingularSeriesSquareMean.translated_singularSquare_input

end

end CertifiedMAPEndpointFinalWeld
