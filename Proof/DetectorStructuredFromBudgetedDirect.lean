import CGLDetectorStructuredLargeValue
import CGLPoweredToUniformDensity

/-!
# Direct budgeted-powered to detector-structured adapter

The provenance-sensitive detector conclusion needs only the corrected
budgeted powered large-value bridge.  This direct proof avoids routing through
the stronger uniform theorem and is the compiled numerical core of the live
principal specialization.
-/

namespace MAPDetectorStructuredFromBudgetedDirect

open CGLProofDAG
open CGLDetectorStructuredLargeValue

noncomputable section

theorem detectorStructuredThirtyThirteen_of_budgetedBridge
    (hbridge : BudgetedFixedCharacterPoweredLargeValueBridge) :
    DetectorStructuredThirtyThirteenLargeValue := by
  intro kappa eta hkappa heta
  obtain ⟨C, T₀, hC, hT₀, hbound⟩ :=
    hbridge kappa (eta / 2) hkappa (half_pos heta)
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro T sigma D b W hT hsigmaLow hsigmaHigh hDlow hDhigh hb hsep
    hheight hlarge q _inst chi U Ncut Y scale _hprovenance
  have hraw :=
    hbound T sigma D b W hT hsigmaLow hsigmaHigh hDlow hDhigh hb hsep
      hheight hlarge
  have hTone : 1 ≤ T := (by norm_num : (1 : ℝ) ≤ 2).trans (hT₀.trans hT)
  have hexp :=
    CGLPoweredToUniformDensity.budgeted_powered_exponent_add_half_loss_le_uniform
      hsigmaLow hsigmaHigh heta
  exact hraw.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hTone (by
      simpa [MAPGuthMaynard.densityCoeff] using hexp))
    hC.le)

end

end MAPDetectorStructuredFromBudgetedDirect

#print axioms MAPDetectorStructuredFromBudgetedDirect.detectorStructuredThirtyThirteen_of_budgetedBridge
