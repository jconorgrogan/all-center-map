import MRTProposition61TypeIINormalizedLedgerV3
import MRTLemma215DynamicTypeIICellPruningV3

/-! # Equation-(3.5) specialization for one nonzero actual Type-II cell -/

namespace MRTProposition61TypeIIActualCellLedgerV3

open MAPMRTCorollary25 MAPMRTCorollary25TypeD1LiteralWeld MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3 MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIICellPruningV3 MRTLemma215OpenIntervalCutoffV3
open MRTProposition61TypeIINormalizedLedgerV3

noncomputable section

/-- Literal equation (3.5) after inserting the three certified active-cell
scale inequalities. The prefix dilation remains explicit for the later fixed
`2^(2K)` envelope. -/
theorem actualTypeIICell_normalized_product_le_four_terms
    {X delta H₀ q U T : ℝ} {K k : ℕ}
    (hX : 0 < X) (hq : 1 ≤ q) (hU : 0 < U)
    (hT : 0 ≤ T) (hH₀ : 0 ≤ H₀)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIIPrefixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow X delta))))))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct
      (typeIISuffixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow X delta))))))
    (hnonzero : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow X delta))) leftCell)
        (factorListDyadicCell
          (typeIISuffixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow X delta))) suffixCell)) ≠ 0) :
    let left := typeIIPrefixFactorList
      (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta))
    let N : ℝ := (2 ^ (leftCell : ℕ) : ℕ)
    let M : ℝ := (2 ^ (suffixCell : ℕ) : ℕ)
    ((q * (2 * U) + 8 * Real.pi * N) *
        (q * T + 8 * Real.pi * M)) / (q * U * X) ≤
      2 * q * T / X + 64 * Real.pi / Real.rpow X delta +
        16 * Real.pi * (2 : ℝ) ^ left.length * H₀ * T / (U * X) +
        128 * Real.pi ^ 2 / U := by
  dsimp only
  let left := typeIIPrefixFactorList
    (sortedComponentFactorList logIndex zbag mbag)
    (largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta)
    )
  let suffix := typeIISuffixFactorList
    (sortedComponentFactorList logIndex zbag mbag)
    (largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta)
    )
  let N : ℝ := (2 ^ (leftCell : ℕ) : ℕ)
  let M : ℝ := (2 ^ (suffixCell : ℕ) : ℕ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hD : 0 < Real.rpow X delta := Real.rpow_pos_of_pos hX _
  have hlower := actualTypeIICell_leftScale_gt_half_rpow
    logIndex zbag mbag houtcome leftCell suffixCell hnonzero
  have hupper := actualTypeIICell_leftScale_lt_upper
    logIndex zbag mbag houtcome leftCell
  have hsupports := nonzero_intervalCutoff_literalConvolution_product_bounds
    hX.le
    (scaledTypeIIPrefixCell_supported zbag mbag left leftCell)
    (factorListDyadicCell_supported suffix suffixCell) hnonzero
  have hraw := normalized_typeII_product_le_four_terms
    hq hU hX hD hN hM hT (by positivity : 0 ≤ 8 * Real.pi)
    (by positivity : 0 ≤ (2 : ℝ) ^ left.length) (by positivity : 0 ≤ 2 * H₀)
    (show Real.rpow X delta ≤ 2 * N by simpa [N] using hlower.le)
    (show N ≤ (2 : ℝ) ^ left.length * (2 * H₀) by
      simpa [N, left] using hupper.le)
    (show N * M ≤ 2 * X by simpa [N, M, left, suffix] using hsupports.2)
  dsimp [N, M, left, suffix] at hraw ⊢
  convert hraw using 1 <;> ring

end
end MRTProposition61TypeIIActualCellLedgerV3

#print axioms MRTProposition61TypeIIActualCellLedgerV3.actualTypeIICell_normalized_product_le_four_terms
