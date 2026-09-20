import MRTProposition61TypeIIActualCellLedgerV3
import MRTProposition61TypeIIEndpointLedgerV3

/-! # Actual Type-II cell with the outer-collar saving exposed -/

namespace MRTProposition61TypeIIActualEndpointLedgerV3

open MAPMRTCorollary25 MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3 MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215OpenIntervalCutoffV3
open MRTProposition61TypeIIActualCellLedgerV3
open MRTProposition61TypeIIEndpointWidthV3
open MRTProposition61TypeIIEndpointLedgerV3

noncomputable section

/-- Equation (3.5) for the actual long length
`(b-a)+2*T+2*U`, after retaining the exact MRT collar width. -/
theorem actualTypeIICell_normalized_product_le_endpoint_terms
    {X H beta eta delta H₀ q T : ℝ} {K k : ℕ}
    (hX : 0 < X) (hH : 0 < H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hq : 1 ≤ q) (hU : 0 < stationaryWidth beta H)
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
              (Real.rpow X delta))) suffixCell)) ≠ 0)
    (component : OuterComponent) :
    let left := typeIIPrefixFactorList
      (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta))
    let N : ℝ := (2 ^ (leftCell : ℕ) : ℕ)
    let M : ℝ := (2 ^ (suffixCell : ℕ) : ℕ)
    let U := stationaryWidth beta H
    let L := (componentEndpoints X beta eta component).2 -
      (componentEndpoints X beta eta component).1
    ((q * (2 * U) + 8 * Real.pi * N) *
        (q * (L + 2 * T + 2 * U) + 8 * Real.pi * M)) /
        (q * U * X) ≤
      2 * q * U / (eta * H) + 4 * q * T / X + 4 * q * U / X +
        64 * Real.pi / Real.rpow X delta +
        16 * Real.pi * (2 : ℝ) ^ left.length * H₀ / (eta * H) +
        32 * Real.pi * (2 : ℝ) ^ left.length * H₀ * T / (U * X) +
        32 * Real.pi * (2 : ℝ) ^ left.length * H₀ / X +
        128 * Real.pi ^ 2 / U := by
  dsimp only
  let left := typeIIPrefixFactorList
    (sortedComponentFactorList logIndex zbag mbag)
    (largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta))
  let U := stationaryWidth beta H
  let L := (componentEndpoints X beta eta component).2 -
    (componentEndpoints X beta eta component).1
  have hL : L ≤ U * X / (eta * H) := by
    dsimp [L, U]
    exact componentEndpoints_sub_le_stationaryWidth_mul
      hX.le heta.le hH component
  have hL0 : 0 ≤ L := by
    dsimp [L]
    rw [componentEndpoints_sub_eq_outerUpper_sub_outerLower]
    unfold outerUpper outerLower
    have hlower : eta * |beta| * X ≤ |beta| * X / eta := by
      have he2 : eta ^ 2 ≤ 1 := by nlinarith
      apply (le_div_iff₀ heta).2
      have hA : 0 ≤ |beta| * X := mul_nonneg (abs_nonneg beta) hX.le
      calc
        eta * |beta| * X * eta = eta ^ 2 * (|beta| * X) := by ring
        _ ≤ 1 * (|beta| * X) := mul_le_mul_of_nonneg_right he2 hA
        _ = |beta| * X := by ring
    linarith
  have hV0 : 0 ≤ L + 2 * T + 2 * U := by
    dsimp [U] at hU ⊢
    positivity
  have hraw := actualTypeIICell_normalized_product_le_four_terms
    hX hq hU hV0 hH₀ logIndex zbag mbag houtcome
    leftCell suffixCell hnonzero
  have hlong := normalized_long_length_terms_le
    (X := X) (eta := eta) (H := H) (U := U) (L := L) (T := T)
    (q := q) (G := (2 : ℝ) ^ left.length) (H₀ := H₀)
    hX heta hH hU hL0 hT (by linarith [hq])
    (by positivity : 0 ≤ (2 : ℝ) ^ left.length) hH₀ hL
  dsimp [left, U, L] at hraw hlong ⊢
  linarith

end
end MRTProposition61TypeIIActualEndpointLedgerV3

#print axioms MRTProposition61TypeIIActualEndpointLedgerV3.actualTypeIICell_normalized_product_le_endpoint_terms
