import MRTProposition61TypeIIGlobalCellAggregationV3
import MRTProposition61TypeIIFilteredAggregateBoundV3

/-! # Global filtered Type-II analytic ledger with one uniform constant -/

namespace MRTProposition61TypeIIGlobalFilteredAnalyticV3

open scoped BigOperators
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypesRefinedV3 MAPFinishDynamicThreeTypeTrace
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicSupportV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTProposition61TypeIIComponentTotalV3
open MRTProposition61TypeIIActiveAggregateBoundV3
open MRTProposition61TypeIIGlobalCellAggregationV3
open MRTProposition61TypeIIFilteredAggregateBoundV3

noncomputable section

def dynamicFilteredTypeIIAnalyticAggregateV3
    (p : Corollary53Input) (delta H₀ T theta C : ℝ) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (component : OuterComponent) : ℝ :=
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  let leftCount := sourceDyadicCount (factorUpperProduct left)
  let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
  if dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeII then
    if suffix = [] then 0 else
      (leftCount : ℝ) * suffixCount *
        ∑ leftCell : Fin leftCount,
          ∑ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3
              zbag mbag left suffix leftCell,
            activeTypeIICellAnalyticRHSV3 p T theta C
              logIndex zbag mbag left suffix leftCell suffixCell component
  else 0

def dynamicAllTypeIIFilteredAnalyticLedgerV3
    (p : Corollary53Input) (delta H₀ T theta C : ℝ) : ℝ :=
  ∑ component : OuterComponent, ∑ branch : Fin (hbOrder delta),
    dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
      (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
        (branch : ℕ) : ℝ) *
      ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
        ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
          ∑ mbag ∈ dynamicLowMBagSetV3 p.X (hbOrder delta) (branch : ℕ),
            dynamicFilteredTypeIIAnalyticAggregateV3
              p delta H₀ T theta C logIndex zbag mbag component

/-- The complete refined Type-II source is bounded by one explicit filtered
analytic ledger with a coefficient constant depending only on the fixed HB
order and `theta`. -/
theorem exists_fixedOrder_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger
    (delta theta : ℝ) (hdelta : 0 < delta) (htheta : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Corollary53Input) [NeZero p.q]
        (hp : Corollary53Admissible 1 1 p)
        (H₀ T : ℝ) (hX : 2 ≤ p.X)
        (hH₀ : 0 ≤ H₀)
        (hglobal : (2 : ℝ) ^ (2 * hbOrder delta) * (2 * H₀) ≤ p.X)
        (hT : 1 ≤ T),
        (∑ component : OuterComponent,
          dynamicAllTypeIIMassRefinedV3
            p delta H₀ hX hdelta component) ≤
          dynamicAllTypeIIFilteredAnalyticLedgerV3
            p delta H₀ T theta C := by
  classical
  obtain ⟨C, hC, hcell⟩ :=
    exists_fixedOrder_activeTypeIICellAggregate_le_filteredAnalytic
      (hbOrder delta) (hbOrder_one hdelta) theta htheta
  refine ⟨C, hC, ?_⟩
  intro p _ hp H₀ T hX hH₀ hglobal hT
  calc
    _ ≤ dynamicAllTypeIICellLedgerRefinedV3 p delta H₀ hX hdelta :=
      sum_dynamicAllTypeIIMassRefined_le_cellLedger
        hp hX hdelta hH₀ hglobal
    _ ≤ dynamicAllTypeIIFilteredAnalyticLedgerV3
        p delta H₀ T theta C := by
      unfold dynamicAllTypeIICellLedgerRefinedV3
        dynamicAllTypeIIFilteredAnalyticLedgerV3
        dynamicRawTypeIICellLedgerV3
      apply Finset.sum_le_sum
      intro component hcomponent
      apply Finset.sum_le_sum
      intro branch hbranch
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro logIndex hlogIndex
        apply Finset.sum_le_sum
        intro zbag hzbag
        apply Finset.sum_le_sum
        intro mbag hmbag
        by_cases houtcome : dynamicComponentOutcome 8 delta H₀
            logIndex zbag mbag = .typeII
        · by_cases hsuffix : typeIISuffixFactorList
              (sortedComponentFactorList logIndex zbag mbag)
              (largestSmallPrefix
                (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
                (Real.rpow p.X delta)) = []
          · unfold dynamicTypeIICellAggregateV3
              dynamicFilteredTypeIIAnalyticAggregateV3
            dsimp only
            rw [if_pos houtcome, if_pos hsuffix,
              if_pos houtcome, if_pos hsuffix]
          · unfold dynamicFilteredTypeIIAnalyticAggregateV3
            dsimp only
            rw [if_pos houtcome, if_neg hsuffix]
            exact hcell p hp delta H₀ T hT branch logIndex zbag mbag houtcome hsuffix component
        · unfold dynamicTypeIICellAggregateV3
            dynamicFilteredTypeIIAnalyticAggregateV3
          dsimp only
          rw [if_neg houtcome, if_neg houtcome]
      · unfold dynamicBranchLowWeightRefinedV3
        positivity

/-- Specialization of the uniform-in-input ledger to one input. -/
theorem exists_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ T theta : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hH₀ : 0 ≤ H₀)
    (hglobal : (2 : ℝ) ^ (2 * hbOrder delta) * (2 * H₀) ≤ p.X)
    (hT : 1 ≤ T) (htheta : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧
      (∑ component : OuterComponent,
        dynamicAllTypeIIMassRefinedV3
          p delta H₀ hX hdelta component) ≤
        dynamicAllTypeIIFilteredAnalyticLedgerV3
          p delta H₀ T theta C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_fixedOrder_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger
      delta theta hdelta htheta
  exact ⟨C, hC, hbound p hp H₀ T hX hH₀ hglobal hT⟩

end
end MRTProposition61TypeIIGlobalFilteredAnalyticV3

#print axioms MRTProposition61TypeIIGlobalFilteredAnalyticV3.exists_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger

#print axioms MRTProposition61TypeIIGlobalFilteredAnalyticV3.exists_fixedOrder_sum_dynamicAllTypeIIMassRefined_le_uniformFilteredAnalyticLedger
