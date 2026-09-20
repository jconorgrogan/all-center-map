import MRTProposition61TypeIIComponentCauchyRefinedV3
import MRTProposition61TypeIIComponentTotalV3
import MAPDynamicTypeIIEmptySuffixParameterV3

/-! # Exact finite aggregation of every refined Type-II cell -/

namespace MRTProposition61TypeIIGlobalCellAggregationV3

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPFinishDynamicLowTypesRefinedV3 MAPFinishDynamicThreeTypeTrace
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3
open MRTProposition61TypeIIComponentCauchyRefinedV3
open MRTProposition61TypeIIComponentTotalV3
open MAPDynamicTypeIIEmptySuffixParameterV3

noncomputable section

def dynamicRawTypeIICellLedgerV3
    (p : Corollary53Input) (delta H₀ : ℝ) {K : ℕ}
    (branch : Fin K) (component : OuterComponent) : ℝ :=
  ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
    ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
      ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
        dynamicTypeIICellAggregateV3
          p delta H₀ logIndex zbag mbag component

theorem dynamicRawLowComponentMass_typeII_le_cellLedger
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} {K : ℕ} (hK : 1 ≤ K) (hH₀ : 0 ≤ H₀)
    (hglobal : (2 : ℝ) ^ (2 * K) * (2 * H₀) ≤ p.X)
    (branch : Fin K) (component : OuterComponent) :
    dynamicRawLowComponentMassV3
        p delta H₀ branch .typeII component ≤
      dynamicRawTypeIICellLedgerV3 p delta H₀ branch component := by
  unfold dynamicRawLowComponentMassV3 dynamicRawTypeIICellLedgerV3
  apply Finset.sum_le_sum
  intro logIndex hlog
  apply Finset.sum_le_sum
  intro zbag hzbag
  apply Finset.sum_le_sum
  intro mbag hmbag
  apply componentIntegral_dynamicTypeIIComponent_le_totalCells hp hK
  exact component_emptySuffix_large_of_branchEnvelope
    hH₀ hglobal branch logIndex zbag mbag

def dynamicAllTypeIICellLedgerRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  ∑ component : OuterComponent, ∑ branch : Fin (hbOrder delta),
    dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
      (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
        (branch : ℕ) : ℝ) *
      dynamicRawTypeIICellLedgerV3 p delta H₀ branch component

/-- The exact global finite Cauchy weld. Every tuple and double-dyadic cell
is present, while empty suffixes have already been killed. -/
theorem sum_dynamicAllTypeIIMassRefined_le_cellLedger
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hH₀ : 0 ≤ H₀)
    (hglobal : (2 : ℝ) ^ (2 * hbOrder delta) * (2 * H₀) ≤ p.X) :
    (∑ component : OuterComponent,
      dynamicAllTypeIIMassRefinedV3
        p delta H₀ hX hdelta component) ≤
      dynamicAllTypeIICellLedgerRefinedV3 p delta H₀ hX hdelta := by
  unfold dynamicAllTypeIICellLedgerRefinedV3
  apply Finset.sum_le_sum
  intro component hcomponent
  calc
    dynamicAllTypeIIMassRefinedV3
        p delta H₀ hX hdelta component ≤
      ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          dynamicRawLowComponentMassV3
            p delta H₀ branch .typeII component :=
      dynamicAllTypeIIMassRefined_le_rawComponents
        hp hX hdelta component
    _ ≤ ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          dynamicRawTypeIICellLedgerV3
            p delta H₀ branch component := by
      apply Finset.sum_le_sum
      intro branch hbranch
      have hcell := dynamicRawLowComponentMass_typeII_le_cellLedger
        (delta := delta) (H₀ := H₀) hp
        (hbOrder_one hdelta) hH₀ hglobal branch component
      have hw : 0 ≤ dynamicBranchLowWeightRefinedV3
          (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) := by
        unfold dynamicBranchLowWeightRefinedV3
        positivity
      exact mul_le_mul_of_nonneg_left hcell hw

end
end MRTProposition61TypeIIGlobalCellAggregationV3

#print axioms MRTProposition61TypeIIGlobalCellAggregationV3.sum_dynamicAllTypeIIMassRefined_le_cellLedger
