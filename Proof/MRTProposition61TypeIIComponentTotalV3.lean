import MRTProposition61TypeIIComponentCauchyV3
import MRTLemma215DynamicTypeIICellPruningV3

/-! # Total Type-II component-to-cell reduction, including empty suffixes -/

namespace MRTProposition61TypeIIComponentTotalV3

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicTypeIIFactorizationV3 MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIICellPruningV3
open MRTLemma215OpenIntervalCutoffV3
open MRTProposition61TypeIIComponentCauchyV3

noncomputable section

def dynamicTypeIICellAggregateV3
    (p : Corollary53Input) (delta H₀ : ℝ) {K k : ℕ}
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
        ∑ leftCell : Fin leftCount, ∑ suffixCell : Fin suffixCount,
          componentIntegral p.X p.H 1 p.q
            (intervalCutoff (openSourceLeft p.X) (2 * p.X)
              (literalDirichletConvolution
                (scaledTypeIIPrefixCell zbag mbag left leftCell)
                (factorListDyadicCell suffix suffixCell)))
            p.beta p.eta component
  else 0

theorem dynamicTypeIICellAggregateV3_nonneg
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (delta H₀ : ℝ) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (component : OuterComponent) :
    0 ≤ dynamicTypeIICellAggregateV3
      p delta H₀ logIndex zbag mbag component := by
  unfold dynamicTypeIICellAggregateV3
  dsimp only
  split_ifs
  · exact le_rfl
  · apply mul_nonneg
    · positivity
    · exact Finset.sum_nonneg fun leftCell hleft =>
        Finset.sum_nonneg fun suffixCell hsuffix =>
          componentIntegral_nonneg_of_admissibleGeometry
            (by linarith [hp.1, hp.2.1]) hp.2.2.2.2.1
            hp.2.2.2.2.2.1 component
  · exact le_rfl

/-- Complete local alternative. Non-Type-II components vanish; actual
Type-II components either have a nonempty suffix and enter the certified
cell expansion, or have an empty suffix and are killed by the displayed
large-X support inequality. -/
theorem componentIntegral_dynamicTypeIIComponent_le_totalCells
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (hlarge : (2 : ℝ) ^
        (sortedComponentFactorList logIndex zbag mbag).length *
          (2 * H₀) ≤ p.X)
    (component : OuterComponent) :
    componentIntegral p.X p.H 1 p.q
        (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag .typeII) p.beta p.eta component ≤
      dynamicTypeIICellAggregateV3
        p delta H₀ logIndex zbag mbag component := by
  by_cases houtcome : dynamicComponentOutcome 8 delta H₀
      logIndex zbag mbag = .typeII
  · by_cases hsuffix : typeIISuffixFactorList
        (sortedComponentFactorList logIndex zbag mbag)
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta)) = []
    · have hzero : dynamicComponentRemainderV3
          (delta := delta) (H₀ := H₀) logIndex zbag mbag .typeII = 0 := by
        funext n
        unfold dynamicComponentRemainderV3
        rw [houtcome]
        simp only
        exact maskedDynamicComponentV3_eq_zero_of_typeII_emptySuffix
          (by linarith [hp.1, hp.2.1]) hK logIndex zbag mbag
          houtcome hsuffix hlarge n
      rw [hzero]
      have hci : componentIntegral p.X p.H 1 p.q 0
          p.beta p.eta component = 0 := by
        simp [componentIntegral, characterWindow,
          criticalDirichletPolynomial]
      rw [hci]
      unfold dynamicTypeIICellAggregateV3
      dsimp only
      rw [if_pos houtcome, if_pos hsuffix]
    · have hcells := componentIntegral_dynamicTypeIIComponent_le_cells
        hp hK logIndex zbag mbag houtcome hsuffix component
      unfold dynamicTypeIICellAggregateV3
      dsimp only
      rw [if_pos houtcome, if_neg hsuffix]
      exact hcells
  · have hzero := dynamicComponentRemainderV3_typeII_eq_zero_of_outcome_ne
      logIndex zbag mbag houtcome
    rw [hzero]
    have hci : componentIntegral p.X p.H 1 p.q 0
        p.beta p.eta component = 0 := by
      simp [componentIntegral, characterWindow,
        criticalDirichletPolynomial]
    rw [hci]
    unfold dynamicTypeIICellAggregateV3
    dsimp only
    rw [if_neg houtcome]

noncomputable def activeTypeIINonzeroSuffixCellsV3
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (left suffix : List NatDyadicFactor)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct left))) :
    Finset (Fin (sourceDyadicCount (factorUpperProduct suffix))) := by
  classical
  exact (Finset.univ : Finset _).filter (fun suffixCell =>
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag left leftCell)
        (factorListDyadicCell suffix suffixCell)) ≠ 0)

/-- For one active Type-II tuple, remove exactly the sharp-masked zero
cells. This is an equality, so the later scale bounds may assume cell
nonvanishing without enlarging the source. -/
theorem dynamicTypeIICellAggregateV3_eq_nonzeroCells
    {p : Corollary53Input}
    {delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (hsuffix : typeIISuffixFactorList
      (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta)) ≠ [])
    (component : OuterComponent) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow p.X delta)
    let left := typeIIPrefixFactorList factors s
    let suffix := typeIISuffixFactorList factors s
    let leftCount := sourceDyadicCount (factorUpperProduct left)
    let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
    dynamicTypeIICellAggregateV3
        p delta H₀ logIndex zbag mbag component =
      (leftCount : ℝ) * suffixCount *
        ∑ leftCell : Fin leftCount,
          ∑ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3
              zbag mbag left suffix leftCell,
            componentIntegral p.X p.H 1 p.q
              (intervalCutoff (openSourceLeft p.X) (2 * p.X)
                (literalDirichletConvolution
                  (scaledTypeIIPrefixCell zbag mbag left leftCell)
                  (factorListDyadicCell suffix suffixCell)))
              p.beta p.eta component := by
  classical
  dsimp only
  unfold dynamicTypeIICellAggregateV3
  dsimp only
  rw [if_pos houtcome, if_neg hsuffix]
  congr 1
  apply Finset.sum_congr rfl
  intro leftCell hleftCell
  symm
  unfold activeTypeIINonzeroSuffixCellsV3
  apply Finset.sum_subset_zero_on_sdiff (Finset.filter_subset _ _)
  intro suffixCell hdiff
  have hmem : suffixCell ∈ (Finset.univ : Finset _ ) :=
    (Finset.mem_sdiff.mp hdiff).1
  have hnot := (Finset.mem_sdiff.mp hdiff).2
  have hzero : intervalCutoff (openSourceLeft p.X) (2 * p.X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag
          (typeIIPrefixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) leftCell)
        (factorListDyadicCell
          (typeIISuffixFactorList
            (sortedComponentFactorList logIndex zbag mbag)
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow p.X delta))) suffixCell)) = 0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hmem, hn⟩)
  rw [hzero]
  simp [componentIntegral, characterWindow, criticalDirichletPolynomial]
  intro suffixCell hmem
  rfl

end
end MRTProposition61TypeIIComponentTotalV3

#print axioms MRTProposition61TypeIIComponentTotalV3.componentIntegral_dynamicTypeIIComponent_le_totalCells
