import MRTProposition61TypeIIActiveAggregateBoundV3
import MRTProposition61TypeIIActualCellLedgerV3
import MRTLemma215DynamicTypeIIUniformMajorantV3

/-! # Premise-free analytic bound on the genuinely active Type-II cells

Unlike the earlier unfiltered convenience bound, this statement retains the
sharp nonzero-cell filter.  Consequently every summand carries the exact
product-scale hypotheses needed by equation (3.5).
-/

namespace MRTProposition61TypeIIFilteredAggregateBoundV3

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBCanonicalPerronConstantV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicTypeIIFactorizationV3 MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIIUniformCellConstantV3
open MRTLemma215OpenIntervalCutoffV3
open MRTProposition61TypeIICellWeldV3
open MRTProposition61TypeIIComponentTotalV3
open MRTProposition61TypeIIActiveAggregateBoundV3
open MRTProposition61TypeIILemma210InstantiationV3
open MRTLemma215DynamicTypeIIUniformMajorantV3
open MontgomeryVaughanFiniteReduction
open RamachandraShiftedCoefficientEnergy

noncomputable section

/-- Every retained cell is bounded by the literal Lemma-2.10/Perron RHS;
inactive cells never enter this sum. -/
theorem exists_activeTypeIICellAggregate_le_filteredAnalytic
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ theta T : ℝ} {K k : ℕ}
    (hK : 1 ≤ K) (htheta : 0 < theta) (hT : 1 ≤ T)
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
    ∃ C : ℝ, 0 < C ∧
      dynamicTypeIICellAggregateV3
          p delta H₀ logIndex zbag mbag component ≤
        (leftCount : ℝ) * suffixCount *
          ∑ leftCell : Fin leftCount,
            ∑ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3
                zbag mbag left suffix leftCell,
              activeTypeIICellAnalyticRHSV3 p T theta C
                logIndex zbag mbag left suffix leftCell suffixCell component := by
  classical
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_uniform_actualTypeIICell_convolution_bound
      hK htheta logIndex zbag mbag houtcome
  refine ⟨C, hC, ?_⟩
  rw [dynamicTypeIICellAggregateV3_eq_nonzeroCells
    logIndex zbag mbag houtcome hsuffix component]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro leftCell hleftCell
    apply Finset.sum_le_sum
    intro suffixCell hsuffixCell
    let N : ℕ := 2 ^ (leftCell : ℕ)
    let M : ℕ := 2 ^ (suffixCell : ℕ)
    have hN : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
    have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
    have hsA := scaledTypeIIPrefixCell_supported zbag mbag left leftCell
    have hsB := factorListDyadicCell_supported suffix suffixCell
    have hab := MAPMRTProposition51Source.componentEndpoints_mono
      (X := p.X) (beta := p.beta) (by linarith [hp.1, hp.2.1])
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
    have hU : 0 ≤ stationaryWidth p.beta p.H := by
      unfold stationaryWidth
      have hH : 0 ≤ p.H := by linarith [hp.1]
      positivity
    have hcell := componentIntegral_typeIICell_le_lemma210_add_perron
      (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
      (q := p.q) (N := N) (M := M)
      (alpha := scaledTypeIIPrefixCell zbag mbag left leftCell)
      (gamma := factorListDyadicCell suffix suffixCell)
      (T := T) (B := C * Real.rpow (4 * (N : ℝ) * (M : ℝ)) theta)
      hN hM hsA hsB hT
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) theta))
      (hcoeff leftCell suffixCell) component hab hU
    dsimp [activeTypeIICellAnalyticRHSV3, N, M, left, suffix, s, factors]
      at hcell ⊢
    convert hcell using 1 <;> ring
  · positivity

/-- At fixed HB order, the filtered analytic estimate uses one common
coefficient constant for every branch and tuple. -/
theorem exists_fixedOrder_activeTypeIICellAggregate_le_filteredAnalytic
    (K : ℕ) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (p : Corollary53Input) [NeZero p.q]
        (hp : Corollary53Admissible 1 1 p)
        (delta H₀ T : ℝ) (hT : 1 ≤ T),
      ∀ (branch : Fin K)
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option
          (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff p.X K⌋₊))) ((branch : ℕ) + 1))
        (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
          .typeII)
        (hsuffix : typeIISuffixFactorList
          (sortedComponentFactorList logIndex zbag mbag)
          (largestSmallPrefix
            (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
            (Real.rpow p.X delta)) ≠ [])
        (component : OuterComponent),
        let factors := sortedComponentFactorList logIndex zbag mbag
        let s := largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta)
        let left := typeIIPrefixFactorList factors s
        let suffix := typeIISuffixFactorList factors s
        let leftCount := sourceDyadicCount (factorUpperProduct left)
        let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
        dynamicTypeIICellAggregateV3
            p delta H₀ logIndex zbag mbag component ≤
          (leftCount : ℝ) * suffixCount *
            ∑ leftCell : Fin leftCount,
              ∑ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3
                  zbag mbag left suffix leftCell,
                activeTypeIICellAnalyticRHSV3 p T theta C
                  logIndex zbag mbag left suffix leftCell suffixCell
                  component := by
  classical
  obtain ⟨C, hC, hcoeff⟩ :=
    exists_uniform_actualTypeIICell_convolution_bound_fixedOrder
      K hK theta htheta
  refine ⟨C, hC, ?_⟩
  intro p _ hp delta H₀ T hT branch logIndex zbag mbag houtcome hsuffix component
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  rw [dynamicTypeIICellAggregateV3_eq_nonzeroCells
    logIndex zbag mbag houtcome hsuffix component]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro leftCell hleftCell
    apply Finset.sum_le_sum
    intro suffixCell hsuffixCell
    let N : ℕ := 2 ^ (leftCell : ℕ)
    let M : ℕ := 2 ^ (suffixCell : ℕ)
    have hN : 1 ≤ N := Nat.one_le_pow _ _ (by omega)
    have hM : 1 ≤ M := Nat.one_le_pow _ _ (by omega)
    have hsA := scaledTypeIIPrefixCell_supported zbag mbag left leftCell
    have hsB := factorListDyadicCell_supported suffix suffixCell
    have hab := MAPMRTProposition51Source.componentEndpoints_mono
      (X := p.X) (beta := p.beta) (by linarith [hp.1, hp.2.1])
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
    have hU : 0 ≤ stationaryWidth p.beta p.H := by
      unfold stationaryWidth
      have hH : 0 ≤ p.H := by linarith [hp.1]
      positivity
    have hcell := componentIntegral_typeIICell_le_lemma210_add_perron
      (X := p.X) (H := p.H) (beta := p.beta) (eta := p.eta)
      (q := p.q) (N := N) (M := M)
      (alpha := scaledTypeIIPrefixCell zbag mbag left leftCell)
      (gamma := factorListDyadicCell suffix suffixCell)
      (T := T) (B := C * Real.rpow (4 * (N : ℝ) * (M : ℝ)) theta)
      hN hM hsA hsB hT
      (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) theta))
      (hcoeff branch logIndex zbag mbag houtcome leftCell suffixCell)
      component hab hU
    dsimp [activeTypeIICellAnalyticRHSV3, N, M, left, suffix, s, factors]
      at hcell ⊢
    convert hcell using 1 <;> ring
  · positivity

/-- Specialization of the fixed-order estimate to one input. -/
theorem exists_uniform_activeTypeIICellAggregate_le_filteredAnalytic
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    {delta H₀ theta T : ℝ} {K : ℕ}
    (hK : 1 ≤ K) (htheta : 0 < theta) (hT : 1 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (branch : Fin K)
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
        (zbag : Sym (Option
          (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff p.X K⌋₊))) ((branch : ℕ) + 1))
        (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
          .typeII)
        (hsuffix : typeIISuffixFactorList
          (sortedComponentFactorList logIndex zbag mbag)
          (largestSmallPrefix
            (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
            (Real.rpow p.X delta)) ≠ [])
        (component : OuterComponent),
        let factors := sortedComponentFactorList logIndex zbag mbag
        let s := largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow p.X delta)
        let left := typeIIPrefixFactorList factors s
        let suffix := typeIISuffixFactorList factors s
        let leftCount := sourceDyadicCount (factorUpperProduct left)
        let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
        dynamicTypeIICellAggregateV3
            p delta H₀ logIndex zbag mbag component ≤
          (leftCount : ℝ) * suffixCount *
            ∑ leftCell : Fin leftCount,
              ∑ suffixCell ∈ activeTypeIINonzeroSuffixCellsV3
                  zbag mbag left suffix leftCell,
                activeTypeIICellAnalyticRHSV3 p T theta C
                  logIndex zbag mbag left suffix leftCell suffixCell
                  component := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_fixedOrder_activeTypeIICellAggregate_le_filteredAnalytic
      K hK theta htheta
  exact ⟨C, hC, hbound p hp delta H₀ T hT⟩

end
end MRTProposition61TypeIIFilteredAggregateBoundV3

#print axioms MRTProposition61TypeIIFilteredAggregateBoundV3.exists_activeTypeIICellAggregate_le_filteredAnalytic
#print axioms MRTProposition61TypeIIFilteredAggregateBoundV3.exists_uniform_activeTypeIICellAggregate_le_filteredAnalytic

#print axioms MRTProposition61TypeIIFilteredAggregateBoundV3.exists_fixedOrder_activeTypeIICellAggregate_le_filteredAnalytic
