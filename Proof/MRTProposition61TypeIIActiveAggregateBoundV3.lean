import MRTProposition61TypeIIComponentTotalV3
import MRTLemma215DynamicTypeIIUniformCellConstantV3
import MRTProposition61TypeIICellWeldV3

/-! # Premise-free Lemma-2.10 insertion into one active Type-II aggregate -/

namespace MRTProposition61TypeIIActiveAggregateBoundV3

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
open MRTProposition61TypeIILemma210InstantiationV3
open MontgomeryVaughanFiniteReduction
open RamachandraShiftedCoefficientEnergy

noncomputable section

def activeTypeIICellAnalyticRHSV3
    (p : Corollary53Input) (T theta C : ℝ) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1))
    (left suffix : List NatDyadicFactor)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct left)))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)))
    (component : OuterComponent) : ℝ :=
  let N : ℕ := 2 ^ (leftCell : ℕ)
  let M : ℕ := 2 ^ (suffixCell : ℕ)
  2 * canonicalPerronKFour ^ 2 *
    ((∫ u in (-T)..T, perronWeight u) ^ 2 *
      (2 * stationaryWidth p.beta p.H *
        ((((p.q : ℝ) * (2 * stationaryWidth p.beta p.H) +
              8 * Real.pi * (N : ℝ)) *
            coefficientEnergy
              (criticalDyadicCoefficient
                (scaledTypeIIPrefixCell zbag mbag left leftCell)) N) *
         (((p.q : ℝ) *
              ((componentEndpoints p.X p.beta p.eta component).2 -
                (componentEndpoints p.X p.beta p.eta component).1 +
                2 * T + 2 * stationaryWidth p.beta p.H) +
              8 * Real.pi * (M : ℝ)) *
            coefficientEnergy
              (criticalDyadicCoefficient
                (factorListDyadicCell suffix suffixCell)) M))) +
      ((componentEndpoints p.X p.beta p.eta component).2 -
          (componentEndpoints p.X p.beta p.eta component).1) *
        (2 * stationaryWidth p.beta p.H *
          (Fintype.card (DirichletCharacter ℂ p.q) : ℝ) *
          (C * Real.rpow (4 * (N : ℝ) * (M : ℝ)) theta *
            Real.sqrt ((N : ℝ) * (M : ℝ)) *
            Real.log (2 + T) / T)) ^ 2)

/-- On an actual nonempty Type-II split, a single common positive
coefficient constant works for all cells, and every cell is bounded by the
premise-free Lemma-2.10 plus literal Perron expression. -/
theorem exists_activeTypeIICellAggregate_le_analytic
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
          ∑ leftCell : Fin leftCount, ∑ suffixCell : Fin suffixCount,
            activeTypeIICellAnalyticRHSV3 p T theta C
              logIndex zbag mbag left suffix leftCell suffixCell component := by
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
  unfold dynamicTypeIICellAggregateV3
  dsimp only
  rw [if_pos houtcome, if_neg hsuffix]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro leftCell hleftCell
    apply Finset.sum_le_sum
    intro suffixCell hsuffixCell
    let N : ℕ := 2 ^ (leftCell : ℕ)
    let M : ℕ := 2 ^ (suffixCell : ℕ)
    have hN : 1 ≤ N := by
      dsimp [N]
      exact Nat.one_le_pow _ _ (by omega)
    have hM : 1 ≤ M := by
      dsimp [M]
      exact Nat.one_le_pow _ _ (by omega)
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
      (mul_nonneg hC.le (Real.rpow_nonneg
        (show 0 ≤ 4 * (N : ℝ) * (M : ℝ) by positivity) theta))
      (hcoeff leftCell suffixCell) component hab
      hU
    dsimp [activeTypeIICellAnalyticRHSV3, N, M, left, suffix, s, factors]
      at hcell ⊢
    convert hcell using 1 <;> ring
  · positivity

end
end MRTProposition61TypeIIActiveAggregateBoundV3

#print axioms MRTProposition61TypeIIActiveAggregateBoundV3.exists_activeTypeIICellAggregate_le_analytic
