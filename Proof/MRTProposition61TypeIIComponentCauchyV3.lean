import MRTLemma215DynamicTypeIIMaskedPacketsV3
import MAPFinishDynamicThreeTypeTrace
import MAPFinishDynamicLowTypes

/-!
# Finite Cauchy collection for one dynamic Type-II component

This file prices the exact double-dyadic packet expansion before any analytic
cell estimate is inserted.  Both cell cardinalities remain literal.
-/

namespace MRTProposition61TypeIIComponentCauchyV3

set_option maxHeartbeats 1200000

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MAPDynamicHBSourcePacketBoundV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicClassificationV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215OpenIntervalCutoffV3
open MAPFinishDynamicThreeTypeTrace MAPFinishDynamicLowTypes

noncomputable section

/-- One actual Type-II preliminary component is controlled by the sum of its
masked double-dyadic cell masses, with exactly one Cauchy cardinality for each
finite cell family. -/
theorem componentIntegral_dynamicTypeIIComponent_le_cells
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} {K k : ℕ} (hK : 1 ≤ K)
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
    componentIntegral p.X p.H 1 p.q
        (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag .typeII) p.beta p.eta component ≤
      let factors := sortedComponentFactorList logIndex zbag mbag
      let s := largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow p.X delta)
      let leftFactors := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      let leftCount := sourceDyadicCount (factorUpperProduct leftFactors)
      let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
      (leftCount : ℝ) * suffixCount *
        ∑ leftCell : Fin leftCount,
          ∑ suffixCell : Fin suffixCount,
            componentIntegral p.X p.H 1 p.q
              (intervalCutoff (openSourceLeft p.X) (2 * p.X)
                (literalDirichletConvolution
                  (scaledTypeIIPrefixCell zbag mbag leftFactors leftCell)
                  (factorListDyadicCell suffix suffixCell)))
              p.beta p.eta component := by
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow p.X delta)
  let leftFactors := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  let leftCount := sourceDyadicCount (factorUpperProduct leftFactors)
  let suffixCount := sourceDyadicCount (factorUpperProduct suffix)
  let packet := fun (leftCell : Fin leftCount) (suffixCell : Fin suffixCount) ↦
    intervalCutoff (openSourceLeft p.X) (2 * p.X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag leftFactors leftCell)
        (factorListDyadicCell suffix suffixCell))
  have hXone : 1 ≤ p.X := by linarith [hp.1, hp.2.1]
  have hexpand := dynamicComponentRemainderV3_typeII_eq_sum_maskedPackets
    hXone hK logIndex zbag mbag houtcome hsuffix
  have hX0 : 0 ≤ p.X := by linarith
  have hH0 : 0 ≤ p.H := by linarith [hp.1]
  have houter := componentIntegral_finset_sum_le
    (Finset.univ : Finset (Fin leftCount))
    (fun leftCell n ↦ ∑ suffixCell : Fin suffixCount,
      packet leftCell suffixCell n)
    (beta := p.beta) (q₀ := 1) (q₁ := p.q)
    hX0 hH0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  have hinner :
      (∑ leftCell : Fin leftCount,
        componentIntegral p.X p.H 1 p.q
          (fun n ↦ ∑ suffixCell : Fin suffixCount,
            packet leftCell suffixCell n)
          p.beta p.eta component) ≤
      (suffixCount : ℝ) *
        ∑ leftCell : Fin leftCount,
          ∑ suffixCell : Fin suffixCount,
            componentIntegral p.X p.H 1 p.q
              (packet leftCell suffixCell) p.beta p.eta component := by
    calc
      _ ≤ ∑ leftCell : Fin leftCount,
          (suffixCount : ℝ) * ∑ suffixCell : Fin suffixCount,
            componentIntegral p.X p.H 1 p.q
              (packet leftCell suffixCell) p.beta p.eta component := by
        apply Finset.sum_le_sum
        intro leftCell hleft
        simpa using componentIntegral_finset_sum_le
          (Finset.univ : Finset (Fin suffixCount)) (packet leftCell)
          (beta := p.beta) (q₀ := 1) (q₁ := p.q)
          hX0 hH0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
      _ = _ := by rw [Finset.mul_sum]
  have hexpand' :
      dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag .typeII =
        fun n ↦ ∑ leftCell : Fin leftCount,
          ∑ suffixCell : Fin suffixCount, packet leftCell suffixCell n := by
    rw [hexpand]
    funext n
    simp [packet, factors, s, leftFactors, suffix, leftCount, suffixCount]
  have houter' := mul_le_mul_of_nonneg_left houter
    (show 0 ≤ (leftCount : ℝ) by positivity)
  have hinner' := mul_le_mul_of_nonneg_left hinner
    (show 0 ≤ (leftCount : ℝ) by positivity)
  calc
    componentIntegral p.X p.H 1 p.q
        (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag .typeII) p.beta p.eta component =
      componentIntegral p.X p.H 1 p.q
        (fun n ↦ ∑ leftCell : Fin leftCount,
          ∑ suffixCell : Fin suffixCount, packet leftCell suffixCell n)
        p.beta p.eta component := by rw [hexpand']
    _ ≤ (leftCount : ℝ) *
        ∑ leftCell : Fin leftCount,
          componentIntegral p.X p.H 1 p.q
            (fun n ↦ ∑ suffixCell : Fin suffixCount,
              packet leftCell suffixCell n)
            p.beta p.eta component := by simpa [packet] using houter
    _ ≤ (leftCount : ℝ) * (suffixCount : ℝ) *
        ∑ leftCell : Fin leftCount,
          ∑ suffixCell : Fin suffixCount,
            componentIntegral p.X p.H 1 p.q
              (packet leftCell suffixCell) p.beta p.eta component := by
      simpa [mul_assoc] using hinner'

/-- First global collection layer: one branch Type-II mass is bounded by the
literal tuple multiplicity times the sum of its individual classified
component masses. -/
theorem dynamicBranchTypeIIMassV3_le_rawComponents
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchTypeIIMassV3 p delta H₀ hX hdelta component branch ≤
      dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
        (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
          (branch : ℕ) : ℝ) *
        dynamicRawLowComponentMassV3 p delta H₀ branch .typeII component := by
  have hraw :=
    componentIntegral_dynamicRawBranchRemainderCoeffV3_le_components
      (delta := delta) (H₀ := H₀) hp branch
      HBPerronPacketIndexedSourceV2.HBRemainderKind.typeII component
  have hw : 0 ≤ dynamicBranchPacketWeightV3 (H₀ := H₀)
      hX hdelta branch := dynamicBranchPacketWeightV3_nonneg hX hdelta branch
  unfold dynamicBranchTypeIIMassV3
  have hmul := mul_le_mul_of_nonneg_left hraw hw
  simpa [mul_assoc] using hmul

/-- Summing the preceding exact branch bound gives the complete first-stage
Type-II collection inequality for one outer component. -/
theorem dynamicAllTypeIIMassV3_le_rawComponents
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllTypeIIMassV3 p delta H₀ hX hdelta component ≤
      ∑ branch : Fin (hbOrder delta),
        dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta)
            (branch : ℕ) : ℝ) *
          dynamicRawLowComponentMassV3 p delta H₀ branch .typeII component := by
  unfold dynamicAllTypeIIMassV3
  exact Finset.sum_le_sum fun branch hbranch ↦
    dynamicBranchTypeIIMassV3_le_rawComponents
      hp hX hdelta component branch

end
end MRTProposition61TypeIIComponentCauchyV3

#print axioms MRTProposition61TypeIIComponentCauchyV3.componentIntegral_dynamicTypeIIComponent_le_cells
#print axioms MRTProposition61TypeIIComponentCauchyV3.dynamicAllTypeIIMassV3_le_rawComponents
