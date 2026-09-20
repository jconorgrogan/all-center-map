import MRTLemma215DynamicPacketCriticalLineV3

/-!
# Deterministic source bound for the dynamic packet family

The literal raw HB branch is split into one combined low remainder and its
finite high-packet family.  Cauchy costs exactly `packetCount+1`.  Each packet
integral is then identified with the clipped moving-mass expression used by
certified Perron removal.
-/

namespace MRTLemma215DynamicPacketSourceBoundV3

set_option maxHeartbeats 2400000

open scoped ArithmeticFunction BigOperators
open MeasureTheory ArithmeticFunction
open MixedMeanFrontend DeterminantCountWeld
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPDynamicHBSourceV3
open HBPerronPacketIndexedSourceV2
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215DynamicPacketCriticalLineV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

def dynamicBranchCombinedRemainderCoeffV3
    (X delta H₀ : ℝ) {K : ℕ} (branch : Fin K) : ℕ → ℂ :=
  fun n => ∑ kind : HBRemainderKind,
    dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind n

def dynamicBranchSourcePieceV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :
    Option (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) →
      ℕ → ℂ
  | none => dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch
  | some packet => intervalCutoff (openSourceLeft X) (2 * X)
      (branchHighPacketConvolutionV3 packet)

theorem dynamicHBBranchCoeff_eq_sum_sourcePiecesV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (hK : 1 ≤ K)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin K)
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow X delta ≤ X)
    (branch : Fin K) :
    dynamicHBBranchCoeff X K branch =
      ∑ piece : Option (DynamicBranchHighPacketIndexV3
        (H₀ := H₀) hX hdelta branch),
        dynamicBranchSourcePieceV3 hX hdelta branch piece := by
  rw [dynamicHBBranchCoeff_eq_remainders_add_flatHighPacketsV3
    hX hdelta hK hgeom hsize branch]
  rw [Fintype.sum_option]
  rfl

/-- Exact branchwise Cauchy bound. -/
theorem componentIntegral_dynamicHBBranch_le_sourcePiecesV3
    {X H beta eta delta H₀ : ℝ}
    (hX : 2 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (hdelta : 0 < delta) {K q : ℕ} (hK : 1 ≤ K)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin K)
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow X delta ≤ X)
    (branch : Fin K) (component : OuterComponent) :
    componentIntegral X H 1 q (dynamicHBBranchCoeff X K branch)
        beta eta component ≤
      ((Fintype.card (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch) + 1 : ℕ) : ℝ) *
        ∑ piece : Option (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch),
          componentIntegral X H 1 q
            (dynamicBranchSourcePieceV3 hX hdelta branch piece)
            beta eta component := by
  classical
  have hcoeff := dynamicHBBranchCoeff_eq_sum_sourcePiecesV3
    hX hdelta hK hgeom hsize branch
  have hpoint : dynamicHBBranchCoeff X K branch = fun n =>
      ∑ piece ∈ (Finset.univ : Finset (Option
        (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch))),
        dynamicBranchSourcePieceV3 hX hdelta branch piece n := by
    rw [hcoeff]
    funext n
    simpa using Finset.sum_apply n
      (Finset.univ : Finset (Option
        (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch)))
      (dynamicBranchSourcePieceV3 hX hdelta branch)
  rw [hpoint]
  have hraw := componentIntegral_finset_sum_le
    (Finset.univ : Finset (Option (DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch)))
    (dynamicBranchSourcePieceV3 hX hdelta branch)
    (beta := beta) (q₀ := 1) (q₁ := q)
    (show 0 ≤ X by linarith) hH heta hetaOne component
  simpa using hraw

end
end MRTLemma215DynamicPacketSourceBoundV3

#print axioms MRTLemma215DynamicPacketSourceBoundV3.dynamicHBBranchCoeff_eq_sum_sourcePiecesV3
#print axioms MRTLemma215DynamicPacketSourceBoundV3.componentIntegral_dynamicHBBranch_le_sourcePiecesV3
