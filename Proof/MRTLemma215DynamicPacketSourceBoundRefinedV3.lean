import MRTLemma215DynamicPacketSourceBoundV3

/-! # Two-stage Cauchy for the dynamic source split -/

namespace MRTLemma215DynamicPacketSourceBoundRefinedV3

set_option maxHeartbeats 1200000

open scoped ArithmeticFunction BigOperators Matrix
open ArithmeticFunction
open MAPMRTCorollary25 MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicPacketSourceBoundV3
open MRTLemma215OpenIntervalCutoffV3
open MRTLemma215DynamicHighPacketFlattenV3

noncomputable section

/-- Splitting one coefficient into exactly two pieces costs two, independent
of the size of either piece's later internal packetization. -/
theorem componentIntegral_add_le_two
    {X H beta eta : ℝ} {q₀ q₁ : ℕ} (f g : ℕ → ℂ)
    (hX : 0 ≤ X) (hH : 0 ≤ H) (heta : 0 < eta) (hetaOne : eta ≤ 1)
    (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (fun n => f n + g n)
        beta eta component ≤
      2 * (componentIntegral X H q₀ q₁ f beta eta component +
        componentIntegral X H q₀ q₁ g beta eta component) := by
  let pieces : Fin 2 → ℕ → ℂ := ![f, g]
  have hraw := componentIntegral_finset_sum_le
    (Finset.univ : Finset (Fin 2)) pieces
    (beta := beta) (q₀ := q₀) (q₁ := q₁)
    hX hH heta hetaOne component
  simpa [pieces, Fin.sum_univ_two] using hraw

/-- The exact high packet sum coefficient of one dynamic HB branch. -/
def dynamicBranchHighSumCoeffV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) : ℕ → ℂ :=
  fun n => ∑ packet : DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch,
    intervalCutoff (openSourceLeft X) (2 * X)
      (branchHighPacketConvolutionV3 packet) n

/-- Exact equality before the refined inequality: the branch is one low
coefficient plus the complete high packet sum. -/
theorem dynamicHBBranchCoeff_eq_low_add_highSumV3
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
    dynamicHBBranchCoeff X K branch = fun n =>
      dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch n +
        dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch n := by
  rw [dynamicHBBranchCoeff_eq_sum_sourcePiecesV3
    hX hdelta hK hgeom hsize branch]
  funext n
  rw [Fintype.sum_option]
  simp [dynamicBranchSourcePieceV3, dynamicBranchHighSumCoeffV3,
    Finset.sum_apply]

/-- Sharpened branchwise Cauchy.  The low term pays only `2`; the high
family alone pays its cardinality. -/
theorem componentIntegral_dynamicHBBranch_le_twoStageV3
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
      2 * componentIntegral X H 1 q
          (dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch)
          beta eta component +
        2 * (Fintype.card (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch) : ℝ) *
          ∑ packet : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch,
            componentIntegral X H 1 q
              (intervalCutoff (openSourceLeft X) (2 * X)
                (branchHighPacketConvolutionV3 packet))
              beta eta component := by
  classical
  have hcoeff := dynamicHBBranchCoeff_eq_low_add_highSumV3
    hX hdelta hK hgeom hsize branch
  rw [hcoeff]
  have hadd := componentIntegral_add_le_two
    (X := X) (H := H) (beta := beta) (eta := eta) (q₀ := 1) (q₁ := q)
    (dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch)
    (dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch)
    (show 0 ≤ X by linarith) hH heta hetaOne component
  have hhigh := componentIntegral_finset_sum_le
    (Finset.univ : Finset (DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch))
    (fun packet n => intervalCutoff (openSourceLeft X) (2 * X)
      (branchHighPacketConvolutionV3 packet) n)
    (X := X) (H := H) (beta := beta) (eta := eta) (q₀ := 1) (q₁ := q)
    (by linarith) hH heta hetaOne component
  have hhigh' : componentIntegral X H 1 q
      (dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch)
      beta eta component ≤
      (Fintype.card (DynamicBranchHighPacketIndexV3
        (H₀ := H₀) hX hdelta branch) : ℝ) *
        ∑ packet : DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch,
          componentIntegral X H 1 q
            (intervalCutoff (openSourceLeft X) (2 * X)
              (branchHighPacketConvolutionV3 packet))
            beta eta component := by
    simpa [dynamicBranchHighSumCoeffV3] using hhigh
  calc
    componentIntegral X H 1 q
        (fun n => dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch n +
          dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch n)
        beta eta component ≤
      2 * (componentIntegral X H 1 q
          (dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch)
          beta eta component +
        componentIntegral X H 1 q
          (dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch)
          beta eta component) := hadd
    _ ≤ 2 * (componentIntegral X H 1 q
          (dynamicBranchCombinedRemainderCoeffV3 X delta H₀ branch)
          beta eta component +
        (Fintype.card (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch) : ℝ) *
          ∑ packet : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch,
            componentIntegral X H 1 q
              (intervalCutoff (openSourceLeft X) (2 * X)
                (branchHighPacketConvolutionV3 packet))
              beta eta component) := by gcongr
    _ = _ := by ring

end
end MRTLemma215DynamicPacketSourceBoundRefinedV3

#print axioms MRTLemma215DynamicPacketSourceBoundRefinedV3.componentIntegral_add_le_two
#print axioms MRTLemma215DynamicPacketSourceBoundRefinedV3.dynamicHBBranchCoeff_eq_low_add_highSumV3
#print axioms MRTLemma215DynamicPacketSourceBoundRefinedV3.componentIntegral_dynamicHBBranch_le_twoStageV3
