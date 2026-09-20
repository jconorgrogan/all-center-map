import MRTLemma215DynamicHighPacketAggregateV3

/-!
# Flattened packet family for one raw dynamic HB branch

This module turns the exact componentwise packet expansion into the literal
single finite packet family consumed by Perron removal.  The open-left cutoff
is distributed over a finite sum coefficientwise; no boundary term is added.
-/

namespace MRTLemma215DynamicHighPacketFlattenV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary25 MAPHBPerronSourceData MAPDynamicHBSourceV3
open HBPerronPacketIndexedSourceV2
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicHighPacketsV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

/-- One surviving high packet whose raw HB branch is fixed. -/
def DynamicBranchHighPacketIndexV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :=
  Σ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
    {cell : Fin (sourceDyadicCount
        (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c)))) //
      cell ∈ survivingComplementCells
        (highSelectedFactorV3 hX hdelta (branchHighToGlobalV3 c)).length
        (highComplementV3 (branchHighToGlobalV3 c))}

instance {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :
    Fintype (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) := by
  classical
  unfold DynamicBranchHighPacketIndexV3
  infer_instance

def branchHighPacketToGlobalV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) :
    DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K :=
  ⟨branchHighToGlobalV3 packet.1, packet.2⟩

def branchHighPacketConvolutionV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) :
    ArithmeticFunction ℂ :=
  highPacketConvolutionV3 (branchHighPacketToGlobalV3 packet)

/-- Closed real interval cutoff commutes exactly with a finite sum of
arithmetic functions. -/
theorem intervalCutoff_fintypeSum
    {ι : Type*} [Fintype ι] (X1 X2 : ℝ)
    (F : ι → ArithmeticFunction ℂ) :
    intervalCutoff X1 X2
        ((∑ i, F i : ArithmeticFunction ℂ) : ℕ → ℂ) =
      ∑ i, intervalCutoff X1 X2 (F i) := by
  classical
  funext n
  have hsum : (∑ i : ι, F i) n = ∑ i : ι, F i n := by
    simpa using arithmeticFunction_finsetSum_apply
      (Finset.univ : Finset ι) F n
  have hcutSum : (∑ i : ι, intervalCutoff X1 X2 (F i)) n =
      ∑ i : ι, intervalCutoff X1 X2 (F i) n := by
    simpa using arithmeticFunction_finsetSum_apply
      (Finset.univ : Finset ι) (fun i => intervalCutoff X1 X2 (F i)) n
  rw [hcutSum]
  unfold intervalCutoff
  by_cases hn : X1 ≤ (n : ℝ) ∧ (n : ℝ) ≤ X2
  · simp [hn, hsum]
  · simp [hn]

theorem highComponentPacketSumV3_eq_branchCellSum
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} {branch : Fin K}
    (c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch) :
    highComponentPacketSumV3 hX hdelta (branchHighToGlobalV3 c) =
      ∑ cell : {cell : Fin (sourceDyadicCount
          (factorUpperProduct (highComplementV3 (branchHighToGlobalV3 c)))) //
        cell ∈ survivingComplementCells
          (highSelectedFactorV3 hX hdelta (branchHighToGlobalV3 c)).length
          (highComplementV3 (branchHighToGlobalV3 c))},
        branchHighPacketConvolutionV3
          (Sigma.mk c cell : DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch) := by
  rfl

set_option maxHeartbeats 800000 in
/-- One raw HB branch is exactly its low remainders plus one flattened family
of open-left-cutoff high packets. -/
theorem dynamicHBBranchCoeff_eq_remainders_add_flatHighPacketsV3
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
      (∑ kind : HBRemainderKind,
        dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind) +
      ∑ packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch,
        intervalCutoff (openSourceLeft X) (2 * X)
          (branchHighPacketConvolutionV3 packet) := by
  rw [show dynamicHBBranchCoeff X K branch =
      (∑ kind : HBRemainderKind,
        dynamicRawBranchRemainderCoeffV3 X delta H₀ branch kind) +
      dynamicRawBranchHighCoeffV3 X delta H₀ branch by
    funext n
    exact dynamicHBBranchCoeff_eq_remainders_add_highV3
      hX hdelta hK hgeom hsize branch n]
  congr 1
  rw [dynamicRawBranchHighCoeffV3_eq_cutoff_highComponentPacketSums
    hX hdelta hK branch]
  simp_rw [highComponentPacketSumV3_eq_branchCellSum hX hdelta]
  have hdist : ∀ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
      intervalCutoff (openSourceLeft X) (2 * X)
          (((∑ cell, branchHighPacketConvolutionV3
            (Sigma.mk c cell : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch)) : ArithmeticFunction ℂ) : ℕ → ℂ) =
        ∑ cell, intervalCutoff (openSourceLeft X) (2 * X)
          (branchHighPacketConvolutionV3
            (Sigma.mk c cell : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch)) := by
    intro c
    exact intervalCutoff_fintypeSum _ _ _
  rw [show (∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
      intervalCutoff (openSourceLeft X) (2 * X)
        (((∑ cell, branchHighPacketConvolutionV3
          (Sigma.mk c cell : DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch)) : ArithmeticFunction ℂ) : ℕ → ℂ)) =
      ∑ c : DynamicBranchHighComponentIndexV3 X delta H₀ K branch,
        ∑ cell, intervalCutoff (openSourceLeft X) (2 * X)
          (branchHighPacketConvolutionV3
            (Sigma.mk c cell : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch)) by
    exact Finset.sum_congr rfl (fun c hc => hdist c)]
  have hflat := Fintype.sum_sigma (fun packet :
    DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch =>
      intervalCutoff (openSourceLeft X) (2 * X)
        (branchHighPacketConvolutionV3 packet))
  exact hflat.symm

end
end MRTLemma215DynamicHighPacketFlattenV3

#print axioms MRTLemma215DynamicHighPacketFlattenV3.intervalCutoff_fintypeSum
#print axioms MRTLemma215DynamicHighPacketFlattenV3.dynamicHBBranchCoeff_eq_remainders_add_flatHighPacketsV3
