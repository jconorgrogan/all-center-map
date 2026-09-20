import MRTLemma215DynamicPacketSourceBoundRefinedV3
import MRTLemma215DynamicPacketComponentIntegralV3
import MAPDynamicHBSourceDecompositionV3

/-! # Refined dynamic HB source bound

The first Cauchy split separates the combined low coefficient from the sum of
high packets.  Consequently the low coefficient pays only `2 * hbOrder`; the
cardinality of the high packet family is charged only to its own summands.
-/

namespace MAPDynamicHBSourcePacketBoundRefinedV3

set_option maxHeartbeats 1200000

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski
open MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPDynamicHBSourceDecompositionV3
open MRTLemma215HBExpansion MRTLemma215DyadicPartition
open MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215DynamicPacketComponentIntegralV3
open MRTLemma215DynamicPacketSourceBoundV3
open MRTLemma215DynamicPacketSourceBoundRefinedV3
open MRTLemma215OpenIntervalCutoffV3
open MAPMRTCorollary25TypeD1LiteralWeld

noncomputable section

def dynamicBranchLowWeightRefinedV3 {K : ℕ} : ℝ := 2 * K

def dynamicBranchHighWeightRefinedV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) : ℝ :=
  2 * K * Fintype.card (DynamicBranchHighPacketIndexV3
    (H₀ := H₀) hX hdelta branch)

def dynamicBranchLowMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
    componentIntegral p.X p.H 1 p.q
      (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
      p.beta p.eta component

def dynamicBranchHighMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta branch *
  ∑ packet : DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch,
    ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            (openSourceLeft p.X) (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
            (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
            (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
          (stationaryWidth p.beta p.H) t) ^ 2

theorem dynamicHBSourceMassV3_cutoff_le_low_add_high_refined
    {p : Corollary53Input} {delta H₀ : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hgeom : Real.rpow p.X delta *
        (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow p.X delta ≤ p.X)
    (component : OuterComponent) :
    dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
      ∑ branch : Fin (hbOrder delta),
        (dynamicBranchLowMassRefinedV3 p delta H₀ hX hdelta component branch +
          dynamicBranchHighMassRefinedV3 p delta H₀ hX hdelta component branch) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  unfold dynamicHBSourceMassV3
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro branch hbranch
  have hraw := componentIntegral_dynamicHBBranch_le_twoStageV3
    (beta := p.beta) (q := p.q) hX hH heta hetaOne hdelta
    (hbOrder_one hdelta) hgeom hsize branch component
  simp_rw [componentIntegral_branchHighPacket_eq_clipped] at hraw
  unfold dynamicBranchLowMassRefinedV3 dynamicBranchHighMassRefinedV3
    dynamicBranchLowWeightRefinedV3 dynamicBranchHighWeightRefinedV3
  calc
    (hbOrder delta : ℝ) *
        componentIntegral p.X p.H 1 p.q
          (dynamicHBBranchCoeff p.X (hbOrder delta) branch)
          p.beta p.eta component ≤
      (hbOrder delta : ℝ) *
        (2 * componentIntegral p.X p.H 1 p.q
            (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
            p.beta p.eta component +
          2 * (Fintype.card (DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch) : ℝ) *
            ∑ packet : DynamicBranchHighPacketIndexV3
                (H₀ := H₀) hX hdelta branch,
              ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
                (componentEndpoints p.X p.beta p.eta component).2,
                (characterMovingMass
                  (typeD1ClippedNorm
                    (highPacketLongLengthV3
                      (branchHighPacketToGlobalV3 packet) : ℝ)
                    (highPacketShortLengthV3
                      (branchHighPacketToGlobalV3 packet) : ℝ)
                    (openSourceLeft p.X) (2 * p.X)
                    (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                    (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                    (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
                  (stationaryWidth p.beta p.H) t) ^ 2) :=
        mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = 2 * (hbOrder delta : ℝ) *
          componentIntegral p.X p.H 1 p.q
            (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
            p.beta p.eta component +
        (2 * (hbOrder delta : ℝ) *
          Fintype.card (DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch)) *
          ∑ packet : DynamicBranchHighPacketIndexV3
              (H₀ := H₀) hX hdelta branch,
            ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
              (componentEndpoints p.X p.beta p.eta component).2,
              (characterMovingMass
                (typeD1ClippedNorm
                  (highPacketLongLengthV3
                    (branchHighPacketToGlobalV3 packet) : ℝ)
                  (highPacketShortLengthV3
                    (branchHighPacketToGlobalV3 packet) : ℝ)
                  (openSourceLeft p.X) (2 * p.X)
                  (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
                  (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                  (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
                (stationaryWidth p.beta p.H) t) ^ 2 := by ring

def dynamicAllLowMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchLowMassRefinedV3 p delta H₀ hX hdelta component branch

def dynamicAllHighMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchHighMassRefinedV3 p delta H₀ hX hdelta component branch

theorem dynamicHBSourceMassV3_cutoff_le_refinedMasses
    {p : Corollary53Input} {delta H₀ : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hgeom : Real.rpow p.X delta *
        (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow p.X delta ≤ p.X)
    (component : OuterComponent) :
    dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
      dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component +
        dynamicAllHighMassRefinedV3 p delta H₀ hX hdelta component := by
  have h := dynamicHBSourceMassV3_cutoff_le_low_add_high_refined
    hp hX hdelta hgeom hsize component
  unfold dynamicAllLowMassRefinedV3 dynamicAllHighMassRefinedV3
  rw [Finset.sum_add_distrib] at h
  exact h

end
end MAPDynamicHBSourcePacketBoundRefinedV3

#print axioms MAPDynamicHBSourcePacketBoundRefinedV3.dynamicHBSourceMassV3_cutoff_le_low_add_high_refined
#print axioms MAPDynamicHBSourcePacketBoundRefinedV3.dynamicHBSourceMassV3_cutoff_le_refinedMasses
