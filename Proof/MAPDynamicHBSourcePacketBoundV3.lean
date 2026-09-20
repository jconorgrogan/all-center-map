import MRTLemma215DynamicPacketSourceBoundV3
import MRTLemma215DynamicPacketComponentIntegralV3
import MAPDynamicHBSourceDecompositionV3

/-!
# Dynamic HB source mass bounded by literal packet integrals

This is the deterministic V3 analogue of the old fixed-eight source bound.
The honest outer loss is the dynamic HB order; the inner Cauchy loss is the
actual number of surviving packets of each raw branch plus one remainder.
-/

namespace MAPDynamicHBSourcePacketBoundV3

set_option maxHeartbeats 1200000

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPDynamicHBSourceDecompositionV3
open HBPerronPacketIndexedSourceV2
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215DynamicPacketSourceBoundV3
open MRTLemma215DynamicPacketComponentIntegralV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

def dynamicBranchPacketWeightV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) : ℝ :=
  (K : ℝ) *
    (Fintype.card (DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch) + 1 : ℕ)

theorem dynamicBranchPacketWeightV3_nonneg
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :
    0 ≤ dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch := by
  unfold dynamicBranchPacketWeightV3
  positivity

def dynamicBranchLowMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
    componentIntegral p.X p.H 1 p.q
      (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
      p.beta p.eta component

def dynamicBranchHighMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) : ℝ :=
  ∑ packet : DynamicBranchHighPacketIndexV3
      (H₀ := H₀) hX hdelta branch,
    dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch *
      ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (branchHighPacketToGlobalV3 packet) : ℝ)
            (openSourceLeft p.X) (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
            (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
            (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
          (stationaryWidth p.beta p.H) t) ^ 2

theorem dynamicHBSourceMassV3_cutoff_le_low_add_high
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
        (dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch +
          dynamicBranchHighMassV3 p delta H₀ hX hdelta component branch) := by
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have heta : 0 < p.eta := hp.2.2.2.2.1
  have hetaOne : p.eta ≤ 1 := hp.2.2.2.2.2.1
  unfold dynamicHBSourceMassV3
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro branch hbranch
  have hraw := componentIntegral_dynamicHBBranch_le_sourcePiecesV3
    (beta := p.beta) (q := p.q)
    hX hH heta hetaOne hdelta (hbOrder_one hdelta)
    hgeom hsize branch component
  let card := Fintype.card (DynamicBranchHighPacketIndexV3
    (H₀ := H₀) hX hdelta branch)
  have hsplit :
      (∑ piece : Option (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch),
        componentIntegral p.X p.H 1 p.q
          (dynamicBranchSourcePieceV3 hX hdelta branch piece)
          p.beta p.eta component) =
        componentIntegral p.X p.H 1 p.q
          (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
          p.beta p.eta component +
        ∑ packet : DynamicBranchHighPacketIndexV3
            (H₀ := H₀) hX hdelta branch,
          componentIntegral p.X p.H 1 p.q
            (intervalCutoff (openSourceLeft p.X) (2 * p.X)
              (branchHighPacketConvolutionV3 packet))
            p.beta p.eta component := by
    rw [Fintype.sum_option]
    rfl
  rw [hsplit] at hraw
  simp_rw [componentIntegral_branchHighPacket_eq_clipped] at hraw
  unfold dynamicBranchLowMassV3 dynamicBranchHighMassV3
    dynamicBranchPacketWeightV3
  calc
    (hbOrder delta : ℝ) *
        componentIntegral p.X p.H 1 p.q
          (dynamicHBBranchCoeff p.X (hbOrder delta) branch)
          p.beta p.eta component ≤
      (hbOrder delta : ℝ) *
        (((card + 1 : ℕ) : ℝ) *
          (componentIntegral p.X p.H 1 p.q
            (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
            p.beta p.eta component +
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
                  (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                  (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                  (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
                (stationaryWidth p.beta p.H) t) ^ 2)) := by
        exact mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = _ := by
      rw [show (hbOrder delta : ℝ) *
          (((card + 1 : ℕ) : ℝ) *
            (componentIntegral p.X p.H 1 p.q
              (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
              p.beta p.eta component +
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
                    (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                    (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                    (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
                  (stationaryWidth p.beta p.H) t) ^ 2)) =
          ((hbOrder delta : ℝ) * ((card + 1 : ℕ) : ℝ)) *
            (componentIntegral p.X p.H 1 p.q
              (dynamicBranchCombinedRemainderCoeffV3 p.X delta H₀ branch)
              p.beta p.eta component +
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
                    (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                    (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                    (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
                  (stationaryWidth p.beta p.H) t) ^ 2) by ring]
      rw [mul_add]
      congr 1
      simpa using (Finset.mul_sum (R := ℝ)
        (Finset.univ : Finset (DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch))
        (fun packet =>
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2,
            (characterMovingMass
              (typeD1ClippedNorm
                (highPacketLongLengthV3
                  (branchHighPacketToGlobalV3 packet) : ℝ)
                (highPacketShortLengthV3
                  (branchHighPacketToGlobalV3 packet) : ℝ)
                (openSourceLeft p.X) (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                (highPacketLongCoeffV3 (branchHighPacketToGlobalV3 packet))
                (highPacketShortCoeffV3 (branchHighPacketToGlobalV3 packet)))
              (stationaryWidth p.beta p.H) t) ^ 2)
        ((hbOrder delta : ℝ) * ((card + 1 : ℕ) : ℝ)))

end
end MAPDynamicHBSourcePacketBoundV3

#print axioms MAPDynamicHBSourcePacketBoundV3.dynamicHBSourceMassV3_cutoff_le_low_add_high
