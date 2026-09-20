import MAPDynamicHBScaledPacketSourceV3
import MAPDynamicHBSourcePacketBoundRefinedV3

/-! # Scaled high packets for the refined two-stage source bound -/

namespace MAPDynamicHBScaledPacketSourceRefinedV3

set_option maxHeartbeats 900000

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski MAPMRTCorollary25TypeD1IntegratedWeld
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPDynamicHBScaledPacketSourceV3
open HBPerronPacketIndexedSourceV2
open MRTLemma215DyadicPartition MRTLemma215DynamicFactorExtractionV3
open MRTLemma215HBExpansion
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

def dynamicPacketScaleRefinedV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) : ℝ :=
  Real.sqrt (dynamicBranchHighWeightRefinedV3
    (H₀ := H₀) hX hdelta branch)

theorem dynamicBranchHighWeightRefinedV3_nonneg
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) :
    0 ≤ dynamicBranchHighWeightRefinedV3
      (H₀ := H₀) hX hdelta branch := by
  unfold dynamicBranchHighWeightRefinedV3
  positivity

theorem dynamicPacketScaleRefinedV3_nonneg
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) :
    0 ≤ dynamicPacketScaleRefinedV3
      (H₀ := H₀) hX hdelta branch := by
  unfold dynamicPacketScaleRefinedV3
  positivity

theorem dynamicPacketScaleRefinedV3_sq
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) :
    dynamicPacketScaleRefinedV3 (H₀ := H₀) hX hdelta branch ^ 2 =
      dynamicBranchHighWeightRefinedV3
        (H₀ := H₀) hX hdelta branch := by
  unfold dynamicPacketScaleRefinedV3
  rw [Real.sq_sqrt]
  exact dynamicBranchHighWeightRefinedV3_nonneg hX hdelta branch

def scaledAllPacketLongCoeffRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    ℕ → ℂ :=
  scaleNatCoefficient
    (dynamicPacketScaleRefinedV3 (H₀ := H₀) hX hdelta packet.1)
    (highPacketLongCoeffV3 (allPacketGlobalV3 packet))

theorem characterMovingMass_scaledAllPacketRefined_eq_weight_mul
    {X delta H₀ L U t : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {q : ℕ}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    (characterMovingMass
      (typeD1ClippedNorm
        (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
        (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
        L (2 * X)
        (fun chi : DirichletCharacter ℂ q => fun n => chi n)
        (scaledAllPacketLongCoeffRefinedV3 packet)
        (allPacketShortCoeffV3 packet)) U t) ^ 2 =
      dynamicBranchHighWeightRefinedV3
          (H₀ := H₀) hX hdelta packet.1 *
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
            L (2 * X)
            (fun chi : DirichletCharacter ℂ q => fun n => chi n)
            (highPacketLongCoeffV3 (allPacketGlobalV3 packet))
            (allPacketShortCoeffV3 packet)) U t) ^ 2 := by
  unfold scaledAllPacketLongCoeffRefinedV3
  rw [characterMovingMass_scale_left
    (dynamicPacketScaleRefinedV3_nonneg hX hdelta packet.1)]
  rw [mul_pow, dynamicPacketScaleRefinedV3_sq]

def dynamicAllScaledHighMassRefinedV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta,
    ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
      (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (openSourceLeft p.X) (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
          (scaledAllPacketLongCoeffRefinedV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2

theorem dynamicAllHighMassRefined_eq_scaled
    (p : Corollary53Input) {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllHighMassRefinedV3 p delta H₀ hX hdelta component =
      dynamicAllScaledHighMassRefinedV3 p delta H₀ hX hdelta component := by
  unfold dynamicAllHighMassRefinedV3 dynamicBranchHighMassRefinedV3
    dynamicAllScaledHighMassRefinedV3
  let packetMass : DynamicAllHighPacketIndexV3
      (H₀ := H₀) hX hdelta → ℝ := fun packet =>
    ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
      (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (openSourceLeft p.X) (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
          (scaledAllPacketLongCoeffRefinedV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2
  change (∑ branch : Fin (hbOrder delta),
      dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta branch *
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
              (stationaryWidth p.beta p.H) t) ^ 2) = ∑ packet, packetMass packet
  have hsigma : (∑ packet : DynamicAllHighPacketIndexV3
      (H₀ := H₀) hX hdelta, packetMass packet) =
      ∑ branch : Fin (hbOrder delta),
        ∑ packet : DynamicBranchHighPacketIndexV3
          (H₀ := H₀) hX hdelta branch,
          packetMass ⟨branch, packet⟩ := by
    exact Fintype.sum_sigma packetMass
  rw [hsigma]
  apply Finset.sum_congr rfl
  intro branch hbranch
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro packet hpacket
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  exact (characterMovingMass_scaledAllPacketRefined_eq_weight_mul
    (Sigma.mk branch packet : DynamicAllHighPacketIndexV3
      (H₀ := H₀) hX hdelta)).symm

theorem dynamicHBSourceMassV3_cutoff_le_scaledPackets_refined
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
        dynamicAllScaledHighMassRefinedV3 p delta H₀ hX hdelta component := by
  calc
    dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
        dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component +
          dynamicAllHighMassRefinedV3 p delta H₀ hX hdelta component :=
      dynamicHBSourceMassV3_cutoff_le_refinedMasses
        hp hX hdelta hgeom hsize component
    _ = _ := by rw [dynamicAllHighMassRefined_eq_scaled]

end
end MAPDynamicHBScaledPacketSourceRefinedV3

#print axioms MAPDynamicHBScaledPacketSourceRefinedV3.dynamicAllHighMassRefined_eq_scaled
#print axioms MAPDynamicHBScaledPacketSourceRefinedV3.dynamicHBSourceMassV3_cutoff_le_scaledPackets_refined
