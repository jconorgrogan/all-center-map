import MAPDynamicHBSourcePacketBoundV3

/-!
# Scaled all-packet source family for the dynamic HB decomposition

The exact Cauchy factors are absorbed into the long coefficient of each high
packet.  This leaves the source bound as an unweighted sum of literal clipped
packet integrals plus the explicit low remainder mass.
-/

namespace MAPDynamicHBScaledPacketSourceV3

set_option maxHeartbeats 800000

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MAPDynamicHBSourceDecompositionV3 MAPDynamicHBSourcePacketBoundV3
open HBPerronPacketIndexedSourceV2
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215OpenIntervalCutoffV3 MRTLemma215DyadicPartition
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215HBExpansion

noncomputable section

def DynamicAllHighPacketIndexV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) :=
  Σ branch : Fin (hbOrder delta),
    DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch

instance {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) :
    Fintype (DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) := by
  classical
  unfold DynamicAllHighPacketIndexV3
  infer_instance

def allPacketGlobalV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta (hbOrder delta) :=
  branchHighPacketToGlobalV3 packet.2

def dynamicPacketScaleV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) : ℝ :=
  Real.sqrt (dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch)

theorem dynamicPacketScaleV3_nonneg
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) :
    0 ≤ dynamicPacketScaleV3 (H₀ := H₀) hX hdelta branch := by
  unfold dynamicPacketScaleV3
  positivity

theorem dynamicPacketScaleV3_sq
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (branch : Fin (hbOrder delta)) :
    dynamicPacketScaleV3 (H₀ := H₀) hX hdelta branch ^ 2 =
      dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta branch := by
  unfold dynamicPacketScaleV3
  rw [Real.sq_sqrt]
  exact dynamicBranchPacketWeightV3_nonneg hX hdelta branch

def scaledAllPacketLongCoeffV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℕ → ℂ :=
  scaleNatCoefficient
    (dynamicPacketScaleV3 (H₀ := H₀) hX hdelta packet.1)
    (highPacketLongCoeffV3 (allPacketGlobalV3 packet))

def allPacketShortCoeffV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℕ → ℂ :=
  highPacketShortCoeffV3 (allPacketGlobalV3 packet)

theorem scaledAllPacketLongSupportV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    SupportedNatDyadic (highPacketLongLengthV3 (allPacketGlobalV3 packet))
      (scaledAllPacketLongCoeffV3 packet) := by
  apply scaleNatCoefficient_supported
  exact (highPacket_supportV3 (allPacketGlobalV3 packet)).2

theorem allPacketShortSupportV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    SupportedNatDyadic (highPacketShortLengthV3 (allPacketGlobalV3 packet))
      (allPacketShortCoeffV3 packet) :=
  (highPacket_supportV3 (allPacketGlobalV3 packet)).1

/-- The scaled moving mass squares to the exact source Cauchy weight. -/
theorem characterMovingMass_scaledAllPacket_eq_weight_mul
    {X delta H₀ L U t : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {q : ℕ}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    (characterMovingMass
      (typeD1ClippedNorm
        (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
        (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
        L (2 * X)
        (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
        (scaledAllPacketLongCoeffV3 packet)
        (allPacketShortCoeffV3 packet)) U t) ^ 2 =
      dynamicBranchPacketWeightV3 (H₀ := H₀) hX hdelta packet.1 *
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
            L (2 * X)
            (fun chi : DirichletCharacter ℂ q ↦ fun n ↦ chi n)
            (highPacketLongCoeffV3 (allPacketGlobalV3 packet))
            (highPacketShortCoeffV3 (allPacketGlobalV3 packet))) U t) ^ 2 := by
  unfold scaledAllPacketLongCoeffV3 allPacketShortCoeffV3
  rw [characterMovingMass_scale_left
    (dynamicPacketScaleV3_nonneg hX hdelta packet.1)]
  rw [mul_pow, dynamicPacketScaleV3_sq]

def dynamicAllLowMassV3
    (p : Corollary53Input) (delta H₀ : ℝ)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) : ℝ :=
  ∑ branch : Fin (hbOrder delta),
    dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch

def dynamicAllScaledHighMassV3
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
          (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
          (scaledAllPacketLongCoeffV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2

theorem dynamicHBSourceMassV3_cutoff_le_scaledPackets
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
      dynamicAllLowMassV3 p delta H₀ hX hdelta component +
        dynamicAllScaledHighMassV3 p delta H₀ hX hdelta component := by
  have hraw := dynamicHBSourceMassV3_cutoff_le_low_add_high
    hp hX hdelta hgeom hsize component
  unfold dynamicAllLowMassV3 dynamicAllScaledHighMassV3
  calc
    dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
      ∑ branch : Fin (hbOrder delta),
        (dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch +
          dynamicBranchHighMassV3 p delta H₀ hX hdelta component branch) := hraw
    _ = (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowMassV3 p delta H₀ hX hdelta component branch) +
        ∑ packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta,
          ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
            (componentEndpoints p.X p.beta p.eta component).2,
            (characterMovingMass
              (typeD1ClippedNorm
                (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
                (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
                (openSourceLeft p.X) (2 * p.X)
                (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
                (scaledAllPacketLongCoeffV3 packet)
                (allPacketShortCoeffV3 packet))
              (stationaryWidth p.beta p.H) t) ^ 2 := by
      rw [Finset.sum_add_distrib]
      congr 1
      let packetMass : DynamicAllHighPacketIndexV3
          (H₀ := H₀) hX hdelta → ℝ := fun packet ↦
        ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
          (characterMovingMass
            (typeD1ClippedNorm
              (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
              (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
              (openSourceLeft p.X) (2 * p.X)
              (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
              (scaledAllPacketLongCoeffV3 packet)
              (allPacketShortCoeffV3 packet))
            (stationaryWidth p.beta p.H) t) ^ 2
      change (∑ branch : Fin (hbOrder delta),
        dynamicBranchHighMassV3 p delta H₀ hX hdelta component branch) =
        ∑ packet, packetMass packet
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
      unfold dynamicBranchHighMassV3
      apply Finset.sum_congr rfl
      intro packet hpacket
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t ht
      exact (characterMovingMass_scaledAllPacket_eq_weight_mul
        (Sigma.mk branch packet : DynamicAllHighPacketIndexV3
          (H₀ := H₀) hX hdelta)).symm
    _ = _ := rfl

end
end MAPDynamicHBScaledPacketSourceV3

#print axioms MAPDynamicHBScaledPacketSourceV3.characterMovingMass_scaledAllPacket_eq_weight_mul
#print axioms MAPDynamicHBScaledPacketSourceV3.dynamicHBSourceMassV3_cutoff_le_scaledPackets
