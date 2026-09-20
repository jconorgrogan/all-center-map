import MAPDynamicHBPacketPerronV3
import MAPDynamicHBScaledPacketSourceRefinedV3

/-! # Perron transfer for refined two-stage scaled packets -/

namespace MAPDynamicHBPacketPerronRefinedV3

set_option maxHeartbeats 800000

open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPDynamicHBSourceV3
open MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBPacketPerronV3 HBPerronPacketIndexedSourceV2
open MRTLemma215DynamicHighPacketIndexV3

noncomputable section

theorem scaledAllPacketLongSupportRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    SupportedNatDyadic (highPacketLongLengthV3 (allPacketGlobalV3 packet))
      (scaledAllPacketLongCoeffRefinedV3 packet) := by
  apply scaleNatCoefficient_supported
  exact (highPacket_supportV3 (allPacketGlobalV3 packet)).2

def dynamicPacketConvolutionBoundRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  finiteLiteralConvolutionBound
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)

theorem dynamicPacketConvolutionBoundRefinedV3_nonneg
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 ≤ dynamicPacketConvolutionBoundRefinedV3 packet := by
  unfold dynamicPacketConvolutionBoundRefinedV3
  exact finiteLiteralConvolutionBound_nonneg _ _ _ _

theorem dynamicPacketConvolutionBoundRefinedV3_bound
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) (n : ℕ) :
    ‖literalDirichletConvolution
      (scaledAllPacketLongCoeffRefinedV3 packet)
      (allPacketShortCoeffV3 packet) n‖ ≤
        dynamicPacketConvolutionBoundRefinedV3 packet := by
  apply norm_literalDirichletConvolution_le_finiteBound
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).2.1.trans' (by omega)
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).1.trans' (by omega)
  · exact scaledAllPacketLongSupportRefinedV3 packet
  · exact allPacketShortSupportV3 packet

theorem exists_dynamicPacketPerronTransferRefinedV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    ∃ K : ℝ, 0 < K ∧
      (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (MRTLemma215OpenIntervalCutoffV3.openSourceLeft p.X) (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
            (scaledAllPacketLongCoeffRefinedV3 packet)
            (allPacketShortCoeffV3 packet))
          (stationaryWidth p.beta p.H) t) ^ 2) ≤
        perronCellError p.q
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (highPacketShortLengthV3 (allPacketGlobalV3 packet)) p.X
          (dynamicPacketConvolutionBoundRefinedV3 packet)
          (stationaryWidth p.beta p.H)
          (componentEndpoints p.X p.beta p.eta component).1
          (componentEndpoints p.X p.beta p.eta component).2 K +
        literalFactoredTypeDCell p.q
          (highPacketShortLengthV3 (allPacketGlobalV3 packet))
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (paddedCharacterTwist p.q p.q le_rfl
            (allPacketShortCoeffV3 packet))
          (scaleCoeffFamily (perronCellScale K p.X)
            (paddedCharacterTwist p.q p.q le_rfl
              (scaledAllPacketLongCoeffRefinedV3 packet)))
          ((componentEndpoints p.X p.beta p.eta component).1 - p.X)
          ((componentEndpoints p.X p.beta p.eta component).2 + p.X)
          (stationaryWidth p.beta p.H) := by
  have hgeom := highPacket_geometryV3 (allPacketGlobalV3 packet)
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX0 : 0 ≤ p.X := by linarith
  exact literalTypeD1_component95_to_paddedCell
    (by omega : 1 ≤ highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (by omega : 1 ≤ highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (by linarith : 1 ≤ p.X)
    (dynamicPacketConvolutionBoundRefinedV3_nonneg packet)
    (by unfold stationaryWidth; positivity)
    (MAPMRTProposition51Source.componentEndpoints_mono
      (beta := p.beta) hX0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component)
    (scaledAllPacketLongSupportRefinedV3 packet)
    (allPacketShortSupportV3 packet)
    (dynamicPacketConvolutionBoundRefinedV3_bound packet)

end
end MAPDynamicHBPacketPerronRefinedV3

#print axioms MAPDynamicHBPacketPerronRefinedV3.exists_dynamicPacketPerronTransferRefinedV3
