import MAPDynamicHBPacketPerronRefinedV3
import MAPDynamicHBCanonicalPerronConstantV3
import MRTLemma215DynamicHighCellPruningV3
import MRTLemma215DynamicHighSharpCoefficientBoundV3

/-! # Canonical-constant free-truncation Perron transfer for actual refined packets

Normalization repair: the older `dynamicPacketConvolutionBoundRefinedV3` uses
`finiteLiteralConvolutionBound`, an L1 sum over coefficients through `4MN`;
it is not a finite supremum and has no asserted subpower estimate here.
The new free-T transfer instead consumes `sharpPacketConvolutionBoundRefinedV3`,
the maximum of the norms of the literal scaled convolution on `Icc 0 (4MN)`.
Its unconditional pointwise bound supplies exactly the hypothesis of the
canonical Perron theorem. `freePacketErrorRefinedV3` and the adopted
`MRTProposition61HighActivePacketDataV3.activePacketIndexedData` use this maximum.
The original refined L1 error and certificate objects are unchanged.
-/

namespace MRTProposition61HighFreePerronV3

open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBPacketPerronV3 HBPerronPacketIndexedSourceV2
open MRTLemma215DynamicHighPacketIndexV3

open MAPDynamicHBCanonicalPerronConstantV3
open MAPDynamicHBPacketPerronRefinedV3
open MRTLemma215DynamicHighSharpCoefficientBoundV3

open scoped BigOperators
open MRTLemma215DynamicHighCellPruningV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3

noncomputable section

theorem dynamicPacketPerronTransferRefined_freeT_canonical
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (T : ℝ) (hT : 1 ≤ T)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
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
          (highPacketShortLengthV3 (allPacketGlobalV3 packet)) T
          (sharpPacketConvolutionBoundRefinedV3 packet)
          (stationaryWidth p.beta p.H)
          (componentEndpoints p.X p.beta p.eta component).1
          (componentEndpoints p.X p.beta p.eta component).2 canonicalPerronKFour +
        literalFactoredTypeDCell p.q
          (highPacketShortLengthV3 (allPacketGlobalV3 packet))
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (paddedCharacterTwist p.q p.q le_rfl
            (allPacketShortCoeffV3 packet))
          (scaleCoeffFamily (perronCellScale canonicalPerronKFour T)
            (paddedCharacterTwist p.q p.q le_rfl
              (scaledAllPacketLongCoeffRefinedV3 packet)))
          ((componentEndpoints p.X p.beta p.eta component).1 - T)
          ((componentEndpoints p.X p.beta p.eta component).2 + T)
          (stationaryWidth p.beta p.H) := by
  have hgeom := highPacket_geometryV3 (allPacketGlobalV3 packet)
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX0 : 0 ≤ p.X := by linarith
  exact literalTypeD1_component95_to_paddedCell_canonical
    (by omega : 1 ≤ highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (by omega : 1 ≤ highPacketShortLengthV3 (allPacketGlobalV3 packet))
    hT
    (sharpPacketConvolutionBoundRefinedV3_nonneg packet)
    (by unfold stationaryWidth; positivity)
    (MAPMRTProposition51Source.componentEndpoints_mono
      (beta := p.beta) hX0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component)
    (scaledAllPacketLongSupportRefinedV3 packet)
    (allPacketShortSupportV3 packet)
    (sharpPacketConvolutionBoundRefinedV3_bound packet)


/-- Exact error term for a free truncation, using the sharp finite coefficient
maximum of the actual scaled convolution and the single global Perron constant. -/
def freePacketErrorRefinedV3
    (p : Corollary53Input) (T : ℝ) {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  perronCellError p.q
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (highPacketShortLengthV3 (allPacketGlobalV3 packet)) T
    (sharpPacketConvolutionBoundRefinedV3 packet)
    (stationaryWidth p.beta p.H)
    (componentEndpoints p.X p.beta p.eta component).1
    (componentEndpoints p.X p.beta p.eta component).2 canonicalPerronKFour

/-- The matching literal cell. The scale and both endpoints use the same
free truncation, so the error and main terms remain a valid source transfer. -/
def freePacketCellRefinedV3
    (p : Corollary53Input) [NeZero p.q] (T : ℝ) {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  literalFactoredTypeDCell p.q
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (paddedCharacterTwist p.q p.q le_rfl (allPacketShortCoeffV3 packet))
    (scaleCoeffFamily (perronCellScale canonicalPerronKFour T)
      (paddedCharacterTwist p.q p.q le_rfl (scaledAllPacketLongCoeffRefinedV3 packet)))
    ((componentEndpoints p.X p.beta p.eta component).1 - T)
    ((componentEndpoints p.X p.beta p.eta component).2 + T)
    (stationaryWidth p.beta p.H)

/-- The actual refined high source is first pruned by its sharp mask, then
transferred using one freely chosen truncation. No source weight is discarded. -/
theorem dynamicAllScaledHighMassRefined_le_active_freeT
    {p : Corollary53Input} [NeZero p.q] {delta H₀ : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (T : ℝ) (hT : 1 ≤ T)
    (component : OuterComponent) :
    dynamicAllScaledHighMassRefinedV3 p delta H₀ hX hdelta component ≤
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        freePacketErrorRefinedV3 p T hX hdelta component packet) +
      ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        freePacketCellRefinedV3 p T hX hdelta component packet := by
  classical
  rw [dynamicAllScaledHighMassRefined_eq_active]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro packet hpacket
  exact dynamicPacketPerronTransferRefined_freeT_canonical hp hX hdelta T hT component packet

/-- Full low/high source decomposition with active-mask pruning and free
Perron truncation already welded in. -/
theorem dynamicHBSourceMassV3_cutoff_le_low_active_freeT
    {p : Corollary53Input} [NeZero p.q] {delta H₀ : ℝ}
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (T : ℝ) (hT : 1 ≤ T)
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
      (∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        freePacketErrorRefinedV3 p T hX hdelta component packet) +
      ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        freePacketCellRefinedV3 p T hX hdelta component packet := by
  have hsource := dynamicHBSourceMassV3_cutoff_le_scaledPackets_refined
    hp hX hdelta hgeom hsize component
  have hhigh := dynamicAllScaledHighMassRefined_le_active_freeT (H₀ := H₀) hp hX hdelta T hT component
  linarith

end
end MRTProposition61HighFreePerronV3

#print axioms MRTProposition61HighFreePerronV3.dynamicPacketPerronTransferRefined_freeT_canonical

#print axioms MRTProposition61HighFreePerronV3.dynamicHBSourceMassV3_cutoff_le_low_active_freeT
