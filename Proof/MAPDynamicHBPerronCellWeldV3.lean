import MAPDynamicHBPacketPerronV3

/-!
# Dynamic HB source to literal Perron cells

This module sums the certified packetwise Corollary 2.5 transfers.  The low
MRT branches and every Perron error remain explicit; no analytic budget is
used here.
-/

namespace MAPDynamicHBPerronCellWeldV3

set_option maxHeartbeats 800000

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBPacketPerronV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215OpenIntervalCutoffV3 MRTLemma215DyadicPartition
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215HBExpansion

noncomputable section

def dynamicPacketPerronKV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  Classical.choose
    (exists_dynamicPacketPerronTransferV3 hp hX hdelta component packet)

theorem dynamicPacketPerronKV3_pos
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 < dynamicPacketPerronKV3 hp hX hdelta component packet :=
  (Classical.choose_spec
    (exists_dynamicPacketPerronTransferV3 hp hX hdelta component packet)).1

def dynamicPacketCellErrorV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  perronCellError p.q
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (highPacketShortLengthV3 (allPacketGlobalV3 packet)) p.X
    (dynamicPacketConvolutionBoundV3 packet)
    (stationaryWidth p.beta p.H)
    (componentEndpoints p.X p.beta p.eta component).1
    (componentEndpoints p.X p.beta p.eta component).2
    (dynamicPacketPerronKV3 hp hX hdelta component packet)

def dynamicPacketLiteralCellV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  literalFactoredTypeDCell p.q
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (paddedCharacterTwist p.q p.q le_rfl
      (allPacketShortCoeffV3 packet))
    (scaleCoeffFamily
      (perronCellScale (dynamicPacketPerronKV3 hp hX hdelta component packet) p.X)
      (paddedCharacterTwist p.q p.q le_rfl
        (scaledAllPacketLongCoeffV3 packet)))
    ((componentEndpoints p.X p.beta p.eta component).1 - p.X)
    ((componentEndpoints p.X p.beta p.eta component).2 + p.X)
    (stationaryWidth p.beta p.H)

def dynamicPacketTransferRHSV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  dynamicPacketCellErrorV3 hp hX hdelta component packet +
    dynamicPacketLiteralCellV3 hp hX hdelta component packet

theorem dynamicPacketPerronTransferV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (openSourceLeft p.X) (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
          (scaledAllPacketLongCoeffV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2) ≤
      dynamicPacketCellErrorV3 hp hX hdelta component packet +
        dynamicPacketLiteralCellV3 hp hX hdelta component packet := by
  exact (Classical.choose_spec
    (exists_dynamicPacketPerronTransferV3 hp hX hdelta component packet)).2

/-- Exact deterministic V3 source-to-cell reduction.  Its remaining terms
are precisely the five low-source masses and the finite Perron errors. -/
theorem dynamicHBSourceMassV3_cutoff_le_low_errors_cells
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
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
        ∑ packet : DynamicAllHighPacketIndexV3
            (X := p.X) (delta := delta) (H₀ := H₀) hX hdelta,
          dynamicPacketTransferRHSV3 hp hX hdelta component packet := by
  calc
    dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
      dynamicAllLowMassV3 p delta H₀ hX hdelta component +
        dynamicAllScaledHighMassV3 p delta H₀ hX hdelta component :=
      dynamicHBSourceMassV3_cutoff_le_scaledPackets
        hp hX hdelta hgeom hsize component
    _ ≤ dynamicAllLowMassV3 p delta H₀ hX hdelta component +
        ∑ packet : DynamicAllHighPacketIndexV3
            (X := p.X) (delta := delta) (H₀ := H₀) hX hdelta,
          dynamicPacketTransferRHSV3 hp hX hdelta component packet := by
      apply add_le_add le_rfl
      unfold dynamicAllScaledHighMassV3
      exact Finset.sum_le_sum fun packet hpacket ↦
        dynamicPacketPerronTransferV3 (p := p) (delta := delta) (H₀ := H₀)
          hp hX hdelta component packet
    _ = _ := rfl

end
end MAPDynamicHBPerronCellWeldV3

#print axioms MAPDynamicHBPerronCellWeldV3.dynamicPacketPerronTransferV3
#print axioms MAPDynamicHBPerronCellWeldV3.dynamicHBSourceMassV3_cutoff_le_low_errors_cells
