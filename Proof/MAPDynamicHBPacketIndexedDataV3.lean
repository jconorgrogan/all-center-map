import MAPDynamicHBPerronCellWeldV3

/-!
# Existing packet-indexed interface for the dynamic V3 source

Every cutoff bookkeeping slot uses the same finite packet index.  Only the
`typeD3` slot is active in the dynamic source; the seven inactive slots add
nonnegative dummy cells.  This costs a fixed factor eight in the later upper
bound and avoids any dependent cast or strengthening of the source theorem.
-/

namespace MAPDynamicHBPacketIndexedDataV3

set_option maxHeartbeats 1000000

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPPacketIndexedFarSourceV2
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBPacketPerronV3
open MAPDynamicHBPerronCellWeldV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215OpenIntervalCutoffV3 MRTLemma215DyadicPartition
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215HBExpansion

noncomputable section

abbrev DynamicAllPacketsV3
    {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :=
  DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta

def dynamicPacketOfFinV3
    {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (i : Fin (Fintype.card (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta))) :
    DynamicAllPacketsV3 (H₀ := H₀) hX hdelta :=
  (Fintype.equivFin (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)).symm i

theorem sum_dynamicPacketOfFinV3
    {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (f : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta → ℝ) :
    (∑ i : Fin (Fintype.card
        (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
      f (dynamicPacketOfFinV3 hX hdelta i)) = ∑ packet, f packet := by
  exact Equiv.sum_comp
    (Fintype.equivFin (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)).symm f

theorem dynamicPacketLiteralCellV3_nonneg
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) :
    0 ≤ dynamicPacketLiteralCellV3 hp hX hdelta component packet := by
  have hX0 : 0 ≤ p.X := by linarith
  have hab := MAPMRTProposition51Source.componentEndpoints_mono
    (beta := p.beta) hX0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  unfold dynamicPacketLiteralCellV3 literalFactoredTypeDCell
  apply intervalIntegral.integral_nonneg
  · linarith
  · intro t ht
    positivity

def dynamicV3CellError
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : CutoffBranch) : ℝ :=
  if branch = .typeD3 then
    dynamicAllLowMassV3 p delta H₀ hX hdelta component +
      ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
        dynamicPacketCellErrorV3 hp hX hdelta component packet
  else 0

def dynamicPacketIndexedDataV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    PacketIndexedPaddedSourceData p where
  decompositionError := hbDecompositionError p
  sourceMass := dynamicHBSourceMassV3 p delta
  cellError := dynamicV3CellError (H₀ := H₀) hp hX hdelta
  blockCount := fun _ _ ↦ Fintype.card
    (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)
  q := fun _ _ _ ↦ p.q
  shortLength := fun _ _ i ↦
    highPacketShortLengthV3
      (allPacketGlobalV3 (dynamicPacketOfFinV3 hX hdelta i))
  longLength := fun _ _ i ↦
    highPacketLongLengthV3
      (allPacketGlobalV3 (dynamicPacketOfFinV3 hX hdelta i))
  beta := fun _ _ i ↦
    paddedCharacterTwist p.q p.q le_rfl
      (allPacketShortCoeffV3 (dynamicPacketOfFinV3 hX hdelta i))
  g := fun component _ i ↦
    scaleCoeffFamily
      (perronCellScale
        (dynamicPacketPerronKV3 hp hX hdelta component
          (dynamicPacketOfFinV3 hX hdelta i)) p.X)
      (paddedCharacterTwist p.q p.q le_rfl
        (scaledAllPacketLongCoeffV3 (dynamicPacketOfFinV3 hX hdelta i)))
  a := fun component _ _ ↦
    (componentEndpoints p.X p.beta p.eta component).1 - p.X
  b := fun component _ _ ↦
    (componentEndpoints p.X p.beta p.eta component).2 + p.X
  U := fun _ _ _ ↦ stationaryWidth p.beta p.H

theorem dynamicPacketIndexedCellsV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hgeom : Real.rpow p.X delta *
        (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (rawBranch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option
        (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (rawBranch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((rawBranch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
        Real.rpow p.X delta ≤ p.X)
    (component : OuterComponent) :
    SourceToPacketIndexedPaddedCells
      (fun branch ↦ dynamicHBSourceMassV3 p delta component (.cutoff branch))
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).cellError component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).blockCount component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).q component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).shortLength component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).longLength component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).beta component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).g component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).a component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).b component)
      ((dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).U component) := by
  intro branch
  have hnonneg : 0 ≤
      ∑ i : Fin (Fintype.card
          (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
        dynamicPacketLiteralCellV3 hp hX hdelta component
          (dynamicPacketOfFinV3 hX hdelta i) :=
    Finset.sum_nonneg fun i hi ↦
      dynamicPacketLiteralCellV3_nonneg hp hX hdelta component _
  cases branch with
  | typeD3 =>
      have hsource := dynamicHBSourceMassV3_cutoff_le_low_errors_cells
        (H₀ := H₀) hp hX hdelta hgeom hsize component
      have herr := sum_dynamicPacketOfFinV3 (H₀ := H₀) hX hdelta
        (fun packet ↦ dynamicPacketCellErrorV3
          (H₀ := H₀) hp hX hdelta component packet)
      have hcell := sum_dynamicPacketOfFinV3 (H₀ := H₀) hX hdelta
        (fun packet ↦ dynamicPacketLiteralCellV3
          (H₀ := H₀) hp hX hdelta component packet)
      unfold SourceToPacketIndexedPaddedCells at *
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError]
      calc
        dynamicHBSourceMassV3 p delta component (.cutoff .typeD3) ≤
            dynamicAllLowMassV3 p delta H₀ hX hdelta component +
              ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
                dynamicPacketTransferRHSV3 hp hX hdelta component packet := hsource
        _ = (dynamicAllLowMassV3 p delta H₀ hX hdelta component +
              ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
                dynamicPacketCellErrorV3 hp hX hdelta component packet) +
              ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
                dynamicPacketLiteralCellV3 hp hX hdelta component packet := by
            unfold dynamicPacketTransferRHSV3
            rw [Finset.sum_add_distrib]
            ring
        _ = _ := by
          rw [← herr, ← hcell]
          simp [dynamicPacketLiteralCellV3]
          rfl
  | typeD1 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeD2 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeD4 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeD5 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeD6 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeD7 =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg
  | typeII =>
      dsimp [dynamicPacketIndexedDataV3, dynamicV3CellError, dynamicHBSourceMassV3]
      simpa [dynamicPacketLiteralCellV3] using hnonneg

end
end MAPDynamicHBPacketIndexedDataV3

#print axioms MAPDynamicHBPacketIndexedDataV3.dynamicPacketLiteralCellV3_nonneg
#print axioms MAPDynamicHBPacketIndexedDataV3.dynamicPacketIndexedCellsV3
