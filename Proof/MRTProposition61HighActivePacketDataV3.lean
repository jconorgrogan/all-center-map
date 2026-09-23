import MRTProposition61HighFreePerronV3
import MAPDynamicHBPacketIndexedCertificateRefinedV3
import MAPDynamicHBExpandedBudgetLedgerRefinedV3

/-! # Active-mask, free-truncation packet data for the public source certificate -/

namespace MRTProposition61HighActivePacketDataV3

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25Minkowski MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTProposition51Source MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPPacketIndexedFarSourceV2
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3 MAPDynamicHBCanonicalPerronConstantV3
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215DynamicHighCellPruningV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion MRTLemma215DynamicFactorExtractionV3
open MRTProposition61HighFreePerronV3

noncomputable section
set_option maxHeartbeats 1600000

abbrev ActivePackets {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :=
  ↥(activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta)

def activePacketOfFin {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (i : Fin (Fintype.card (ActivePackets (H₀ := H₀) hX hdelta))) :
    DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta :=
  ((Fintype.equivFin (ActivePackets (H₀ := H₀) hX hdelta)).symm i).val

theorem sum_activePacketOfFin {p : Corollary53Input} {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (f : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta → ℝ) :
    (∑ i : Fin (Fintype.card (ActivePackets (H₀ := H₀) hX hdelta)),
      f (activePacketOfFin hX hdelta i)) =
    ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta, f packet := by
  classical
  calc
    _ = ∑ packet : ActivePackets (H₀ := H₀) hX hdelta, f packet.val :=
      Equiv.sum_comp (Fintype.equivFin (ActivePackets (H₀ := H₀) hX hdelta)).symm _
    _ = _ := Finset.sum_coe_sort _ _

def activeCellError {p : Corollary53Input} {delta H₀ : ℝ}
    (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : CutoffBranch) : ℝ :=
  if branch = .typeD3 then
    dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component +
      ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
        freePacketErrorRefinedV3 p T hX hdelta component packet
  else 0

def activePacketIndexedData {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    PacketIndexedPaddedSourceData p where
  decompositionError := hbDecompositionError p
  sourceMass := dynamicHBSourceMassV3 p delta
  cellError := activeCellError (H₀ := H₀) T hX hdelta
  blockCount := fun _ _ => Fintype.card (ActivePackets (H₀ := H₀) hX hdelta)
  q := fun _ _ _ => p.q
  shortLength := fun _ _ i => highPacketShortLengthV3 (allPacketGlobalV3 (activePacketOfFin hX hdelta i))
  longLength := fun _ _ i => highPacketLongLengthV3 (allPacketGlobalV3 (activePacketOfFin hX hdelta i))
  beta := fun _ _ i => paddedCharacterTwist p.q p.q le_rfl
    (allPacketShortCoeffV3 (activePacketOfFin hX hdelta i))
  g := fun _ _ i => scaleCoeffFamily (perronCellScale canonicalPerronKFour T)
    (paddedCharacterTwist p.q p.q le_rfl
      (scaledAllPacketLongCoeffRefinedV3 (activePacketOfFin hX hdelta i)))
  a := fun component _ _ => (componentEndpoints p.X p.beta p.eta component).1 - T
  b := fun component _ _ => (componentEndpoints p.X p.beta p.eta component).2 + T
  U := fun _ _ _ => stationaryWidth p.beta p.H

theorem freePacketCell_nonneg {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (T : ℝ) (hT : 0 ≤ T) (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 ≤ freePacketCellRefinedV3 p T hX hdelta component packet := by
  have hend := componentEndpoints_mono (beta := p.beta) (by linarith : 0 ≤ p.X)
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  unfold freePacketCellRefinedV3 literalFactoredTypeDCell
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t ht
  positivity

theorem activePacketIndexedCells
    {p : Corollary53Input} [NeZero p.q] {delta H₀ : ℝ}
    (hp : Corollary53Admissible 1 1 p) (T : ℝ) (hT : 1 ≤ T)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hgeom : Real.rpow p.X delta * (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length * Real.rpow p.X delta ≤ p.X)
    (component : OuterComponent) :
    SourceToPacketIndexedPaddedCells
      (fun branch => dynamicHBSourceMassV3 p delta component (.cutoff branch))
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).cellError component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).blockCount component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).q component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).shortLength component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).longLength component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).beta component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).g component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).a component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).b component)
      ((activePacketIndexedData (H₀ := H₀) T hX hdelta).U component) := by
  intro branch
  have hnonneg : 0 ≤ ∑ i : Fin (Fintype.card (ActivePackets (H₀ := H₀) hX hdelta)),
      freePacketCellRefinedV3 p T hX hdelta component (activePacketOfFin hX hdelta i) :=
    Finset.sum_nonneg fun i _ => freePacketCell_nonneg hp T (by linarith) hX hdelta component _
  cases branch with
  | typeD3 =>
    have hsource := dynamicHBSourceMassV3_cutoff_le_low_active_freeT
      (H₀ := H₀) hp hX hdelta T hT hgeom hsize component
    have hcell := sum_activePacketOfFin (H₀ := H₀) hX hdelta
      (fun packet => freePacketCellRefinedV3 p T hX hdelta component packet)
    rw [← hcell] at hsource
    dsimp [activePacketIndexedData, activeCellError]
    simpa only [freePacketCellRefinedV3] using! hsource
  | typeD1 | typeD2 | typeD4 | typeD5 | typeD6 | typeD7 | typeII =>
    dsimp [activePacketIndexedData, activeCellError, dynamicHBSourceMassV3]
    simpa only [freePacketCellRefinedV3, zero_add] using! hnonneg

/-- Public certificate constructor for the active-mask free-truncation data.
Its numerical input is the actual expanded RHS of this exact data object. -/
def activePacketCertificate_of_expandedBudget
    {p : Corollary53Input} [NeZero p.q] {delta H₀ budget : ℝ}
    (hp : Corollary53Admissible 1 1 p) (T : ℝ) (hT : 1 ≤ T)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hf : p.f = mapMangoldtCoeff p.X)
    (hgeom : Real.rpow p.X delta * (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hsize : ∀ (branch : Fin (hbOrder delta))
      (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (branch : ℕ))
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((branch : ℕ) + 1)),
      (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length * Real.rpow p.X delta ≤ p.X)
    (hbudget : expandedPacketIndexedSourceRHS p
      (activePacketIndexedData (H₀ := H₀) T hX hdelta) ≤ budget) :
    PacketIndexedPaddedSourceCertificate p budget where
  data := activePacketIndexedData (H₀ := H₀) T hX hdelta
  sourceDecomposition := sourceBranchDecomposition_dynamicHBV3 hp hdelta hf
  paddedCells := activePacketIndexedCells hp T hT hX hdelta hgeom hsize
  intervalOrder := by
    intro component branch i
    dsimp [activePacketIndexedData]
    have hend := componentEndpoints_mono (beta := p.beta) (by linarith : 0 ≤ p.X)
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
    linarith
  widthNonneg := by
    intro component branch i
    dsimp [activePacketIndexedData, stationaryWidth]
    have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
    positivity
  expandedBudget := hbudget

def activeIndexedMixedTotal {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  let d := activePacketIndexedData (H₀ := H₀) T hX hdelta
  ∑ component : OuterComponent, ∑ branch : CutoffBranch,
    ∑ i : Fin (d.blockCount component branch),
      2 * characterPairMixedMass (d.q component branch i) (d.shortLength component branch i)
        (d.longLength component branch i)
        (pairShortFamily (d.beta component branch i)) (pairLongFamily (d.g component branch i))
        ((d.a component branch i + d.b component branch i) / 2)
        ((d.b component branch i - d.a component branch i) + 2 * d.U component branch i)
        (d.U component branch i)

def activeExpandedCore {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  (∑ component : OuterComponent, smallRemainderMass p component) +
    (∑ component : OuterComponent,
      (dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component +
        ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          freePacketErrorRefinedV3 p T hX hdelta component packet)) +
    activeIndexedMixedTotal (H₀ := H₀) T hX hdelta

/-- Exact expanded budget for the adopted active/free-truncation certificate. -/
theorem expandedSourceRHS_active_eq
    {p : Corollary53Input} [NeZero p.q] {delta H₀ : ℝ}
    (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    expandedPacketIndexedSourceRHS p (activePacketIndexedData (H₀ := H₀) T hX hdelta) =
      (divisorCount p.q : ℝ) ^ 4 / (p.q * stationaryWidth p.beta p.H ^ 2) *
        activeExpandedCore (H₀ := H₀) T hX hdelta +
      ordinaryError p.X p.H p.f p.beta p.eta := by
  unfold expandedPacketIndexedSourceRHS activeExpandedCore
  dsimp [activePacketIndexedData]
  rw [MAPDynamicHBExpandedBudgetLedgerRefinedV3.dynamicNonCellSourceTotalV3_eq]
  have herr : (∑ component : OuterComponent, ∑ branch : CutoffBranch,
      activeCellError (H₀ := H₀) T hX hdelta component branch) =
      ∑ component : OuterComponent,
        (dynamicAllLowMassRefinedV3 p delta H₀ hX hdelta component +
          ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
            freePacketErrorRefinedV3 p T hX hdelta component packet) := by
    apply Finset.sum_congr rfl
    intro component hc
    unfold activeCellError
    simp
  rw [← herr]
  unfold activeIndexedMixedTotal
  dsimp [activePacketIndexedData]
  simp_rw [Finset.sum_add_distrib]
  simp only [add_assoc]
  rfl

end
end MRTProposition61HighActivePacketDataV3

#print axioms MRTProposition61HighActivePacketDataV3.activePacketIndexedCells

#print axioms MRTProposition61HighActivePacketDataV3.activePacketCertificate_of_expandedBudget

#print axioms MRTProposition61HighActivePacketDataV3.expandedSourceRHS_active_eq
