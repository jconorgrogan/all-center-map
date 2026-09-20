import MAPDynamicHBHighMixedBudgetV3

/-!
# Exact expanded-budget ledger for the dynamic HB source

The packet-indexed expanded RHS is reduced definitionally to four visible
pieces: the nonprincipal-factor remainder, the three classified low types,
the finite Perron errors, and the certified high-packet mixed masses.  This
module performs only finite algebra and does not absorb any analytic term.
-/

namespace MAPDynamicHBExpandedBudgetLedgerV3

set_option maxHeartbeats 1000000

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPFarAnnulusSourceToModel MAPFarAnnulusMRT
open MAPHBPerronSourceData MAPPacketIndexedFarSourceV2
open MAPDynamicHBSourceDecompositionV3 MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBPacketIndexedDataV3 MAPDynamicHBPerronCellWeldV3
open MAPDynamicHBHighMixedBudgetV3

noncomputable section

theorem dynamicNonCellSourceTotalV3_eq
    (p : Corollary53Input) (delta : ℝ) :
    nonCellSourceTotal (hbDecompositionError p)
        (dynamicHBSourceMassV3 p delta) =
      ∑ component : OuterComponent, smallRemainderMass p component := by
  unfold nonCellSourceTotal hbDecompositionError dynamicHBSourceMassV3
  simp

theorem dynamicCellErrorTotalV3_eq
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    (∑ component : OuterComponent, ∑ branch : CutoffBranch,
      dynamicV3CellError (H₀ := H₀) hp hX hdelta component branch) =
      ∑ component : OuterComponent,
        (dynamicAllLowMassV3 p delta H₀ hX hdelta component +
          ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
            dynamicPacketCellErrorV3 hp hX hdelta component packet) := by
  apply Finset.sum_congr rfl
  intro component hcomponent
  unfold dynamicV3CellError
  simp

def dynamicExpandedCoreV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  (∑ component : OuterComponent, smallRemainderMass p component) +
  (∑ component : OuterComponent,
    (dynamicAllLowMassV3 p delta H₀ hX hdelta component +
      ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
        dynamicPacketCellErrorV3 hp hX hdelta component packet)) +
  dynamicIndexedMixedCellTotalV3 (H₀ := H₀) hp hX hdelta

theorem expandedPacketIndexedSourceRHS_dynamicV3_eq
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    expandedPacketIndexedSourceRHS p
        (dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta) =
      (divisorCount p.q : ℝ) ^ 4 /
          (p.q * stationaryWidth p.beta p.H ^ 2) *
        dynamicExpandedCoreV3 (H₀ := H₀) hp hX hdelta +
      ordinaryError p.X p.H p.f p.beta p.eta := by
  unfold expandedPacketIndexedSourceRHS dynamicExpandedCoreV3
  dsimp [dynamicPacketIndexedDataV3]
  rw [dynamicNonCellSourceTotalV3_eq]
  have herr := dynamicCellErrorTotalV3_eq (H₀ := H₀) hp hX hdelta
  rw [← herr]
  unfold dynamicIndexedMixedCellTotalV3
  dsimp [dynamicPacketIndexedDataV3]
  have hcenter : ∀ component : OuterComponent,
      (((componentEndpoints p.X p.beta p.eta component).1 - p.X) +
        ((componentEndpoints p.X p.beta p.eta component).2 + p.X)) / 2 =
      ((componentEndpoints p.X p.beta p.eta component).1 +
        (componentEndpoints p.X p.beta p.eta component).2) / 2 := by
    intro component
    ring
  have hwindow : ∀ component : OuterComponent,
      ((componentEndpoints p.X p.beta p.eta component).2 + p.X) -
          ((componentEndpoints p.X p.beta p.eta component).1 - p.X) +
          2 * stationaryWidth p.beta p.H =
        2 * stationaryWidth p.beta p.H + 2 * p.X -
          (componentEndpoints p.X p.beta p.eta component).1 +
          (componentEndpoints p.X p.beta p.eta component).2 := by
    intro component
    ring
  simp_rw [hcenter, hwindow]
  simp_rw [Finset.sum_add_distrib]
  simp only [add_assoc]
  rfl

end
end MAPDynamicHBExpandedBudgetLedgerV3

#print axioms MAPDynamicHBExpandedBudgetLedgerV3.dynamicNonCellSourceTotalV3_eq
#print axioms MAPDynamicHBExpandedBudgetLedgerV3.dynamicCellErrorTotalV3_eq
#print axioms MAPDynamicHBExpandedBudgetLedgerV3.expandedPacketIndexedSourceRHS_dynamicV3_eq
