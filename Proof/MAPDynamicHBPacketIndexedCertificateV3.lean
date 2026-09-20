import MAPDynamicHBPacketIndexedDataV3

/-!
# Dynamic V3 packet certificate up to the explicit expanded budget

All structural fields of the existing far-source certificate are inhabited
from the arbitrary-order HB decomposition.  The sole remaining input is the
numeric bound on the fully expanded RHS.
-/

namespace MAPDynamicHBPacketIndexedCertificateV3

set_option maxHeartbeats 1000000

open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPMRTProposition51Source MAPFarAnnulusSourceToModel
open MAPPacketIndexedFarSourceV2 MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBPacketIndexedDataV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3

noncomputable section

theorem dynamicPacketIndexedIntervalOrderV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    ∀ component branch i,
      (dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).a
          component branch i ≤
        (dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).b
          component branch i := by
  intro component branch i
  dsimp [dynamicPacketIndexedDataV3]
  have hX0 : 0 ≤ p.X := by linarith
  have hend := componentEndpoints_mono (beta := p.beta) hX0
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  linarith

theorem dynamicPacketIndexedWidthNonnegV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    ∀ component branch i,
      0 ≤ (dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta).U
        component branch i := by
  intro component branch i
  dsimp [dynamicPacketIndexedDataV3, stationaryWidth]
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  positivity

/-- Constructor whose only uninhabited field is stated literally as the
expanded analytic budget to be proved next. -/
def dynamicPacketIndexedCertificateV3_of_expandedBudget
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ budget : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hf : p.f = mapMangoldtCoeff p.X)
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
    (hbudget : expandedPacketIndexedSourceRHS p
      (dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta) ≤ budget) :
    PacketIndexedPaddedSourceCertificate p budget where
  data := dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta
  sourceDecomposition := sourceBranchDecomposition_dynamicHBV3 hp hdelta hf
  paddedCells := dynamicPacketIndexedCellsV3
    (H₀ := H₀) hp hX hdelta hgeom hsize
  intervalOrder := dynamicPacketIndexedIntervalOrderV3
    (H₀ := H₀) hp hX hdelta
  widthNonneg := dynamicPacketIndexedWidthNonnegV3
    (H₀ := H₀) hp hX hdelta
  expandedBudget := hbudget

end
end MAPDynamicHBPacketIndexedCertificateV3

#print axioms MAPDynamicHBPacketIndexedCertificateV3.dynamicPacketIndexedIntervalOrderV3
#print axioms MAPDynamicHBPacketIndexedCertificateV3.dynamicPacketIndexedCertificateV3_of_expandedBudget
