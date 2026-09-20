import MAPPacketIndexedFarBudgetConsumerV2
import MRTProposition61HighAdoptedThirtiethV3
import MAPDynamicHBSourceDecompositionV3
import MRTLemma215DyadicPartition
import MRTLemma215DynamicFactorExtractionV3

/-!
# Active high certificate bridge

This is the smallest source-facing adapter for the adopted high packet data.
It deliberately does not coerce the adopted field into
`DynamicV3TermwiseBudget.high_packets`: that field describes the old
all-packet, `T = X`, unrefined L1 data.  The bridge instead consumes the
literal expanded budget for `activePacketIndexedData`, whose high term is the
active free-`T` sharp-max field.
-/

namespace MRTProposition61HighCertificateBridgeV3

open scoped BigOperators
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBSourceDecompositionV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MAPDynamicHBPacketIndexedDataRefinedV3
open MAPDynamicHBExpandedBudgetLedgerRefinedV3
open MAPPacketIndexedFarSourceV2
open MAPPacketIndexedFarBudgetConsumerV2
open MAPAllCenterApertureTransfer
open MRTLemma215DyadicPartition MRTLemma215DynamicFactorExtractionV3 MRTLemma215HBExpansion
open MRTProposition61HighActivePacketDataV3
open MRTProposition61HighAdoptedThirtiethV3
open MRTProposition61HighEnvelopeSplitV3
open MAPFinishDynamicLowTypes

noncomputable section

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-- Exact prerequisites for constructing the public packet-indexed
certificate from the adopted active/free-`T` packet data.

`high_mass` is intentionally an explicit proved mass bound.  No theorem about
the incompatible original `high_packets` field is accepted here. -/
structure ActivePacketCertificateBridge (delta : ℝ)
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (budget : ℝ) where
  delta_pos : 0 < delta
  map_coefficient : p.f = mapMangoldtCoeff p.X
  classifier_geometry : Real.rpow p.X delta *
    (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤
    2 * highClassifierH0 p.X delta
  component_size : ∀ (rawBranch : Fin (hbOrder delta))
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option
      (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (rawBranch : ℕ))
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((rawBranch : ℕ) + 1)),
    (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
      Real.rpow p.X delta ≤ p.X
  truncation_ge_one : 1 ≤ selectedHighTruncation p
  remainder_le : dynamicLowNormalizationV3 p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
    budget / 5
  low_le : dynamicLowNormalizationV3 p *
      (∑ component : OuterComponent,
        dynamicAllLowMassRefinedV3 p delta (highClassifierH0 p.X delta)
          hX delta_pos component) ≤ budget / 5
  high_mass : activeCertificateHighSlot p delta hX delta_pos ≤ budget / 5
  ordinary_le : ordinaryError p.X p.H p.f p.beta p.eta ≤ budget / 5

/-- The bridge's output is the exact public certificate for the adopted data. -/
def toPacketIndexedCertificate
    {p : Corollary53Input} [NeZero p.q]
    {hp : Corollary53Admissible 1 1 p} {hX : 2 ≤ p.X} {budget delta : ℝ}
    (h : ActivePacketCertificateBridge delta hp hX budget) :
    PacketIndexedPaddedSourceCertificate p budget :=
  activePacketCertificate_of_expandedBudget
    hp (selectedHighTruncation p) h.truncation_ge_one hX h.delta_pos
    h.map_coefficient h.classifier_geometry h.component_size
    (active_expanded_rhs_le_of_high_fifth
      (delta := delta) (budget := budget) hX h.delta_pos
      (by have hn : 0 ≤ ordinaryError p.X p.H p.f p.beta p.eta := by
            unfold ordinaryError
            apply mul_nonneg
            · positivity
            · unfold ordinarySlidingMass
              exact MeasureTheory.integral_nonneg (fun x ↦ sq_nonneg _)
          have hb := h.ordinary_le
          linarith)
      (by simpa [dynamicLowNormalizationV3] using h.remainder_le)
      h.low_le h.high_mass h.ordinary_le)

theorem toPacketIndexedCertificate_nonempty
    {p : Corollary53Input} [NeZero p.q]
    {hp : Corollary53Admissible 1 1 p} {hX : 2 ≤ p.X} {budget delta : ℝ}
    (h : ActivePacketCertificateBridge delta hp hX budget) :
    Nonempty (PacketIndexedPaddedSourceCertificate p budget) :=
  ⟨toPacketIndexedCertificate h⟩

/-- Uniform producer contract. Choose delta after A and epsilon but before
X and all source data; every returned certificate uses that exact delta. -/
def UniformActivePacketCertificateBridge : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 / 240 ∧
    ∃ B D Cc : ℕ, ∃ Cred X₀ : ℝ,
      0 < Cred ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        1 < baseAperture epsilon X ∧
        baseAperture epsilon X ≤ X ∧
        ∀ q a : ℕ, ∀ beta : ℝ,
          let Q := (Real.log X) ^ B
          let H := baseAperture epsilon X
          let eta := 1 / Real.sqrt Q
          let p := mapCorollary53Input X H q a beta eta
          1 ≤ q → (q : ℝ) ≤ Q → a < q → a.Coprime q →
          |beta| ≤ 1 / ((q : ℝ) * Q) →
          2 * (Real.log X) ^ Cc < stationaryWidth beta H →
          ∃ hq₀ : q ≠ 0, ∃ hp : Corollary53Admissible 1 1 p,
            ∃ hX : 2 ≤ p.X,
              Nonempty (@ActivePacketCertificateBridge delta p ⟨hq₀⟩ hp hX
                (Cred * X * Real.rpow (Real.log X) (-A)))

/-- Active/free-`T` certificate bridge to the common packet-indexed consumer. -/
theorem uniformPacketIndexedPaddedFarBudget_of_activeBridge
    (hbridge : UniformActivePacketCertificateBridge) :
    UniformPacketIndexedPaddedFarBudget := by
  intro A epsilon hA hepsilon
  obtain ⟨delta, hdelta, hdeltaUpper, B, D, Cc, Cred, X₀, hCred, hX₀, hlocal⟩ :=
    hbridge A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cred, X₀, hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hHone, hHX, hpoint⟩ := hlocal X hXX₀
  refine ⟨hlog, hHone, hHX, ?_⟩
  dsimp only
  intro q a beta hq hqQ ha hcop hbeta hfar
  letI : NeZero q := ⟨Nat.ne_of_gt (by omega)⟩
  obtain ⟨hq₀, hp, hXp, hcert⟩ :=
    hpoint q a beta hq hqQ ha hcop hbeta hfar
  letI : NeZero (mapCorollary53Input X (baseAperture epsilon X) q a beta
      (1 / Real.sqrt ((Real.log X) ^ B))).q := ⟨hq₀⟩
  exact toPacketIndexedCertificate_nonempty hcert.some

end
end MRTProposition61HighCertificateBridgeV3

#print axioms MRTProposition61HighCertificateBridgeV3.toPacketIndexedCertificate
#print axioms MRTProposition61HighCertificateBridgeV3.uniformPacketIndexedPaddedFarBudget_of_activeBridge
