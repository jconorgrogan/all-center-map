import MAPDynamicHBExpandedBudgetLedgerV3
import MAPPacketIndexedFarBudgetConsumerV2

/-!
# Termwise constructor for the dynamic packet-indexed far budget

The final expanded inequality is allocated across its five literal terms.
This prevents an opaque expanded-budget premise from hiding which analytic
branch remains open.  The constructor itself is finite algebra.
-/

namespace MAPDynamicHBTermwiseBudgetConstructorV3

set_option maxHeartbeats 1200000

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPFarAnnulusSourceToModel MAPFarAnnulusMRT
open MAPHBPerronSourceData MAPPacketIndexedFarSourceV2
open MAPPacketIndexedFarBudgetConsumerV2
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBPacketIndexedDataV3 MAPDynamicHBPerronCellWeldV3
open MAPDynamicHBExpandedBudgetLedgerV3 MAPDynamicHBHighMixedBudgetV3
open MRTLemma215DyadicPartition MRTLemma215DynamicFactorExtractionV3
open MRTLemma215HBExpansion

noncomputable section

def dynamicV3Normalization (p : Corollary53Input) : ℝ :=
  (divisorCount p.q : ℝ) ^ 4 /
    (p.q * stationaryWidth p.beta p.H ^ 2)

/-- Literal five-way allocation of the dynamic V3 expanded source budget. -/
structure DynamicV3TermwiseBudget
    {p : Corollary53Input} [NeZero p.q]
    (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (budget : ℝ) where
  delta : ℝ
  H0 : ℝ
  delta_pos : 0 < delta
  map_coefficient : p.f = mapMangoldtCoeff p.X
  classifier_geometry : Real.rpow p.X delta *
    (2 * Real.rpow p.X ((8 : ℝ)⁻¹)) ≤ 2 * H0
  component_size : ∀ (rawBranch : Fin (hbOrder delta))
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option
      (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) (rawBranch : ℕ))
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff p.X (hbOrder delta)⌋₊))) ((rawBranch : ℕ) + 1)),
    (2 : ℝ) ^ (dynamicComponentFactorList logIndex zbag mbag).length *
      Real.rpow p.X delta ≤ p.X
  small_remainder : dynamicV3Normalization p *
      (∑ component : OuterComponent, smallRemainderMass p component) ≤
    budget / 5
  low_types : dynamicV3Normalization p *
      (∑ component : OuterComponent,
        dynamicAllLowMassV3 p delta H0 hX delta_pos component) ≤
    budget / 5
  perron_errors : dynamicV3Normalization p *
      (∑ component : OuterComponent,
        ∑ packet : DynamicAllPacketsV3 (H₀ := H0) hX delta_pos,
          dynamicPacketCellErrorV3 hp hX delta_pos component packet) ≤
    budget / 5
  high_packets : dynamicV3Normalization p *
      dynamicIndexedMixedCellTotalV3 (H₀ := H0) hp hX delta_pos ≤
    budget / 5
  ordinary_error : ordinaryError p.X p.H p.f p.beta p.eta ≤ budget / 5

theorem expandedPacketIndexedSourceRHS_dynamicV3_le_of_termwise
    {p : Corollary53Input} [NeZero p.q]
    {hp : Corollary53Admissible 1 1 p} {hX : 2 ≤ p.X} {budget : ℝ}
    (parts : DynamicV3TermwiseBudget hp hX budget) :
    expandedPacketIndexedSourceRHS p
        (dynamicPacketIndexedDataV3 (H₀ := parts.H0)
          hp hX parts.delta_pos) ≤ budget := by
  rw [expandedPacketIndexedSourceRHS_dynamicV3_eq]
  unfold dynamicExpandedCoreV3
  have hsmall := parts.small_remainder
  have hlow := parts.low_types
  have hperron := parts.perron_errors
  have hhigh := parts.high_packets
  dsimp [dynamicV3Normalization] at hsmall hlow hperron hhigh
  have hexpand :
      (divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) *
          ((∑ component : OuterComponent, smallRemainderMass p component) +
            (∑ component : OuterComponent,
              (dynamicAllLowMassV3 p parts.delta parts.H0 hX
                  parts.delta_pos component +
                ∑ packet : DynamicAllPacketsV3
                    (H₀ := parts.H0) hX parts.delta_pos,
                  dynamicPacketCellErrorV3 hp hX parts.delta_pos
                    component packet)) +
            dynamicIndexedMixedCellTotalV3
              (H₀ := parts.H0) hp hX parts.delta_pos) +
          ordinaryError p.X p.H p.f p.beta p.eta =
        ((divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) *
          (∑ component : OuterComponent, smallRemainderMass p component)) +
        ((divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) *
          (∑ component : OuterComponent,
            dynamicAllLowMassV3 p parts.delta parts.H0 hX
              parts.delta_pos component)) +
        ((divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) *
          (∑ component : OuterComponent,
            ∑ packet : DynamicAllPacketsV3
                (H₀ := parts.H0) hX parts.delta_pos,
              dynamicPacketCellErrorV3 hp hX parts.delta_pos
                component packet)) +
        ((divisorCount p.q : ℝ) ^ 4 /
            (p.q * stationaryWidth p.beta p.H ^ 2) *
          dynamicIndexedMixedCellTotalV3
            (H₀ := parts.H0) hp hX parts.delta_pos) +
        ordinaryError p.X p.H p.f p.beta p.eta := by
    simp_rw [Finset.sum_add_distrib]
    ring
  rw [hexpand]
  linarith [hsmall, hlow, hperron, hhigh, parts.ordinary_error]

/-- The five literal term bounds construct the complete packet-indexed source
certificate. -/
def dynamicPacketIndexedCertificateV3_of_termwise
    {p : Corollary53Input} [NeZero p.q]
    {hp : Corollary53Admissible 1 1 p} {hX : 2 ≤ p.X} {budget : ℝ}
    (parts : DynamicV3TermwiseBudget hp hX budget) :
    PacketIndexedPaddedSourceCertificate p budget :=
  MAPDynamicHBPacketIndexedCertificateV3.dynamicPacketIndexedCertificateV3_of_expandedBudget
    hp hX parts.delta_pos parts.map_coefficient parts.classifier_geometry
    parts.component_size
    (expandedPacketIndexedSourceRHS_dynamicV3_le_of_termwise parts)

/-- Uniform source proposition with the five obligations exposed.  This is
the source-facing replacement for the opaque shared-short far budget. -/
def UniformDynamicV3TermwiseFarBudget : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
    ∃ B D Cc : ℕ, ∃ Cred X₀ : ℝ,
      0 < Cred ∧ 2 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X →
        1 ≤ Real.log X ∧
        1 < MAPAllCenterApertureTransfer.baseAperture epsilon X ∧
        MAPAllCenterApertureTransfer.baseAperture epsilon X ≤ X ∧
        ∀ q a : ℕ, ∀ beta : ℝ,
          let Q := (Real.log X) ^ B
          let H := MAPAllCenterApertureTransfer.baseAperture epsilon X
          let eta := 1 / Real.sqrt Q
          let p := mapCorollary53Input X H q a beta eta
          ∀ hq : (1 : ℕ) ≤ q, (q : ℝ) ≤ Q → a < q → a.Coprime q →
          |beta| ≤ 1 / ((q : ℝ) * Q) →
          2 * (Real.log X) ^ Cc < stationaryWidth beta H →
          ∃ hp : Corollary53Admissible 1 1 p,
            ∃ hX : 2 ≤ p.X,
              Nonempty (@DynamicV3TermwiseBudget p
                ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)⟩ hp hX
                (Cred * X * Real.rpow (Real.log X) (-A)))

theorem uniformPacketIndexedPaddedFarBudget_of_dynamicV3Termwise
    (hparts : UniformDynamicV3TermwiseFarBudget) :
    UniformPacketIndexedPaddedFarBudget := by
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, Cred, X₀, hCred, hX₀, hlocal⟩ :=
    hparts A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cred, X₀, hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hHone, hHX, hpoint⟩ := hlocal X hXX₀
  refine ⟨hlog, hHone, hHX, ?_⟩
  dsimp only
  intro q a beta hq hqQ ha hcop hbeta hfar
  letI : NeZero q := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hq)⟩
  obtain ⟨hp, hXp, parts⟩ :=
    hpoint q a beta hq hqQ ha hcop hbeta hfar
  let hpq : NeZero
      (mapCorollary53Input X
        (MAPAllCenterApertureTransfer.baseAperture epsilon X)
        q a beta (1 / Real.sqrt ((Real.log X) ^ B))).q := by
    dsimp [mapCorollary53Input]
    infer_instance
  exact ⟨@dynamicPacketIndexedCertificateV3_of_termwise
    (mapCorollary53Input X
      (MAPAllCenterApertureTransfer.baseAperture epsilon X)
      q a beta (1 / Real.sqrt ((Real.log X) ^ B))) hpq
    hp hXp (Cred * X * Real.rpow (Real.log X) (-A)) parts.some⟩

end
end MAPDynamicHBTermwiseBudgetConstructorV3

#print axioms MAPDynamicHBTermwiseBudgetConstructorV3.expandedPacketIndexedSourceRHS_dynamicV3_le_of_termwise
#print axioms MAPDynamicHBTermwiseBudgetConstructorV3.dynamicPacketIndexedCertificateV3_of_termwise
#print axioms MAPDynamicHBTermwiseBudgetConstructorV3.uniformPacketIndexedPaddedFarBudget_of_dynamicV3Termwise
