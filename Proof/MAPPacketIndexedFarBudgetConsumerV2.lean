import MAPPacketIndexedFarSourceV2

/-!
# Packet-indexed far-budget consumer

This is the packet-indexed analogue of the legacy shared-short far-budget
consumer.  It connects a literal `PacketIndexedPaddedSourceCertificate`
directly to `MAPFarSourceReduction`; no adapter back to the stronger
shared-short interface is used.
-/

namespace MAPPacketIndexedFarBudgetConsumerV2

open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPFarSourceWeldScaffold MAPPacketIndexedFarSourceV2
open MAPFarCircleSourceWeld MAPFarRationalApproximation
open MAPMajorArcWeld MAPAllCenterApertureTransfer MAPAllCenterNearFarTransfer
open PrimePairEndpoints

noncomputable section

/-- Uniform far-source budget stated at the literal packet-indexed source
interface.  All packet parameters may vary with the packet. -/
def UniformPacketIndexedPaddedFarBudget : Prop :=
  ∀ A epsilon : ℝ, 0 < A → 0 < epsilon →
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
          Nonempty (PacketIndexedPaddedSourceCertificate p
            (Cred * X * Real.rpow (Real.log X) (-A)))

/-- A packet-indexed literal budget implies the live MAP far-source
reduction.  The proof follows the public rational-lift and circle/source
comparison exactly, changing only the final certificate consumer. -/
theorem mapFarSourceReduction_one_of_uniformPacketIndexedPaddedFarBudget
    (hbudget : UniformPacketIndexedPaddedFarBudget) :
    MAPFarSourceReduction 1 1 := by
  intro A epsilon hA hepsilon
  obtain ⟨B, D, Cc, Cred, X₀, hCred, hX₀, hlocal⟩ :=
    hbudget A epsilon hA hepsilon
  refine ⟨B, D, Cc, Cred, X₀, hCred, hX₀, ?_⟩
  intro X hXX₀
  obtain ⟨hlog, hHone, hHX, hcell⟩ := hlocal X hXX₀
  refine ⟨hlog, ?_⟩
  intro center houtside
  let Q := (Real.log X) ^ B
  let H := baseAperture epsilon X
  let eta := 1 / Real.sqrt Q
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact one_le_pow₀ hlog
  have hHpos : 0 < H := by dsimp [H]; linarith
  obtain ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta, hfar⟩ :=
    exists_far_reduced_rational_lift
      (Q := Q) (H := H) (B := B) (Cc := Cc)
      (epsilon := epsilon) (X := X) rfl rfl hQ hHpos center houtside
  refine ⟨q, a, beta, hq, hqQ, ha, hcop, hcenter, hbeta, hfar, ?_⟩
  let p := mapCorollary53Input X H q a beta eta
  have hp : Corollary53Admissible 1 1 p := by
    apply selectedMapInput_admissible_one hlog hQ hHone hHX hq hcop hbeta hfar
  refine ⟨hp, ?_, ?_⟩
  · have hcircle := centeredArc_primeEnergy_le_mapSourceEnergy
      (X := X) (H := H) (beta := beta) (eta := eta)
      (q := q) (a := a) hHone
    simpa [H, hcenter] using! hcircle
  · have hcert : Nonempty (PacketIndexedPaddedSourceCertificate p
        (Cred * X * Real.rpow (Real.log X) (-A))) := by
      simpa [p, Q, H, eta] using
        (hcell q a beta hq hqQ ha hcop hbeta hfar)
    obtain ⟨cert⟩ := hcert
    exact sourceRHS_le_of_packetIndexedCertificate (hq := hq) cert

end
end MAPPacketIndexedFarBudgetConsumerV2

#print axioms MAPPacketIndexedFarBudgetConsumerV2.mapFarSourceReduction_one_of_uniformPacketIndexedPaddedFarBudget
