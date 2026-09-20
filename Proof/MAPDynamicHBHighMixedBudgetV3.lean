import MAPDynamicHBScaledPacketMixedMeanV3

/-!
# Pointwise high-packet mixed-mean budget

This module applies the certified mixed-mean theorem to the exact cells in
`dynamicPacketIndexedDataV3` and sums the resulting literal packetwise
majorants.  It does not claim a uniform logarithmic exponent; that final
uniformity ledger remains visible in the chosen packet exponents below.
-/

namespace MAPDynamicHBHighMixedBudgetV3

set_option maxHeartbeats 1000000

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPMRTProposition51Source MAPFarAnnulusSourceToModel MAPFarAnnulusMRT
open MAPHBPerronSourceData MAPPacketIndexedFarSourceV2
open MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBPacketIndexedDataV3
open MAPDynamicHBPerronCellWeldV3 MAPDynamicHBScaledPacketMixedMeanV3
open MRTLemma215DynamicHighPacketIndexV3

noncomputable section

def dynamicPacketCenterV3
    (p : Corollary53Input) (component : OuterComponent) : ℝ :=
  (((componentEndpoints p.X p.beta p.eta component).1 - p.X) +
    ((componentEndpoints p.X p.beta p.eta component).2 + p.X)) / 2

def dynamicPacketWindowV3
    (p : Corollary53Input) (component : OuterComponent) : ℝ :=
  ((componentEndpoints p.X p.beta p.eta component).2 + p.X) -
    ((componentEndpoints p.X p.beta p.eta component).1 - p.X) +
      2 * stationaryWidth p.beta p.H

theorem one_le_dynamicPacketWindowV3
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent) :
    1 ≤ dynamicPacketWindowV3 p component := by
  have hX0 : 0 ≤ p.X := by linarith
  have hend := componentEndpoints_mono (beta := p.beta) hX0
    hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
  unfold dynamicPacketWindowV3
  linarith

def dynamicPacketMixedMassV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) : ℝ :=
  characterPairMixedMass p.q
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (pairShortFamily (paddedCharacterTwist p.q p.q le_rfl
      (allPacketShortCoeffV3 packet)))
    (pairLongFamily (scaleCoeffFamily
      (perronCellScale
        (dynamicPacketPerronKV3 hp hX hdelta component packet) p.X)
      (paddedCharacterTwist p.q p.q le_rfl
        (scaledAllPacketLongCoeffV3 packet))))
    (dynamicPacketCenterV3 p component)
    (dynamicPacketWindowV3 p component)
    (stationaryWidth p.beta p.H)

def dynamicPacketMixedExistenceV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) :=
  exists_scaledAllPacket_mixedMass_boundV3
    (q := p.q) (X := p.X) (delta := delta) (H₀ := H₀)
    (hX := hX) (hdelta := hdelta) packet
    (perronCellScale
      (dynamicPacketPerronKV3 hp hX hdelta component packet) p.X)
    (dynamicPacketCenterV3 p component)
    (dynamicPacketWindowV3 p component)
    (stationaryWidth p.beta p.H)
    (one_le_dynamicPacketWindowV3 hp hX hU component) hU

def dynamicPacketMixedExponentV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) : ℕ :=
  Classical.choose
    (dynamicPacketMixedExistenceV3 (H₀ := H₀) hp hX hdelta hU component packet)

def dynamicPacketMixedConstantV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) : ℝ :=
  Classical.choose (Classical.choose_spec
    (dynamicPacketMixedExistenceV3 (H₀ := H₀) hp hX hdelta hU component packet))

theorem dynamicPacketMixedConstantV3_pos
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) :
    0 < dynamicPacketMixedConstantV3 hp hX hdelta hU component packet := by
  exact (Classical.choose_spec (Classical.choose_spec
    (dynamicPacketMixedExistenceV3 (H₀ := H₀) hp hX hdelta hU component packet))).1

def dynamicPacketMixedMajorantV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) : ℝ :=
  let M := highPacketShortLengthV3 (allPacketGlobalV3 packet)
  let N := highPacketLongLengthV3 (allPacketGlobalV3 packet)
  let r := (highComplementV3 (allPacketGlobalV3 packet).1).length
  let a := dynamicPacketMixedExponentV3 hp hX hdelta hU component packet
  let C := dynamicPacketMixedConstantV3 hp hX hdelta hU component packet
  stationaryWidth p.beta p.H * (p.q : ℝ) ^ 2 * C *
    Real.log (2 * (M : ℝ) * (N : ℝ)) ^
      (4 * a + 2 * max 2 (r * r) + 2) *
    (stationaryWidth p.beta p.H * dynamicPacketWindowV3 p component +
      stationaryWidth p.beta p.H * (N : ℝ) +
      (M : ℝ) * (N : ℝ) + dynamicPacketWindowV3 p component)

theorem dynamicPacketMixedMassV3_le_majorant
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H)
    (component : OuterComponent)
    (packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta) :
    dynamicPacketMixedMassV3 hp hX hdelta component packet ≤
      dynamicPacketMixedMajorantV3 hp hX hdelta hU component packet := by
  exact (Classical.choose_spec (Classical.choose_spec
    (dynamicPacketMixedExistenceV3 (H₀ := H₀) hp hX hdelta hU component packet))).2

/-- Exact finite aggregation of the certified packetwise mixed-mean bounds.
The chosen exponent and constant remain attached to the source packet, so the
later uniformity step cannot silently promote pointwise choices. -/
theorem sum_dynamicPacketMixedMassV3_le_majorants
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H) :
    (∑ component : OuterComponent,
      ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
        dynamicPacketMixedMassV3 hp hX hdelta component packet) ≤
      ∑ component : OuterComponent,
        ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
          dynamicPacketMixedMajorantV3 hp hX hdelta hU component packet := by
  apply Finset.sum_le_sum
  intro component hcomponent
  exact Finset.sum_le_sum fun packet hpacket ↦
    dynamicPacketMixedMassV3_le_majorant hp hX hdelta hU component packet

/-- The complete mixed-cell sum appearing in the packet-indexed expanded
source RHS for the dynamic data. -/
def dynamicIndexedMixedCellTotalV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) : ℝ :=
  let d := dynamicPacketIndexedDataV3 (H₀ := H₀) hp hX hdelta
  ∑ component : OuterComponent, ∑ branch : CutoffBranch,
    ∑ i : Fin (d.blockCount component branch),
      2 * characterPairMixedMass
        (d.q component branch i) (d.shortLength component branch i)
        (d.longLength component branch i)
        (pairShortFamily (d.beta component branch i))
        (pairLongFamily (d.g component branch i))
        ((d.a component branch i + d.b component branch i) / 2)
        ((d.b component branch i - d.a component branch i) +
          2 * d.U component branch i) (d.U component branch i)

theorem dynamicIndexedMixedCellTotalV3_eq
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    dynamicIndexedMixedCellTotalV3 (H₀ := H₀) hp hX hdelta =
      16 * ∑ component : OuterComponent,
        ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
          dynamicPacketMixedMassV3 hp hX hdelta component packet := by
  unfold dynamicIndexedMixedCellTotalV3
  dsimp [dynamicPacketIndexedDataV3]
  change (∑ component : OuterComponent, ∑ branch : CutoffBranch,
      ∑ i : Fin (Fintype.card
        (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
        2 * dynamicPacketMixedMassV3 hp hX hdelta component
          (dynamicPacketOfFinV3 hX hdelta i)) = _
  have hinner : ∀ component : OuterComponent,
      (∑ i : Fin (Fintype.card
          (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
        2 * dynamicPacketMixedMassV3 hp hX hdelta component
          (dynamicPacketOfFinV3 hX hdelta i)) =
        2 * ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
          dynamicPacketMixedMassV3 hp hX hdelta component packet := by
    intro component
    calc
      (∑ i : Fin (Fintype.card
          (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
        2 * dynamicPacketMixedMassV3 hp hX hdelta component
          (dynamicPacketOfFinV3 hX hdelta i)) =
          2 * ∑ i : Fin (Fintype.card
            (DynamicAllPacketsV3 (H₀ := H₀) hX hdelta)),
            dynamicPacketMixedMassV3 hp hX hdelta component
              (dynamicPacketOfFinV3 hX hdelta i) := by
            rw [Finset.mul_sum]
      _ = 2 * ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
          dynamicPacketMixedMassV3 hp hX hdelta component packet := by
            rw [sum_dynamicPacketOfFinV3 (H₀ := H₀) hX hdelta]
  simp_rw [hinner]
  simp
  have hcard : Fintype.card CutoffBranch = 8 := by decide
  rw [hcard]
  push_cast
  simp_rw [show ∀ x : ℝ, 8 * (2 * x) = 16 * x by intro x; ring]
  rw [Finset.mul_sum]

theorem dynamicIndexedMixedCellTotalV3_le_majorants
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (hU : 1 ≤ stationaryWidth p.beta p.H) :
    dynamicIndexedMixedCellTotalV3 (H₀ := H₀) hp hX hdelta ≤
      16 * ∑ component : OuterComponent,
        ∑ packet : DynamicAllPacketsV3 (H₀ := H₀) hX hdelta,
          dynamicPacketMixedMajorantV3 hp hX hdelta hU component packet := by
  rw [dynamicIndexedMixedCellTotalV3_eq]
  apply mul_le_mul_of_nonneg_left
    (sum_dynamicPacketMixedMassV3_le_majorants hp hX hdelta hU)
  norm_num

end
end MAPDynamicHBHighMixedBudgetV3

#print axioms MAPDynamicHBHighMixedBudgetV3.dynamicPacketMixedMassV3_le_majorant
#print axioms MAPDynamicHBHighMixedBudgetV3.sum_dynamicPacketMixedMassV3_le_majorants
#print axioms MAPDynamicHBHighMixedBudgetV3.dynamicIndexedMixedCellTotalV3_eq
#print axioms MAPDynamicHBHighMixedBudgetV3.dynamicIndexedMixedCellTotalV3_le_majorants
