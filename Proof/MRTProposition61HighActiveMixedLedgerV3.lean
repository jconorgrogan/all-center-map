import MRTProposition61HighUniformScaledMixedV3
import MRTProposition61HighParameterLedgerV3
import MRTProposition61HighFreePerronV3
import MRTProposition61HighActivePacketDataV3

/-! # Uniform normalized mixed ledger for the literal active free-T packets -/

namespace MRTProposition61HighActiveMixedLedgerV3

open scoped BigOperators
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTProposition51Source MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3 MAPDynamicHBCanonicalPerronConstantV3
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215DynamicHighCellPruningV3
open MRTProposition61HighUniformScaledMixedV3 MRTProposition61HighParameterLedgerV3
open MRTProposition61HighActivePacketDataV3

noncomputable section
set_option maxHeartbeats 1600000

def activeHighPacketMixedMass (p : Corollary53Input) [NeZero p.q]
    {delta H₀ : ℝ} (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  characterPairMixedMass p.q
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (pairShortFamily (paddedCharacterTwist p.q p.q le_rfl (allPacketShortCoeffV3 packet)))
    (pairLongFamily (scaleCoeffFamily (perronCellScale canonicalPerronKFour T)
      (paddedCharacterTwist p.q p.q le_rfl (scaledAllPacketLongCoeffRefinedV3 packet))))
    (((componentEndpoints p.X p.beta p.eta component).1 +
      (componentEndpoints p.X p.beta p.eta component).2) / 2)
    ((componentEndpoints p.X p.beta p.eta component).2 -
      (componentEndpoints p.X p.beta p.eta component).1 + 2 * T + 2 * stationaryWidth p.beta p.H)
    (stationaryWidth p.beta p.H)

/-- This is the actual free-truncation mixed mass, with the exact active mask
and normalization. The fixed-order `C,a` are chosen before all source inputs. -/
theorem exists_uniform_activeHighMixed_normalized_bound
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (p : Corollary53Input) [NeZero p.q] (hp : Corollary53Admissible 1 1 p)
        (H₀ T : ℝ) (hX : 2 ≤ p.X) (hT : 1 ≤ T)
        (hU : 1 ≤ stationaryWidth p.beta p.H) (component : OuterComponent)
        (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta),
        packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta →
        let U := stationaryWidth p.beta p.H
        let L := (componentEndpoints p.X p.beta p.eta component).2 -
          (componentEndpoints p.X p.beta p.eta component).1
        let M : ℝ := highPacketShortLengthV3 (allPacketGlobalV3 packet)
        let N : ℝ := highPacketLongLengthV3 (allPacketGlobalV3 packet)
        (divisorCount p.q : ℝ) ^ 4 / (p.q * U ^ 2) *
          activeHighPacketMixedMass p T hX hdelta component packet ≤
        perronCellScale canonicalPerronKFour T ^ 2 *
          dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
          ((divisorCount p.q : ℝ) ^ 4 * p.q * C * Real.log (2 * M * N) ^
            (4 * a + 2 * max 2 ((2 * hbOrder delta) * (2 * hbOrder delta)) + 2) *
            (2 * L + 4 * T + 4 * U + N + 2 * p.X / U)) := by
  obtain ⟨a, C, hC, hmean⟩ := exists_uniform_refinedPacketMixedMass_bound delta hdelta
  refine ⟨a, C, hC, ?_⟩
  intro p _ hp H₀ T hX hT hU component packet hactive
  dsimp only
  let U := stationaryWidth p.beta p.H
  let L := (componentEndpoints p.X p.beta p.eta component).2 -
    (componentEndpoints p.X p.beta p.eta component).1
  let M : ℝ := highPacketShortLengthV3 (allPacketGlobalV3 packet)
  let N : ℝ := highPacketLongLengthV3 (allPacketGlobalV3 packet)
  let E := 4 * a + 2 * max 2 ((2 * hbOrder delta) * (2 * hbOrder delta)) + 2
  let W := L + 2 * T + 2 * U
  have hL : 0 ≤ L := by
    have hm := componentEndpoints_mono (beta := p.beta) (by linarith : 0 ≤ p.X)
      hp.2.2.2.2.1 hp.2.2.2.2.2.1 component
    dsimp [L]; linarith
  have hW : 1 ≤ W := by dsimp [W, U]; linarith
  have hU0 : 0 < U := by dsimp [U]; linarith
  have hq : 0 < (p.q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p.q)
  have hgeometry := highPacket_geometryV3 (allPacketGlobalV3 packet)
  have hM : 2 ≤ M := by dsimp [M]; exact_mod_cast hgeometry.1
  have hN : 2 ≤ N := by dsimp [N]; exact_mod_cast hgeometry.2.1
  have hlog : 0 ≤ Real.log (2 * M * N) := Real.log_nonneg (by nlinarith)
  have hprod := (scaledHighPacket_nonzero_product_boundsRefinedV3 packet
    ((mem_activeScaledHighPacketsRefinedV3 packet).mp hactive)).2
  have hprod' : M * N ≤ 2 * p.X := by simpa only [M, N, mul_comm] using hprod
  have hmeanp := hmean p.q packet (perronCellScale canonicalPerronKFour T)
    (((componentEndpoints p.X p.beta p.eta component).1 +
      (componentEndpoints p.X p.beta p.eta component).2) / 2) W U hW hU
  have hnorm : 0 ≤ (divisorCount p.q : ℝ) ^ 4 / (p.q * U ^ 2) := by positivity
  have hm := mul_le_mul_of_nonneg_left hmeanp hnorm
  have hcore := normalized_high_core_le_free_truncation
    (D := (divisorCount p.q : ℝ) ^ 4) (q := (p.q : ℝ)) (U := U)
    (C := C * Real.log (2 * M * N) ^ E) (M := M) (N := N)
    (X := p.X) (L := L) (T := T)
    (by positivity) hq hU (mul_nonneg hC.le (pow_nonneg hlog _)) hL (by linarith) hprod'
  have hw : 0 ≤ perronCellScale canonicalPerronKFour T ^ 2 *
      dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 :=
    mul_nonneg (sq_nonneg _) (dynamicBranchHighWeightRefinedV3_nonneg hX hdelta packet.1)
  have hupper := mul_le_mul_of_nonneg_left hcore hw
  calc
    _ ≤ _ := hm
    _ ≤ _ := by
      convert hupper using 1 <;> dsimp [U, L, M, N, E, W, activeHighPacketMixedMass] <;> ring

/-- Exact connection to the adopted certificate's mixed total. The factor
sixteen is the public factor two times eight cutoff bookkeeping slots. -/
theorem activeIndexedMixedTotal_eq_sixteen_active_sum
    {p : Corollary53Input} [NeZero p.q] {delta H₀ : ℝ}
    (T : ℝ) (hX : 2 ≤ p.X) (hdelta : 0 < delta) :
    activeIndexedMixedTotal (H₀ := H₀) T hX hdelta =
      16 * ∑ component : OuterComponent,
        ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
          activeHighPacketMixedMass p T hX hdelta component packet := by
  classical
  have hcenter (component : OuterComponent) :
      (((componentEndpoints p.X p.beta p.eta component).1 - T) +
        ((componentEndpoints p.X p.beta p.eta component).2 + T)) / 2 =
      ((componentEndpoints p.X p.beta p.eta component).1 +
        (componentEndpoints p.X p.beta p.eta component).2) / 2 := by ring
  have hwindow (component : OuterComponent) :
      ((componentEndpoints p.X p.beta p.eta component).2 + T) -
        ((componentEndpoints p.X p.beta p.eta component).1 - T) +
        2 * stationaryWidth p.beta p.H =
      (componentEndpoints p.X p.beta p.eta component).2 -
        (componentEndpoints p.X p.beta p.eta component).1 + 2 * T +
        2 * stationaryWidth p.beta p.H := by ring
  unfold activeIndexedMixedTotal
  dsimp [activePacketIndexedData]
  simp_rw [hcenter, hwindow]
  change (∑ component : OuterComponent, ∑ branch : CutoffBranch,
      ∑ i : Fin (Fintype.card (ActivePackets (H₀ := H₀) hX hdelta)),
        2 * activeHighPacketMixedMass p T hX hdelta component (activePacketOfFin hX hdelta i)) = _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component hc
  have hcard : Fintype.card CutoffBranch = 8 := by decide
  simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_activePacketOfFin]
  ring

end
end MRTProposition61HighActiveMixedLedgerV3

#print axioms MRTProposition61HighActiveMixedLedgerV3.exists_uniform_activeHighMixed_normalized_bound

#print axioms MRTProposition61HighActiveMixedLedgerV3.activeIndexedMixedTotal_eq_sixteen_active_sum
