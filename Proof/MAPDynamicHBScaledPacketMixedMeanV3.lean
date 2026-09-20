import MAPDynamicHBPacketIndexedCertificateV3
import MRTLemma215DynamicHighPacketMixedMeanV3

/-!
# Mixed mean for the actual Cauchy-scaled dynamic packet

The extra square-root branch weight introduced by the exact source Cauchy
step is combined algebraically with the Perron scale.  The certified mixed
mean theorem can therefore be applied without changing its hypotheses.
-/

namespace MAPDynamicHBScaledPacketMixedMeanV3

set_option maxHeartbeats 800000

open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPMRTCorollary25TypeD1LiteralWeld MAPHBPerronSourceData
open MAPFarAnnulusSourceToModel MAPFarAnnulusMRT
open HBPerronPacketIndexedSourceV2
open MAPDynamicHBScaledPacketSourceV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketMixedMeanV3

noncomputable section

theorem scaleCoeffFamily_padded_scaleNatCoefficient
    {q : ℕ} [NeZero q] (c s : ℝ) (f : ℕ → ℂ) :
    scaleCoeffFamily c
        (paddedCharacterTwist q q le_rfl (scaleNatCoefficient s f)) =
      scaleCoeffFamily (c * s) (paddedCharacterTwist q q le_rfl f) := by
  funext chi n
  unfold scaleCoeffFamily paddedCharacterTwist zeroPadFamily zeroPad
    scaleNatCoefficient
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro psi hpsi
  split_ifs <;> push_cast <;> ring

/-- Mixed-mean envelope for the exact packet occurring in
`dynamicPacketIndexedDataV3`. -/
theorem exists_scaledAllPacket_mixedMass_boundV3
    {q : ℕ} [NeZero q]
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (perronScale t₀ T U : ℝ) (hT : 1 ≤ T) (hU : 1 ≤ U) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      characterPairMixedMass q
        (highPacketShortLengthV3 (allPacketGlobalV3 packet))
        (highPacketLongLengthV3 (allPacketGlobalV3 packet))
        (pairShortFamily (paddedCharacterTwist q q le_rfl
          (allPacketShortCoeffV3 packet)))
        (pairLongFamily (scaleCoeffFamily perronScale
          (paddedCharacterTwist q q le_rfl
            (scaledAllPacketLongCoeffV3 packet))))
        t₀ T U ≤
      U * (q : ℝ) ^ 2 * C *
        Real.log (2 *
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)) ^
          (4 * a + 2 * max 2
            ((highComplementV3 (allPacketGlobalV3 packet).1).length *
              (highComplementV3 (allPacketGlobalV3 packet).1).length) + 2) *
        (U * T +
          U * (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) +
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) + T) := by
  obtain ⟨a, C, hC, hbound⟩ := exists_highPacket_mixedMass_boundV3
    (q := q) (allPacketGlobalV3 packet)
    (perronScale * dynamicPacketScaleV3 (H₀ := H₀) hX hdelta packet.1)
      t₀ T U hT hU
  refine ⟨a, C, hC, ?_⟩
  have hg := scaleCoeffFamily_padded_scaleNatCoefficient
    (q := q) perronScale
    (dynamicPacketScaleV3 (H₀ := H₀) hX hdelta packet.1)
    (highPacketLongCoeffV3 (allPacketGlobalV3 packet))
  unfold scaledAllPacketLongCoeffV3 allPacketShortCoeffV3
  rw [hg]
  exact hbound

end
end MAPDynamicHBScaledPacketMixedMeanV3

#print axioms MAPDynamicHBScaledPacketMixedMeanV3.scaleCoeffFamily_padded_scaleNatCoefficient
#print axioms MAPDynamicHBScaledPacketMixedMeanV3.exists_scaledAllPacket_mixedMass_boundV3
