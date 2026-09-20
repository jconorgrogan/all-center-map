import MRTLemma215DynamicHighPacketIndexV3
import MRTLemma215DynamicHighProvenanceV3
import MRTLemma215DynamicTypeIIParameterGeometryV3

/-! # Literal high-packet scale savings at the selected classifier geometry -/

namespace MRTLemma215DynamicHighParameterScalesV3

open MAPDynamicHBSourceV3
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215DynamicHighProvenanceV3
open MRTLemma215DynamicTypeIIParameterGeometryV3

noncomputable section

/-- The actual selected smooth short factor is above the manuscript's
threshold; this is stronger than the generic `M≥2` packet condition. -/
theorem highPacketShortLength_gt_tailThreshold
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) {K : ℕ}
    (hgeom : Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    2 * Real.rpow X (1 / 8 : ℝ) < (highPacketShortLengthV3 packet : ℝ) := by
  obtain ⟨hs, hbound⟩ := typeD_selected_gt_tailThreshold hX hdelta
    (by norm_num : 1 ≤ 8) hgeom
    (rawLogIndexV3 packet.1.1) (rawZetaBagV3 packet.1.1) (rawMoebiusBagV3 packet.1.1)
    (highTypeIndexV3 packet.1) (highTypeIndexV3_outcome packet.1)
  simpa only [highPacketShortLengthV3, highSelectedFactorV3, highFactorsV3,
    highSelectedIndexV3, highScalesV3, one_div] using hbound

/-- On an active source packet, the long factor retains the power saving
`N<X^(7/8)`. The product hypothesis is exactly supplied by sharp-mask pruning. -/
theorem highPacketLongLength_lt_rpow
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) {K : ℕ}
    (hgeom : Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (hproduct : (highPacketShortLengthV3 packet : ℝ) *
      (highPacketLongLengthV3 packet : ℝ) ≤ 2 * X) :
    (highPacketLongLengthV3 packet : ℝ) < Real.rpow X (7 / 8 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hM := highPacketShortLength_gt_tailThreshold hX hdelta hgeom packet
  have hN : 0 < (highPacketLongLengthV3 packet : ℝ) := by
    unfold highPacketLongLengthV3
    positivity
  have hXN : Real.rpow X (1 / 8 : ℝ) * (highPacketLongLengthV3 packet : ℝ) < X := by
    have hm := mul_lt_mul_of_pos_right hM hN
    linarith
  have hrpow : X / Real.rpow X (1 / 8 : ℝ) = Real.rpow X (7 / 8 : ℝ) := by
    calc
      _ = Real.rpow X 1 / Real.rpow X (1 / 8 : ℝ) := by simp only [Real.rpow_eq_pow, Real.rpow_one]
      _ = Real.rpow X (1 - 1 / 8 : ℝ) := (Real.rpow_sub hX0 _ _).symm
      _ = _ := by norm_num
  rw [← hrpow]
  apply (lt_div_iff₀ (Real.rpow_pos_of_pos hX0 (1 / 8 : ℝ))).2
  simpa only [mul_comm] using hXN

end
end MRTLemma215DynamicHighParameterScalesV3

#print axioms MRTLemma215DynamicHighParameterScalesV3.highPacketShortLength_gt_tailThreshold
#print axioms MRTLemma215DynamicHighParameterScalesV3.highPacketLongLength_lt_rpow
