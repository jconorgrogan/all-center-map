import MRTLemma215DynamicHighPointwiseV3
import MRTLemma215DynamicHighSharpCoefficientBoundV3
import MRTLemma215DynamicHighCellPruningV3
import MRTLemma215DynamicHighCountV3
import MRTLemma215DynamicTypeIIParameterGeometryV3

namespace MRTLemma215DynamicHighUniformScaledCoefficientsV3
open Filter
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DynamicHighCountV3 MRTLemma215DynamicTypeIIGlobalCountV3
open PostA5HighStripSplitReductionFromFourthMoment
noncomputable section

/-- The literal square-root scale is controlled by a common polylogarithm.
The deliberately loose exponent avoids changing the source's exact weight. -/
theorem exists_refinedScale_polylog_bound (delta : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ R : ℕ, ∀ {X H₀ : ℝ}
      (hX : 3 ≤ X) (hX₂ : 2 ≤ X) (hdelta : 0 < delta)
      (branch : Fin (hbOrder delta)),
      dynamicPacketScaleRefinedV3 (H₀ := H₀) hX₂ hdelta branch ≤
        C * Real.log X ^ R := by
  obtain ⟨C, hC, R, hcard⟩ := exists_fixedOrder_branchHighPacket_card_bound (hbOrder delta)
  refine ⟨1 + 2 * hbOrder delta * C, by positivity, R, ?_⟩
  intro X H₀ hX hX₂ hdelta branch
  have hc := hcard (H₀ := H₀) hX hX₂ hdelta branch
  have hp : 1 ≤ Real.log X ^ R := one_le_pow₀ (log_one_le hX)
  have hs := dynamicPacketScaleRefinedV3_sq (H₀ := H₀) hX₂ hdelta branch
  have hn := dynamicPacketScaleRefinedV3_nonneg (H₀ := H₀) hX₂ hdelta branch
  have hw : dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta branch ≤
      2 * hbOrder delta * C * Real.log X ^ R := by
    unfold dynamicBranchHighWeightRefinedV3
    calc
      _ ≤ (2 * hbOrder delta) * (C * Real.log X ^ R) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  have hsle : dynamicPacketScaleRefinedV3 (H₀ := H₀) hX₂ hdelta branch ≤
      1 + dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX₂ hdelta branch := by
    nlinarith [sq_nonneg (dynamicPacketScaleRefinedV3 (H₀ := H₀) hX₂ hdelta branch - 1)]
  nlinarith

/-- A single threshold absorbs the branch-count scale for every packet. -/
theorem eventually_refinedScale_le_rpow (delta theta : ℝ) (htheta : 0 < theta) :
    ∀ᶠ X : ℝ in atTop, ∀ {H₀ : ℝ} (hX₂ : 2 ≤ X) (hdelta : 0 < delta)
      (branch : Fin (hbOrder delta)),
      dynamicPacketScaleRefinedV3 (H₀ := H₀) hX₂ hdelta branch ≤ Real.rpow X theta := by
  obtain ⟨C, hC, R, hb⟩ := exists_refinedScale_polylog_bound delta
  have he := eventually_const_mul_polylog_le_rpow C R theta hC.le htheta
  filter_upwards [he, eventually_ge_atTop 3] with X he hX
  intro H₀ hX₂ hdelta branch
  apply (hb hX hX₂ hdelta branch).trans
  simpa using he

/-- Uniformity reduction: a common unscaled pointwise product bound and the
literal branch-count scale give a common active sharp envelope. -/
theorem exists_active_sharp_bound_of_unscaled
    (delta theta : ℝ) (htheta : 0 < theta) (C : ℝ) (hC : 0 < C)
    (hpoint : ∀ {X H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
      (packet : MAPDynamicHBScaledPacketSourceV3.DynamicAllHighPacketIndexV3
        (H₀ := H₀) hX hdelta) (n : ℕ),
      ‖MAPMRTCorollary25TypeD1LiteralWeld.literalDirichletConvolution
        (MRTLemma215DynamicHighPacketIndexV3.highPacketLongCoeffV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet))
        (MRTLemma215DynamicHighPacketIndexV3.highPacketShortCoeffV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet)) n‖ ≤
      C * Real.rpow
        (4 * (MRTLemma215DynamicHighPacketIndexV3.highPacketLongLengthV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet) : ℝ) *
          (MRTLemma215DynamicHighPacketIndexV3.highPacketShortLengthV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet) : ℝ)) (theta / 2)) :
    ∃ D X₀ : ℝ, 0 < D ∧ 3 ≤ X₀ ∧
      ∀ {X H₀ : ℝ}, X₀ ≤ X → ∀ (hX : 2 ≤ X) (hdelta : 0 < delta)
      (packet : MAPDynamicHBScaledPacketSourceV3.DynamicAllHighPacketIndexV3
        (H₀ := H₀) hX hdelta),
      packet ∈ MRTLemma215DynamicHighCellPruningV3.activeScaledHighPacketsRefinedV3 hX hdelta →
      MRTLemma215DynamicHighSharpCoefficientBoundV3.sharpPacketConvolutionBoundRefinedV3 packet ≤
        D * Real.rpow X theta := by
  have he := eventually_refinedScale_le_rpow delta (theta / 2) (by positivity)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.1 he
  refine ⟨C * Real.rpow 8 (theta / 2), max 3 X₀, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), le_max_left _ _, ?_⟩
  intro X H₀ hlarge hX hdelta packet hactive
  have hXpos : 0 < X := by linarith
  have hscale := hX₀ X ((le_max_right _ _).trans hlarge) (H₀ := H₀) hX hdelta packet.1
  have hgeom := MRTLemma215DynamicHighCellPruningV3.scaledHighPacket_nonzero_product_boundsRefinedV3
    packet ((MRTLemma215DynamicHighCellPruningV3.mem_activeScaledHighPacketsRefinedV3 packet).1 hactive)
  have hraw := MRTLemma215DynamicHighSharpCoefficientBoundV3.sharpPacketConvolutionBoundRefinedV3_le
    packet (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _)) (hpoint packet)
  have hp : Real.rpow
        (4 * (MRTLemma215DynamicHighPacketIndexV3.highPacketLongLengthV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet) : ℝ) *
          (MRTLemma215DynamicHighPacketIndexV3.highPacketShortLengthV3
          (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet) : ℝ)) (theta / 2) ≤
      Real.rpow (8 * X) (theta / 2) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [hgeom.2]) (by positivity)
  calc
    _ ≤ _ := hraw
    _ ≤ Real.rpow X (theta / 2) * (C * Real.rpow (8 * X) (theta / 2)) :=
      mul_le_mul hscale (mul_le_mul_of_nonneg_left hp hC.le)
        (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))
        (Real.rpow_nonneg hXpos.le _)
    _ = (C * Real.rpow 8 (theta / 2)) * Real.rpow X theta := by
      have hm : Real.rpow (8 * X) (theta / 2) =
          Real.rpow 8 (theta / 2) * Real.rpow X (theta / 2) :=
        Real.mul_rpow (by norm_num) hXpos.le
      rw [hm]
      have hx : Real.rpow X (theta / 2) * Real.rpow X (theta / 2) = Real.rpow X theta := by
        have hadd : theta / 2 + theta / 2 = theta := by ring
        simpa only [hadd] using! (Real.rpow_add hXpos (theta / 2) (theta / 2)).symm
      calc
        _ = (C * Real.rpow 8 (theta / 2)) *
          (Real.rpow X (theta / 2) * Real.rpow X (theta / 2)) := by ring
        _ = _ := by rw [hx]


/-- The final sharp Perron coefficient constant and threshold precede `X`,
`H₀`, every branch, and every packet. Both original coefficient scalars remain. -/
theorem exists_active_sharpPacketConvolutionBoundRefinedV3
    (delta theta : ℝ) (hdelta : 0 < delta) (htheta : 0 < theta) :
    ∃ C X₀ : ℝ, 0 < C ∧ 3 ≤ X₀ ∧
      ∀ {X H₀ : ℝ}, X₀ ≤ X → ∀ (hX : 2 ≤ X)
      (packet : MAPDynamicHBScaledPacketSourceV3.DynamicAllHighPacketIndexV3
        (H₀ := H₀) hX hdelta),
      packet ∈ MRTLemma215DynamicHighCellPruningV3.activeScaledHighPacketsRefinedV3 hX hdelta →
      MRTLemma215DynamicHighSharpCoefficientBoundV3.sharpPacketConvolutionBoundRefinedV3 packet ≤
        C * Real.rpow X theta := by
  obtain ⟨C, hC, hpoint⟩ :=
    MRTLemma215DynamicHighPointwiseV3.exists_fixedOrder_highPacket_convolution_bound
      (hbOrder delta) (hbOrder_one hdelta) (theta / 2) (by positivity)
  obtain ⟨D, X₀, hD, hX₀, hb⟩ := exists_active_sharp_bound_of_unscaled delta theta htheta C hC
    (fun packet n ↦ hpoint (MAPDynamicHBScaledPacketSourceV3.allPacketGlobalV3 packet) n)
  exact ⟨D, X₀, hD, hX₀, fun hlarge hX packet hactive ↦ hb hlarge hX hdelta packet hactive⟩

end
end MRTLemma215DynamicHighUniformScaledCoefficientsV3
#print axioms MRTLemma215DynamicHighUniformScaledCoefficientsV3.eventually_refinedScale_le_rpow

#print axioms MRTLemma215DynamicHighUniformScaledCoefficientsV3.exists_active_sharpPacketConvolutionBoundRefinedV3
