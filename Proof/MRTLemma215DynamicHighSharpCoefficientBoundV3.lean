import MAPDynamicHBPacketPerronRefinedV3

/-! # Sharp coefficient envelope for refined high packets

The old `finiteLiteralConvolutionBound` is an L1 sum. It is intentionally
unchanged. Perron only needs a pointwise envelope, so the free-height consumer
uses this finite maximum, with the original scaled long coefficient and signed
short coefficient intact.
-/
namespace MRTLemma215DynamicHighSharpCoefficientBoundV3
open scoped BigOperators
open MAPHBPerronSourceData
open MAPMRTCorollary25Instantiation MAPMRTCorollary25TypeD1LiteralWeld
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3 MAPDynamicHBPacketPerronRefinedV3
open MRTLemma215DynamicHighPacketIndexV3 MAPDynamicHBPacketPerronV3
noncomputable section

def finiteLiteralConvolutionMax (N M : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  (((Finset.Icc 1 (4 * N * M)).sup
    (fun n ↦ ‖literalDirichletConvolution alpha beta n‖₊) : NNReal) : ℝ)

theorem finiteLiteralConvolutionMax_nonneg (N M : ℕ) (alpha beta : ℕ → ℂ) :
    0 ≤ finiteLiteralConvolutionMax N M alpha beta := NNReal.coe_nonneg _

theorem finiteLiteralConvolutionMax_le {N M : ℕ} {alpha beta : ℕ → ℂ}
    {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ n ∈ Finset.Icc 1 (4 * N * M),
      ‖literalDirichletConvolution alpha beta n‖ ≤ B) :
    finiteLiteralConvolutionMax N M alpha beta ≤ B := by
  change (((Finset.Icc 1 (4 * N * M)).sup
    (fun n ↦ ‖literalDirichletConvolution alpha beta n‖₊) : NNReal) : ℝ) ≤ B
  exact_mod_cast (Finset.sup_le (fun n hn ↦
    (show ‖literalDirichletConvolution alpha beta n‖₊ ≤ ⟨B, hB⟩ from h n hn)))

theorem norm_literalDirichletConvolution_le_finiteMax
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M) {alpha beta : ℕ → ℂ}
    (ha : SupportedNatDyadic N alpha) (hb : SupportedNatDyadic M beta) (n : ℕ) :
    ‖literalDirichletConvolution alpha beta n‖ ≤
      finiteLiteralConvolutionMax N M alpha beta := by
  by_cases hn : n ∈ Finset.Icc 1 (4 * N * M)
  · unfold finiteLiteralConvolutionMax
    exact_mod_cast (Finset.le_sup (f := fun n ↦
      ‖literalDirichletConvolution alpha beta n‖₊) hn)
  · have hoff : ¬ ((N : ℝ) * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * (N : ℝ) * M) := by
      intro hblock
      apply hn
      rw [Finset.mem_Icc]
      constructor
      · have hp : 1 ≤ N * M := Nat.mul_pos hN hM
        exact hp.trans (by exact_mod_cast hblock.1)
      · exact_mod_cast hblock.2
    rw [literalDirichletConvolution_eq_zero_off_productBlock
      (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ M)
      (supportedDyadic_coe_of_supportedNatDyadic ha)
      (supportedDyadic_coe_of_supportedNatDyadic hb) hoff, norm_zero]
    exact finiteLiteralConvolutionMax_nonneg _ _ _ _

def sharpPacketConvolutionBoundRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  finiteLiteralConvolutionMax
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)

theorem sharpPacketConvolutionBoundRefinedV3_nonneg
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 ≤ sharpPacketConvolutionBoundRefinedV3 packet :=
  finiteLiteralConvolutionMax_nonneg _ _ _ _

theorem sharpPacketConvolutionBoundRefinedV3_bound
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) (n : ℕ) :
    ‖literalDirichletConvolution (scaledAllPacketLongCoeffRefinedV3 packet)
      (allPacketShortCoeffV3 packet) n‖ ≤ sharpPacketConvolutionBoundRefinedV3 packet := by
  apply norm_literalDirichletConvolution_le_finiteMax
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).2.1.trans' (by omega)
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).1.trans' (by omega)
  · exact scaledAllPacketLongSupportRefinedV3 packet
  · exact allPacketShortSupportV3 packet

theorem sharpPacketConvolutionBoundRefinedV3_le
    {X delta H₀ B : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hB : 0 ≤ B)
    (hb : ∀ n : ℕ, ‖literalDirichletConvolution
      (highPacketLongCoeffV3 (allPacketGlobalV3 packet))
      (highPacketShortCoeffV3 (allPacketGlobalV3 packet)) n‖ ≤ B) :
    sharpPacketConvolutionBoundRefinedV3 packet ≤
      dynamicPacketScaleRefinedV3 (H₀ := H₀) hX hdelta packet.1 * B := by
  apply finiteLiteralConvolutionMax_le
    (mul_nonneg (dynamicPacketScaleRefinedV3_nonneg hX hdelta packet.1) hB)
  intro n hn
  unfold scaledAllPacketLongCoeffRefinedV3 allPacketShortCoeffV3
  rw [HBPerronPacketIndexedSourceV2.literalDirichletConvolution_scale_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (dynamicPacketScaleRefinedV3_nonneg hX hdelta packet.1)]
  exact mul_le_mul_of_nonneg_left (hb n)
    (dynamicPacketScaleRefinedV3_nonneg hX hdelta packet.1)


/-- The new pointwise envelope never exceeds the original L1 envelope. -/
theorem sharpPacketConvolutionBoundRefinedV3_le_original
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    sharpPacketConvolutionBoundRefinedV3 packet ≤ dynamicPacketConvolutionBoundRefinedV3 packet := by
  apply finiteLiteralConvolutionMax_le (dynamicPacketConvolutionBoundRefinedV3_nonneg packet)
  exact fun n _ ↦ dynamicPacketConvolutionBoundRefinedV3_bound packet n

end
end MRTLemma215DynamicHighSharpCoefficientBoundV3
#print axioms MRTLemma215DynamicHighSharpCoefficientBoundV3.sharpPacketConvolutionBoundRefinedV3_bound
