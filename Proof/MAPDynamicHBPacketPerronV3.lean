import MAPDynamicHBScaledPacketSourceV3

/-!
# Certified Perron removal for every dynamic high packet

The coefficient bound used by Corollary 2.5 is the literal finite sum of
coefficient norms on the product support.  Thus this layer is deterministic:
it uses no divisor estimate and introduces no new analytic premise.
-/

namespace MAPDynamicHBPacketPerronV3

set_option maxHeartbeats 800000

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

/-- A completely finite coefficient envelope on the exact product support. -/
def finiteLiteralConvolutionBound
    (N M : ℕ) (alpha beta : ℕ → ℂ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 (4 * N * M),
    ‖literalDirichletConvolution alpha beta n‖

theorem finiteLiteralConvolutionBound_nonneg
    (N M : ℕ) (alpha beta : ℕ → ℂ) :
    0 ≤ finiteLiteralConvolutionBound N M alpha beta := by
  unfold finiteLiteralConvolutionBound
  positivity

theorem norm_literalDirichletConvolution_le_finiteBound
    {N M : ℕ} (hN : 1 ≤ N) (hM : 1 ≤ M)
    {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta) (n : ℕ) :
    ‖literalDirichletConvolution alpha beta n‖ ≤
      finiteLiteralConvolutionBound N M alpha beta := by
  by_cases hn : n ∈ Finset.Icc 1 (4 * N * M)
  · unfold finiteLiteralConvolutionBound
    exact Finset.single_le_sum
      (fun m hm ↦ norm_nonneg (literalDirichletConvolution alpha beta m)) hn
  · have hoff : ¬ ((N : ℝ) * M ≤ (n : ℝ) ∧
        (n : ℝ) ≤ 4 * (N : ℝ) * M) := by
      intro hblock
      apply hn
      rw [Finset.mem_Icc]
      constructor
      · have hprod : 1 ≤ N * M := Nat.mul_pos hN hM
        exact hprod.trans (by exact_mod_cast hblock.1)
      · exact_mod_cast hblock.2
    rw [literalDirichletConvolution_eq_zero_off_productBlock
      (by positivity : (0 : ℝ) ≤ N) (by positivity : (0 : ℝ) ≤ M)
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta) hoff]
    simpa using finiteLiteralConvolutionBound_nonneg N M alpha beta

def dynamicPacketConvolutionBoundV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) : ℝ :=
  finiteLiteralConvolutionBound
    (highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (scaledAllPacketLongCoeffV3 packet) (allPacketShortCoeffV3 packet)

theorem dynamicPacketConvolutionBoundV3_nonneg
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    0 ≤ dynamicPacketConvolutionBoundV3 packet := by
  unfold dynamicPacketConvolutionBoundV3
  exact finiteLiteralConvolutionBound_nonneg _ _ _ _

theorem dynamicPacketConvolutionBoundV3_bound
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) (n : ℕ) :
    ‖literalDirichletConvolution
      (scaledAllPacketLongCoeffV3 packet) (allPacketShortCoeffV3 packet) n‖ ≤
        dynamicPacketConvolutionBoundV3 packet := by
  apply norm_literalDirichletConvolution_le_finiteBound
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).2.1.trans' (by omega)
  · exact (highPacket_geometryV3 (allPacketGlobalV3 packet)).1.trans' (by omega)
  · exact scaledAllPacketLongSupportV3 packet
  · exact allPacketShortSupportV3 packet

/-- Corollary 2.5 applied to one literal, scaled dynamic packet. -/
theorem exists_dynamicPacketPerronTransferV3
    {p : Corollary53Input} [NeZero p.q]
    {delta H₀ : ℝ} (hp : Corollary53Admissible 1 1 p)
    (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent)
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    ∃ K : ℝ, 0 < K ∧
      (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
          (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (openSourceLeft p.X) (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q ↦ fun n ↦ chi n)
            (scaledAllPacketLongCoeffV3 packet)
            (allPacketShortCoeffV3 packet))
          (stationaryWidth p.beta p.H) t) ^ 2) ≤
        perronCellError p.q
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (highPacketShortLengthV3 (allPacketGlobalV3 packet)) p.X
          (dynamicPacketConvolutionBoundV3 packet)
          (stationaryWidth p.beta p.H)
          (componentEndpoints p.X p.beta p.eta component).1
          (componentEndpoints p.X p.beta p.eta component).2 K +
        literalFactoredTypeDCell p.q
          (highPacketShortLengthV3 (allPacketGlobalV3 packet))
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (paddedCharacterTwist p.q p.q le_rfl
            (allPacketShortCoeffV3 packet))
          (scaleCoeffFamily (perronCellScale K p.X)
            (paddedCharacterTwist p.q p.q le_rfl
              (scaledAllPacketLongCoeffV3 packet)))
          ((componentEndpoints p.X p.beta p.eta component).1 - p.X)
          ((componentEndpoints p.X p.beta p.eta component).2 + p.X)
          (stationaryWidth p.beta p.H) := by
  have hgeom := highPacket_geometryV3 (allPacketGlobalV3 packet)
  have hH : 0 ≤ p.H := le_trans (by norm_num) hp.1
  have hX0 : 0 ≤ p.X := by linarith
  exact literalTypeD1_component95_to_paddedCell
    (by omega : 1 ≤ highPacketLongLengthV3 (allPacketGlobalV3 packet))
    (by omega : 1 ≤ highPacketShortLengthV3 (allPacketGlobalV3 packet))
    (by linarith : 1 ≤ p.X)
    (dynamicPacketConvolutionBoundV3_nonneg packet)
    (by unfold stationaryWidth; positivity)
    (MAPMRTProposition51Source.componentEndpoints_mono
      (beta := p.beta) hX0 hp.2.2.2.2.1 hp.2.2.2.2.2.1 component)
    (scaledAllPacketLongSupportV3 packet)
    (allPacketShortSupportV3 packet)
    (dynamicPacketConvolutionBoundV3_bound packet)

end
end MAPDynamicHBPacketPerronV3

#print axioms MAPDynamicHBPacketPerronV3.norm_literalDirichletConvolution_le_finiteBound
#print axioms MAPDynamicHBPacketPerronV3.exists_dynamicPacketPerronTransferV3
