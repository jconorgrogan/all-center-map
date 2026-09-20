import MRTLemma215DynamicTypeIICellPruningV3
import MRTLemma215DynamicPacketSourceBoundRefinedV3
import MAPDynamicHBPacketPerronRefinedV3

/-! # Literal sharp-mask pruning of dynamic high packets

The active predicate is nonvanishing of the original masked convolution.
The HB scalar already present in the short coefficient and the refined
packet scale already present in the long coefficient are retained.
-/

namespace MRTLemma215DynamicHighCellPruningV3

open scoped BigOperators ArithmeticFunction
open MeasureTheory
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1IntegratedWeld MAPMRTCorollary25Minkowski
open MAPMRTCorollary53Source MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicHighPacketAggregateV3
open MRTLemma215DynamicHighPacketFlattenV3
open MRTLemma215DynamicPacketSourceBoundRefinedV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIICellPruningV3
open MRTLemma215OpenIntervalCutoffV3
open MAPDynamicHBScaledPacketSourceV3
open MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBPacketPerronRefinedV3

noncomputable section

/-- The original short HB scalar remains inside the literal mask. -/
def activeHighPacketsV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) (K : ℕ) :
    Finset (DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) := by
  classical
  exact Finset.univ.filter fun packet =>
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (highPacketShortCoeffV3 packet) (highPacketLongCoeffV3 packet)) ≠ 0

@[simp] theorem mem_activeHighPacketsV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    packet ∈ activeHighPacketsV3 hX hdelta K ↔
      intervalCutoff (openSourceLeft X) (2 * X)
        (literalDirichletConvolution
          (highPacketShortCoeffV3 packet) (highPacketLongCoeffV3 packet)) ≠ 0 := by
  classical
  simp [activeHighPacketsV3]

theorem highPacket_nonzero_product_boundsV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (hnonzero : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (highPacketShortCoeffV3 packet) (highPacketLongCoeffV3 packet)) ≠ 0) :
    X < 4 * (highPacketShortLengthV3 packet : ℝ) *
        (highPacketLongLengthV3 packet : ℝ) ∧
      (highPacketShortLengthV3 packet : ℝ) *
        (highPacketLongLengthV3 packet : ℝ) ≤ 2 * X :=
  nonzero_intervalCutoff_literalConvolution_product_bounds (by linarith)
    (highPacket_supportV3 packet).1 (highPacket_supportV3 packet).2 hnonzero

theorem highPacketConvolution_eq_literalV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) :
    (highPacketConvolutionV3 packet : ℕ → ℂ) =
      literalDirichletConvolution
        (highPacketShortCoeffV3 packet) (highPacketLongCoeffV3 packet) := by
  funext n
  exact arithmetic_mul_apply_eq_literalDirichletConvolution _ _ n

/-- No integrability or interval-orientation premise is needed for zero. -/
theorem componentIntegral_zero_coeff
    (X H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (0 : ℕ → ℂ) beta eta component = 0 := by
  simp [componentIntegral, characterWindow, criticalDirichletPolynomial]

theorem inactiveHighPacket_mask_eq_zeroV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (hinactive : packet ∉ activeHighPacketsV3 hX hdelta K) :
    intervalCutoff (openSourceLeft X) (2 * X)
      (highPacketConvolutionV3 packet) = 0 := by
  rw [highPacketConvolution_eq_literalV3]
  simpa only [mem_activeHighPacketsV3, not_not] using hinactive

theorem inactiveHighPacket_componentIntegral_eq_zeroV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (hinactive : packet ∉ activeHighPacketsV3 hX hdelta K)
    (H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    componentIntegral X H q₀ q₁
      (intervalCutoff (openSourceLeft X) (2 * X) (highPacketConvolutionV3 packet))
      beta eta component = 0 := by
  rw [inactiveHighPacket_mask_eq_zeroV3 packet hinactive]
  exact componentIntegral_zero_coeff _ _ _ _ _ _ _

/-- Weighted sums restrict exactly; their original weights are untouched. -/
theorem weighted_highPacket_integral_sum_eq_activeV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta} {K : ℕ}
    (weight : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K → ℝ)
    (H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    (∑ packet, weight packet * componentIntegral X H q₀ q₁
      (intervalCutoff (openSourceLeft X) (2 * X) (highPacketConvolutionV3 packet))
      beta eta component) =
    ∑ packet ∈ activeHighPacketsV3 hX hdelta K,
      weight packet * componentIntegral X H q₀ q₁
        (intervalCutoff (openSourceLeft X) (2 * X) (highPacketConvolutionV3 packet))
        beta eta component := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro packet _ hn
  rw [inactiveHighPacket_componentIntegral_eq_zeroV3 packet hn]
  simp

def activeBranchHighPacketsV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :
    Finset (DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) := by
  classical
  exact Finset.univ.filter fun packet =>
    branchHighPacketToGlobalV3 packet ∈ activeHighPacketsV3 hX hdelta K

@[simp] theorem mem_activeBranchHighPacketsV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    {K : ℕ} {branch : Fin K}
    (packet : DynamicBranchHighPacketIndexV3 (H₀ := H₀) hX hdelta branch) :
    packet ∈ activeBranchHighPacketsV3 hX hdelta branch ↔
      branchHighPacketToGlobalV3 packet ∈ activeHighPacketsV3 hX hdelta K := by
  classical
  simp [activeBranchHighPacketsV3]

/-- The literal source high coefficient is the sum of exactly its active masks. -/
theorem dynamicBranchHighSumCoeff_eq_activeV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K : ℕ} (branch : Fin K) :
    dynamicBranchHighSumCoeffV3 (H₀ := H₀) hX hdelta branch = fun n =>
      ∑ packet ∈ activeBranchHighPacketsV3 (H₀ := H₀) hX hdelta branch,
        intervalCutoff (openSourceLeft X) (2 * X)
          (branchHighPacketConvolutionV3 packet) n := by
  classical
  funext n
  unfold dynamicBranchHighSumCoeffV3
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro packet _ hn
  have hg : branchHighPacketToGlobalV3 packet ∉ activeHighPacketsV3 hX hdelta K := by
    simpa only [mem_activeBranchHighPacketsV3] using hn
  have hz := inactiveHighPacket_mask_eq_zeroV3 (branchHighPacketToGlobalV3 packet) hg
  change intervalCutoff (openSourceLeft X) (2 * X)
    (highPacketConvolutionV3 (branchHighPacketToGlobalV3 packet)) n = 0
  rw [hz]
  rfl

/-- The refined packet scale is included in this activity test. -/
def activeScaledHighPacketsRefinedV3
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta) :
    Finset (DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) := by
  classical
  exact Finset.univ.filter fun packet =>
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)) ≠ 0

@[simp] theorem mem_activeScaledHighPacketsRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta) :
    packet ∈ activeScaledHighPacketsRefinedV3 hX hdelta ↔
      intervalCutoff (openSourceLeft X) (2 * X)
        (literalDirichletConvolution
          (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)) ≠ 0 := by
  classical
  simp [activeScaledHighPacketsRefinedV3]

theorem scaledHighPacket_nonzero_product_boundsRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hnonzero : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)) ≠ 0) :
    X < 4 * (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) *
        (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) ∧
      (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) *
        (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) ≤ 2 * X :=
  nonzero_intervalCutoff_literalConvolution_product_bounds (by linarith)
    (scaledAllPacketLongSupportRefinedV3 packet) (allPacketShortSupportV3 packet) hnonzero

theorem inactiveScaledHighPacket_componentIntegral_eq_zeroRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hinactive : packet ∉ activeScaledHighPacketsRefinedV3 hX hdelta)
    (H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    componentIntegral X H q₀ q₁
      (intervalCutoff (openSourceLeft X) (2 * X)
        (literalDirichletConvolution
          (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)))
      beta eta component = 0 := by
  have hz : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)) = 0 := by
    simpa only [mem_activeScaledHighPacketsRefinedV3, not_not] using hinactive
  rw [hz]
  exact componentIntegral_zero_coeff _ _ _ _ _ _ _

theorem weighted_scaledHighPacket_integral_sum_eq_activeRefinedV3
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (weight : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta → ℝ)
    (H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    (∑ packet, weight packet * componentIntegral X H q₀ q₁
      (intervalCutoff (openSourceLeft X) (2 * X)
        (literalDirichletConvolution
          (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)))
      beta eta component) =
    ∑ packet ∈ activeScaledHighPacketsRefinedV3 hX hdelta,
      weight packet * componentIntegral X H q₀ q₁
        (intervalCutoff (openSourceLeft X) (2 * X)
          (literalDirichletConvolution
            (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)))
        beta eta component := by
  classical
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro packet _ hn
  rw [inactiveScaledHighPacket_componentIntegral_eq_zeroRefinedV3 packet hn]
  simp

/-- Vanishing is established before Perron and survives every character twist. -/
theorem typeD1ClippedNorm_eq_zero_of_mask_eq_zero
    {Chi : Type*} (N M X1 X2 : ℝ) (phase : Chi → ℕ → ℂ)
    (alpha beta : ℕ → ℂ)
    (hzero : intervalCutoff X1 X2 (literalDirichletConvolution alpha beta) = 0)
    (chi : Chi) (t : ℝ) :
    typeD1ClippedNorm N M X1 X2 phase alpha beta chi t = 0 := by
  unfold typeD1ClippedNorm
  rw [intervalCutoff_characterTwist, hzero]
  simp [characterTwist, halfLineDirichletPolynomial]

theorem inactiveScaledHighPacket_clippedMass_eq_zeroRefinedV3
    (p : Corollary53Input) {delta H₀ : ℝ}
    {hX : 2 ≤ p.X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (hinactive : packet ∉ activeScaledHighPacketsRefinedV3 hX hdelta)
    (component : OuterComponent) :
    (∫ t in (componentEndpoints p.X p.beta p.eta component).1..
      (componentEndpoints p.X p.beta p.eta component).2,
      (characterMovingMass
        (typeD1ClippedNorm
          (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
          (openSourceLeft p.X) (2 * p.X)
          (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
          (scaledAllPacketLongCoeffRefinedV3 packet)
          (allPacketShortCoeffV3 packet))
        (stationaryWidth p.beta p.H) t) ^ 2) = 0 := by
  have hz : intervalCutoff (openSourceLeft p.X) (2 * p.X)
      (literalDirichletConvolution
        (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet)) = 0 := by
    simpa only [mem_activeScaledHighPacketsRefinedV3, not_not] using hinactive
  have hnorm := typeD1ClippedNorm_eq_zero_of_mask_eq_zero
    (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
    (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
    (openSourceLeft p.X) (2 * p.X)
    (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
    (scaledAllPacketLongCoeffRefinedV3 packet) (allPacketShortCoeffV3 packet) hz
  simp [characterMovingMass, movingIntegral, hnorm]

/-- The exact refined source mass, with its original scale, restricted before
any Perron upper bound is introduced. -/
theorem dynamicAllScaledHighMassRefined_eq_active
    (p : Corollary53Input) {delta H₀ : ℝ}
    (hX : 2 ≤ p.X) (hdelta : 0 < delta) (component : OuterComponent) :
    dynamicAllScaledHighMassRefinedV3 p delta H₀ hX hdelta component =
    ∑ packet ∈ activeScaledHighPacketsRefinedV3 (H₀ := H₀) hX hdelta,
      ∫ t in (componentEndpoints p.X p.beta p.eta component).1..
        (componentEndpoints p.X p.beta p.eta component).2,
        (characterMovingMass
          (typeD1ClippedNorm
            (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ)
            (openSourceLeft p.X) (2 * p.X)
            (fun chi : DirichletCharacter ℂ p.q => fun n => chi n)
            (scaledAllPacketLongCoeffRefinedV3 packet)
            (allPacketShortCoeffV3 packet))
          (stationaryWidth p.beta p.H) t) ^ 2 := by
  classical
  unfold dynamicAllScaledHighMassRefinedV3
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro packet _ hn
  exact inactiveScaledHighPacket_clippedMass_eq_zeroRefinedV3 p packet hn component

end
end MRTLemma215DynamicHighCellPruningV3

#print axioms MRTLemma215DynamicHighCellPruningV3.highPacket_nonzero_product_boundsV3
#print axioms MRTLemma215DynamicHighCellPruningV3.dynamicBranchHighSumCoeff_eq_activeV3
#print axioms MRTLemma215DynamicHighCellPruningV3.scaledHighPacket_nonzero_product_boundsRefinedV3
#print axioms MRTLemma215DynamicHighCellPruningV3.weighted_scaledHighPacket_integral_sum_eq_activeRefinedV3

#print axioms MRTLemma215DynamicHighCellPruningV3.dynamicAllScaledHighMassRefined_eq_active
