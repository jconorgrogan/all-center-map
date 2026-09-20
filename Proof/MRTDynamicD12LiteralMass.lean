import MRTDynamicD12FactorExtraction
import MAPFinishDynamicLowTypesRefinedV3

/-! # Literal dynamic d1/d2 mass after sorted-tail extraction -/
namespace MRTDynamicD12LiteralMass

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicClassificationV3 MAPFinishDynamicThreeTypeTrace
open MAPFinishDynamicLowTypesRefinedV3 MAPDynamicHBSourcePacketBoundRefinedV3
open MRTDynamicD12FactorExtraction

noncomputable section

local instance (P : Prop) : Decidable P := Classical.propDecidable P

/-- Literal small-prefix times the remaining smooth tail, still source-masked. -/
def dynamicD12FactorizedCoeff
    {X : ℝ} (delta : ℝ) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) (n : ℕ) : ℂ :=
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
  if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
    (dynamicComponentScalar zbag mbag *
      (factorConvolution (factors.take s) * factorConvolution (factors.drop s))) n
  else 0

theorem dynamicD12FactorizedCoeff_eq_masked
    {X : ℝ} (hX : 1 ≤ X) (delta : ℝ) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    dynamicD12FactorizedCoeff delta logIndex zbag mbag =
      maskedDynamicComponentV3 logIndex zbag mbag := by
  funext n
  exact (maskedDynamicComponent_eq_prefix_mul_tail (delta := delta) hX hK
    logIndex zbag mbag n).symm

/-- The filter is the actual classifier outcome, not the raw HB branch. -/
def dynamicD12IsActive
    {X : ℝ} (delta H₀ : ℝ) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) : Prop :=
  ∃ j : Fin 8,
    dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag = .typeD j ∧
      ((j : ℕ) = 1 ∨ (j : ℕ) = 2)

/-- Every active term in the extracted mass has one or two actual smooth
shells, and its complementary prefix keeps the original small-product bound. -/
theorem activeD12_tail_spec
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (hdelta8 : delta < (8 : ℝ)⁻¹)
    (hgeom : Real.rpow X delta * (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hcut : 2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊) {k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) (k + 1))
    (hactive : dynamicD12IsActive delta H₀ logIndex zbag mbag) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
    ((factors.drop s).length = 1 ∨ (factors.drop s).length = 2) ∧
      (∀ f ∈ factors.drop s, IsSourceSmoothFactor X logIndex f) ∧
      (factorUpperProduct (factors.take s) : ℝ) ≤
        (2 : ℝ) ^ (factors.take s).length * Real.rpow X delta := by
  obtain ⟨j, hout, hj⟩ := hactive
  have hlen := typeD_tail_length logIndex zbag mbag j hout
  have hsmooth := typeD_tail_is_sourceSmooth hX hdelta
    (by norm_num : 1 ≤ (8 : ℕ)) hdelta8 hgeom hcut logIndex zbag mbag j hout
  have hprefix := smallPrefix_upperProduct_le (by linarith : 1 ≤ X) hdelta.le
    logIndex zbag mbag
  dsimp only at hlen hsmooth hprefix ⊢
  refine ⟨?_, hsmooth, hprefix.2⟩
  rw [hlen]
  exact hj

private theorem componentIntegral_zero
    (X H beta eta : ℝ) (q₀ q₁ : ℕ) (component : OuterComponent) :
    componentIntegral X H q₀ q₁ (fun _ : ℕ => (0 : ℂ)) beta eta component = 0 := by
  simp [componentIntegral, characterWindow, criticalDirichletPolynomial]

/-- Individual d1 and d2 masses are mutually exclusive. Their sum is exactly
the active masked factorized mass, with the original component endpoints. -/
theorem componentD12Mass_eq_factorized
    {p : Corollary53Input} (hX : 1 ≤ p.X) {delta H₀ : ℝ}
    {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff p.X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff p.X K⌋₊))) (k + 1)) (component : OuterComponent) :
    componentIntegral p.X p.H 1 p.q
      (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD1) p.beta p.eta component +
    componentIntegral p.X p.H 1 p.q
      (dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD2) p.beta p.eta component =
    if dynamicD12IsActive delta H₀ logIndex zbag mbag then
      componentIntegral p.X p.H 1 p.q
        (dynamicD12FactorizedCoeff delta logIndex zbag mbag) p.beta p.eta component
    else 0 := by
  classical
  rw [dynamicD12FactorizedCoeff_eq_masked hX delta hK]
  change componentIntegral p.X p.H 1 p.q
      (fun n => dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD1 n) p.beta p.eta component +
    componentIntegral p.X p.H 1 p.q
      (fun n => dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeD2 n) p.beta p.eta component = _
  unfold dynamicComponentRemainderV3
  cases hout : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag with
  | typeII =>
      simp [dynamicD12IsActive, hout, dynamicComponentRemainderV3, componentIntegral_zero]
  | vanishing =>
      simp [dynamicD12IsActive, hout, dynamicComponentRemainderV3, componentIntegral_zero]
  | typeD j =>
      by_cases hj1 : (j : ℕ) = 1
      · simp [dynamicD12IsActive, hout, dynamicComponentRemainderV3, hj1, componentIntegral_zero]
      · by_cases hj2 : (j : ℕ) = 2
        · simp [dynamicD12IsActive, hout, dynamicComponentRemainderV3, hj1, hj2, componentIntegral_zero]
        · simp [dynamicD12IsActive, hout, dynamicComponentRemainderV3, hj1, hj2, componentIntegral_zero]

/-- Actual finite extracted mass; all three source index bags remain explicit. -/
def dynamicD12ExtractedBranchMass
    (p : Corollary53Input) (delta H₀ : ℝ) {K : ℕ} (branch : Fin K)
    (component : OuterComponent) : ℝ := by
  classical
  exact ∑ logIndex : Fin (sourceDyadicCount (hbFactorCutoff p.X)),
    ∑ zbag ∈ dynamicLowZBagSetV3 p.X (branch : ℕ),
      ∑ mbag ∈ dynamicLowMBagSetV3 p.X K (branch : ℕ),
        if dynamicD12IsActive delta H₀ logIndex zbag mbag then
          componentIntegral p.X p.H 1 p.q
            (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
            p.beta p.eta component
        else 0

theorem rawComponentD12Mass_eq_extracted
    {p : Corollary53Input} (hX : 1 ≤ p.X) {delta H₀ : ℝ}
    {K : ℕ} (hK : 1 ≤ K) (branch : Fin K) (component : OuterComponent) :
    dynamicRawLowComponentMassV3 p delta H₀ branch .typeD1 component +
      dynamicRawLowComponentMassV3 p delta H₀ branch .typeD2 component =
      dynamicD12ExtractedBranchMass p delta H₀ branch component := by
  unfold dynamicRawLowComponentMassV3 dynamicD12ExtractedBranchMass
  simp_rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro logIndex hlog
  apply Finset.sum_congr rfl
  intro zbag hz
  apply Finset.sum_congr rfl
  intro mbag hm
  exact componentD12Mass_eq_factorized hX hK logIndex zbag mbag component

/-- The raw refined d1/d2 mass is now bounded by actual factored components.
The multiplier is the exact source Cauchy cardinality and fixed branch weight. -/
theorem dynamicBranchD12MassRefined_le_extracted
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) (branch : Fin (hbOrder delta)) :
    dynamicBranchD12MassRefinedV3 p delta H₀ hX hdelta component branch ≤
      dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
        (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta) (branch : ℕ) : ℝ) *
        dynamicD12ExtractedBranchMass p delta H₀ branch component := by
  have h1 := componentIntegral_dynamicRawBranchRemainderCoeffV3_le_components
    hp (delta := delta) (H₀ := H₀) branch .typeD1 component
  have h2 := componentIntegral_dynamicRawBranchRemainderCoeffV3_le_components
    hp (delta := delta) (H₀ := H₀) branch .typeD2 component
  have hsum := add_le_add h1 h2
  rw [← mul_add, rawComponentD12Mass_eq_extracted
    (by linarith : 1 ≤ p.X) (hbOrder_one hdelta)] at hsum
  unfold dynamicBranchD12MassRefinedV3
  have hweight : 0 ≤ dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) := by
    unfold dynamicBranchLowWeightRefinedV3
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hsum hweight

theorem dynamicAllD12MassRefined_le_extracted
    {p : Corollary53Input} (hp : Corollary53Admissible 1 1 p)
    {delta H₀ : ℝ} (hX : 2 ≤ p.X) (hdelta : 0 < delta)
    (component : OuterComponent) :
    dynamicAllD12MassRefinedV3 p delta H₀ hX hdelta component ≤
      ∑ branch : Fin (hbOrder delta),
        dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
          (dynamicLowComponentMultiplicityV3 p.X (hbOrder delta) (branch : ℕ) : ℝ) *
          dynamicD12ExtractedBranchMass p delta H₀ branch component := by
  exact Finset.sum_le_sum fun branch hbranch =>
    dynamicBranchD12MassRefined_le_extracted hp hX hdelta component branch

end
end MRTDynamicD12LiteralMass

#print axioms MRTDynamicD12LiteralMass.componentD12Mass_eq_factorized
#print axioms MRTDynamicD12LiteralMass.dynamicAllD12MassRefined_le_extracted
