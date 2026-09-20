import MRTLemma215DynamicTypeIIDyadicV3
import MRTLemma215OpenIntervalCutoffV3
import MRTLemma215DynamicHighPacketFlattenV3

/-!
# Exact masked packetization of a dynamic Type-II component

The source mask is retained as a literal Corollary-2.5 interval cutoff on
each double-dyadic packet.  No clipped product is factored here.
-/

namespace MRTLemma215DynamicTypeIIMaskedPacketsV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215OpenIntervalCutoffV3
open MRTLemma215DynamicHighPacketFlattenV3

noncomputable section

/-- Multiplying a dyadic cell by the scalar attached to its HB component does
not enlarge support. -/
theorem scaledTypeIIPrefixCell_supported
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (leftFactors : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct leftFactors))) :
    SupportedNatDyadic (2 ^ (cell : ℕ))
      (scaledTypeIIPrefixCell zbag mbag leftFactors cell) := by
  intro n hn
  unfold scaledTypeIIPrefixCell
  rw [dynamicComponentScalar_mul_eq_smul]
  change (dynamicComponentScalarValue zbag mbag : ℂ) *
      factorListDyadicCell leftFactors cell n = 0
  rw [factorListDyadicCell_supported leftFactors cell n hn, mul_zero]

/-- Arithmetic-function multiplication is the same finite antidiagonal
convolution used by the certified Perron interface. -/
theorem arithmetic_mul_apply_eq_literalDirichletConvolution
    (alpha beta : ArithmeticFunction ℂ) (n : ℕ) :
    (alpha * beta) n = literalDirichletConvolution alpha beta n := by
  rw [ArithmeticFunction.mul_apply]
  rfl

/-- A component assigned to any other classifier outcome contributes
nothing to the Type-II remainder slot. -/
theorem dynamicComponentRemainderV3_typeII_eq_zero_of_outcome_ne
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag ≠
      .typeII) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
      logIndex zbag mbag .typeII = 0 := by
  funext n
  unfold dynamicComponentRemainderV3
  cases h : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag with
  | typeII => exact (houtcome h).elim
  | typeD j => simp [h]
  | vanishing => simp [h]

/-- A dyadic product block ending at or before `X` cannot meet the literal
open-left source interval `(X,2X]`. -/
theorem intervalCutoff_literalConvolution_eq_zero_of_four_mul_le
    {X : ℝ} (hX : 0 ≤ X) {N M : ℕ} {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (hsmall : 4 * (N : ℝ) * (M : ℝ) ≤ X) :
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution alpha beta) = 0 := by
  funext n
  unfold intervalCutoff
  split_ifs with hn
  · have hnX : X < (n : ℝ) :=
      (Nat.lt_floor_add_one X).trans_le hn.1
    have hoff : ¬ ((N : ℝ) * M ≤ (n : ℝ) ∧
        (n : ℝ) ≤ 4 * (N : ℝ) * M) := by
      intro hblock
      linarith
    rw [literalDirichletConvolution_eq_zero_off_productBlock
      (by positivity) (by positivity)
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta) hoff]
    simp
  · rfl

/-- A dyadic product block starting above `2X` likewise cannot meet the
literal source interval. -/
theorem intervalCutoff_literalConvolution_eq_zero_of_two_mul_lt
    {X : ℝ} (hX : 0 ≤ X) {N M : ℕ} {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (hlarge : 2 * X < (N : ℝ) * (M : ℝ)) :
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution alpha beta) = 0 := by
  funext n
  unfold intervalCutoff
  split_ifs with hn
  · have hoff : ¬ ((N : ℝ) * M ≤ (n : ℝ) ∧
        (n : ℝ) ≤ 4 * (N : ℝ) * M) := by
      intro hblock
      linarith
    rw [literalDirichletConvolution_eq_zero_off_productBlock
      (by positivity) (by positivity)
      (supportedDyadic_coe_of_supportedNatDyadic halpha)
      (supportedDyadic_coe_of_supportedNatDyadic hbeta) hoff]
    simp
  · rfl

/-- Exact masked double-dyadic expansion of one actual Type-II component.
The empty-suffix alternative is handled separately by
`maskedDynamicComponentV3_eq_zero_of_typeII_emptySuffix`. -/
theorem dynamicComponentRemainderV3_typeII_eq_sum_maskedPackets
    {X delta H₀ : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (hsuffix : typeIISuffixFactorList
      (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta)) ≠ []) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeII =
      let factors := sortedComponentFactorList logIndex zbag mbag
      let s := largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta)
      let leftFactors := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      ∑ leftCell : Fin (sourceDyadicCount (factorUpperProduct leftFactors)),
        ∑ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
          intervalCutoff (openSourceLeft X) (2 * X)
            (literalDirichletConvolution
              (scaledTypeIIPrefixCell zbag mbag leftFactors leftCell)
              (factorListDyadicCell suffix suffixCell)) := by
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow X delta)
  let leftFactors := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  rcases hdata with ⟨hsScale, hsmall, hupper⟩
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length =
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag).length := by
    have := congrArg List.length hlengths
    simpa [factors] using this
  have hslt : s < factors.length := by
    rw [hlenEq]
    simpa [s] using hsScale
  have hprelim := dynamicPreliminaryComponent_eq_sum_typeIIPackets
    hX hK logIndex zbag mbag s
    (by simpa [factors] using hslt)
    (by simpa [suffix, factors, s] using hsuffix)
  have hremainder :
      dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
          logIndex zbag mbag .typeII =
        maskedDynamicComponentV3 logIndex zbag mbag := by
    funext n
    unfold dynamicComponentRemainderV3
    rw [houtcome]
    simp
  rw [hremainder,
    maskedDynamicComponentV3_eq_intervalCutoff (by linarith : 0 ≤ X)]
  rw [hprelim]
  simp only [factors, s, leftFactors, suffix]
  rw [intervalCutoff_fintypeSum]
  apply Finset.sum_congr rfl
  intro leftCell hleft
  rw [intervalCutoff_fintypeSum]
  apply Finset.sum_congr rfl
  intro suffixCell hsuf
  funext n
  unfold intervalCutoff
  split_ifs
  · rw [arithmetic_mul_apply_eq_literalDirichletConvolution]
  · rfl

end
end MRTLemma215DynamicTypeIIMaskedPacketsV3

#print axioms MRTLemma215DynamicTypeIIMaskedPacketsV3.scaledTypeIIPrefixCell_supported
#print axioms MRTLemma215DynamicTypeIIMaskedPacketsV3.dynamicComponentRemainderV3_typeII_eq_zero_of_outcome_ne
#print axioms MRTLemma215DynamicTypeIIMaskedPacketsV3.intervalCutoff_literalConvolution_eq_zero_of_four_mul_le
#print axioms MRTLemma215DynamicTypeIIMaskedPacketsV3.intervalCutoff_literalConvolution_eq_zero_of_two_mul_lt
#print axioms MRTLemma215DynamicTypeIIMaskedPacketsV3.dynamicComponentRemainderV3_typeII_eq_sum_maskedPackets
