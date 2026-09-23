import MRTLemma215DynamicClassificationV3

/-!
# Exact dynamic Type-II factorization

This file exposes the literal two-factor split behind the Type-II outcome in
MRT Lemma 2.15.  The split point is the first prefix whose lower support
passes `X^delta`; the classifier records that the same prefix is at most
`2 * H₀`.  No mean-value estimate is asserted here.
-/

namespace MRTLemma215DynamicTypeIIFactorizationV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicClassificationV3

noncomputable section

/-- The short Type-II prefix, including the first factor that pushes the
small prefix past `X^delta`. -/
def typeIIPrefixFactorList (factors : List NatDyadicFactor) (s : ℕ) :
    List NatDyadicFactor :=
  factors.take (s + 1)

/-- The complementary Type-II factor list. -/
def typeIISuffixFactorList (factors : List NatDyadicFactor) (s : ℕ) :
    List NatDyadicFactor :=
  factors.drop (s + 1)

/-- Exact convolution split at the Type-II cut. -/
theorem factorConvolution_eq_typeIISplit
    (factors : List NatDyadicFactor) (s : ℕ) :
    factorConvolution factors =
      factorConvolution (typeIIPrefixFactorList factors s) *
        factorConvolution (typeIISuffixFactorList factors s) := by
  unfold typeIIPrefixFactorList typeIISuffixFactorList
  rw [← factorConvolution_append, List.take_append_drop]

/-- A Type-II classifier result contains exactly the two inequalities printed
in the proof of MRT Lemma 2.15. -/
theorem typeII_outcome_data
    {X delta H₀ : ℝ} {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeII) :
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    s < scales.length ∧
      Real.rpow X delta < scalePrefixProduct scales (s + 1) ∧
      scalePrefixProduct scales (s + 1) ≤ 2 * H₀ := by
  dsimp only
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  by_cases hs : s < scales.length
  · by_cases hII : scalePrefixProduct scales (s + 1) ≤ 2 * H₀
    · have hnotSmall := largestSmallPrefix_succ_not_small
        (scales := scales) (smallScale := Real.rpow X delta) hs
      exact ⟨hs, lt_of_not_ge hnotSmall, hII⟩
    · by_cases hj : scales.length - s < m
      · have htype : dynamicComponentOutcome m delta H₀
            logIndex zbag mbag = .typeD ⟨scales.length - s, hj⟩ := by
          exact classifyScaleList_typeD
            (by simpa [s, scales] using hs)
            (by simpa [s, scales] using hII)
            (by simpa [s, scales] using hj)
        rw [htype] at houtcome
        cases houtcome
      · have htype : dynamicComponentOutcome m delta H₀
            logIndex zbag mbag = .vanishing := by
          exact classifyScaleList_vanishing_of_largeTail
            (by simpa [s, scales] using hs)
            (by simpa [s, scales] using hII)
            (by simpa [s, scales] using hj)
        rw [htype] at houtcome
        cases houtcome
  · have htype : dynamicComponentOutcome m delta H₀
        logIndex zbag mbag = .vanishing := by
      exact classifyScaleList_vanishing_of_allSmall
        (by simpa [s, scales] using hs)
    rw [htype] at houtcome
    cases houtcome

/-- Lower support of the exact factor prefix equals the classifier's real
prefix product. -/
theorem typeIIPrefix_lowerProduct_eq_scalePrefixProduct
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ) :
    ((factorLowerProduct
      (typeIIPrefixFactorList
        (sortedComponentFactorList logIndex zbag mbag) s) : ℕ) : ℝ) =
      scalePrefixProduct
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (s + 1) := by
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have htake := congrArg
    (fun l : List ℝ => (l.take (s + 1)).prod) hlengths
  unfold typeIIPrefixFactorList factorLowerProduct scalePrefixProduct
  rw [Nat.cast_list_prod]
  simpa only [List.map_map, Function.comp_def, List.map_take] using! htake

/-- Exact Type-II geometry and factorization of the active convolution.
The dyadic re-splitting of the two collected factors is deliberately kept as
a later finite adapter. -/
theorem typeII_regrouping_geometry
    {X delta H₀ : ℝ} {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeII) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      Real.rpow X delta <
          (factorLowerProduct (typeIIPrefixFactorList factors s) : ℝ) ∧
        (factorLowerProduct (typeIIPrefixFactorList factors s) : ℝ) ≤
          2 * H₀ ∧
        factorConvolution (dynamicComponentFactorList logIndex zbag mbag) =
          factorConvolution (typeIIPrefixFactorList factors s) *
            factorConvolution (typeIISuffixFactorList factors s) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  dsimp only at hdata
  rcases hdata with ⟨hsScale, hsmall, hupper⟩
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hsScale
  have hprefix := typeIIPrefix_lowerProduct_eq_scalePrefixProduct
    logIndex zbag mbag s
  refine ⟨hs, ?_, ?_, ?_⟩
  · rw [hprefix]
    simpa [s, scales] using hsmall
  · rw [hprefix]
    simpa [s, scales] using hupper
  · rw [← factorConvolution_sortedComponentFactorList
      logIndex zbag mbag]
    exact factorConvolution_eq_typeIISplit factors s

/-- On a Type-II outcome the classifier remainder is literally the sharp
source mask applied to the scalar times the two collected factors. -/
theorem dynamicComponentRemainderV3_typeII_eq
    {X delta H₀ : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (n : ℕ) :
    dynamicComponentRemainderV3 (delta := delta) (H₀ := H₀)
        logIndex zbag mbag .typeII n =
      if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
        (dynamicComponentScalar zbag mbag *
          (factorConvolution
              (typeIIPrefixFactorList
                (sortedComponentFactorList logIndex zbag mbag)
                (largestSmallPrefix
                  (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
                  (Real.rpow X delta))) *
            factorConvolution
              (typeIISuffixFactorList
                (sortedComponentFactorList logIndex zbag mbag)
                (largestSmallPrefix
                  (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
                  (Real.rpow X delta))))) n
      else 0 := by
  unfold dynamicComponentRemainderV3
  rw [houtcome]
  simp only [ite_true]
  unfold maskedDynamicComponentV3
  split_ifs with hn
  · rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK]
    rw [← factorConvolution_sortedComponentFactorList
      logIndex zbag mbag]
    rw [factorConvolution_eq_typeIISplit]
  · rfl

end
end MRTLemma215DynamicTypeIIFactorizationV3

#print axioms MRTLemma215DynamicTypeIIFactorizationV3.typeII_outcome_data
#print axioms MRTLemma215DynamicTypeIIFactorizationV3.typeII_regrouping_geometry
#print axioms MRTLemma215DynamicTypeIIFactorizationV3.dynamicComponentRemainderV3_typeII_eq
