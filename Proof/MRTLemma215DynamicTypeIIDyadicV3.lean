import MRTLemma215DynamicTypeIIFactorizationV3
import MRTLemma215ComplementDyadicV3
import MRTLemma215DynamicHighPacketCertificateV3

/-!
# Exact dyadic packets for dynamic Type II

The two collected factors in the Type-II split need one further standard
dyadic partition before MRT Lemma 2.10 applies.  This file performs that
finite partition exactly when both collected factor lists are nonempty.  The
empty-complement alternative is intentionally left visible for the global
support/boundary weld.
-/

namespace MRTLemma215DynamicTypeIIDyadicV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215ComplementDyadicV3 MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicClassificationV3

noncomputable section

/-- Standard output shell of an arbitrary nonempty collected factor list. -/
def factorListDyadicCell (factors : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct factors))) :
    ArithmeticFunction ℂ :=
  sourceDyadicArithmetic (factorUpperProduct factors)
    (factorConvolution factors) cell

theorem factorListDyadicCell_supported
    (factors : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct factors))) :
    SupportedNatDyadic (2 ^ (cell : ℕ))
      (factorListDyadicCell factors cell) :=
  sourceDyadicArithmetic_supported _ _ cell

/-- Every nonempty collected factor is the exact sum of its standard dyadic
output cells. -/
theorem factorConvolution_eq_sum_factorListDyadicCell
    (factors : List NatDyadicFactor)
    (hne : factors ≠ [])
    (hone : ∀ f ∈ factors, 1 ≤ f.length) :
    factorConvolution factors =
      ∑ cell : Fin (sourceDyadicCount (factorUpperProduct factors)),
        factorListDyadicCell factors cell := by
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  exact factorConvolution_eq_sum_sourceDyadicArithmetic head tail
    (by simpa using hone)

/-- The Type-II prefix is nonempty at every actual Type-II split. -/
theorem typeIIPrefixFactorList_ne_nil
    (factors : List NatDyadicFactor) {s : ℕ}
    (hs : s < factors.length) :
    typeIIPrefixFactorList factors s ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [typeIIPrefixFactorList, List.length_take,
    Nat.min_eq_left (Nat.succ_le_iff.mpr hs)] at hlen

def scaledTypeIIPrefixCell
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (leftFactors : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct leftFactors))) :
    ArithmeticFunction ℂ :=
  dynamicComponentScalar zbag mbag * factorListDyadicCell leftFactors cell

/-- Exact double-dyadic expansion of one Type-II preliminary component.  The
HB/binomial/multinomial scalar is absorbed into the prefix cell. -/
theorem dynamicPreliminaryComponent_eq_sum_typeIIPackets
    {X : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ)
    (hs : s < (sortedComponentFactorList logIndex zbag mbag).length)
    (hsuffix : typeIISuffixFactorList
      (sortedComponentFactorList logIndex zbag mbag) s ≠ []) :
    dynamicPreliminaryComponent (some logIndex) zbag mbag =
      let factors := sortedComponentFactorList logIndex zbag mbag
      let leftFactors := typeIIPrefixFactorList factors s
      let suffix := typeIISuffixFactorList factors s
      ∑ leftCell : Fin (sourceDyadicCount (factorUpperProduct leftFactors)),
        ∑ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
          scaledTypeIIPrefixCell zbag mbag leftFactors leftCell *
            factorListDyadicCell suffix suffixCell := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let leftFactors := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  have hprefix : leftFactors ≠ [] := by
    exact typeIIPrefixFactorList_ne_nil factors (by simpa [factors] using hs)
  have honeFactors : ∀ f ∈ factors, 1 ≤ f.length := by
    intro f hf
    exact dynamicComponentFactorList_length_one logIndex zbag mbag
      (by simpa [factors] using hf)
  have honePrefix : ∀ f ∈ leftFactors, 1 ≤ f.length := by
    intro f hf
    exact honeFactors f (List.mem_of_mem_take hf)
  have honeSuffix : ∀ f ∈ suffix, 1 ≤ f.length := by
    intro f hf
    exact honeFactors f (List.mem_of_mem_drop hf)
  have hcomponent := dynamicPreliminaryComponent_some_eq_factorConvolution
    hX hK logIndex zbag mbag
  rw [hcomponent]
  rw [← factorConvolution_sortedComponentFactorList logIndex zbag mbag]
  rw [factorConvolution_eq_typeIISplit]
  rw [factorConvolution_eq_sum_factorListDyadicCell leftFactors hprefix honePrefix]
  rw [factorConvolution_eq_sum_factorListDyadicCell suffix
    (by simpa [suffix, factors] using hsuffix) honeSuffix]
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro leftCell hp
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro suffixCell hsCell
  unfold scaledTypeIIPrefixCell
  ring

/-- If the Type-II suffix is empty, the whole factor list is the short
prefix.  Under the literal sufficiently-large-`X` inequality its upper
support lies at or below `X`, so the sharp source mask kills the component.
This is the finite alternative to pretending the suffix is always nonempty. -/
theorem maskedDynamicComponentV3_eq_zero_of_typeII_emptySuffix
    {X delta H₀ : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII)
    (hempty : typeIISuffixFactorList
      (sortedComponentFactorList logIndex zbag mbag)
      (largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta)) = [])
    (hlarge :
      (2 : ℝ) ^ (sortedComponentFactorList logIndex zbag mbag).length *
        (2 * H₀) ≤ X)
    (n : ℕ) :
    maskedDynamicComponentV3 logIndex zbag mbag n = 0 := by
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  dsimp only at hdata
  rcases hdata with ⟨hsScale, hsmall, hprefixUpper⟩
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hsScale
  have hempty' : typeIISuffixFactorList factors s = [] := by
    simpa [factors, s, scales] using hempty
  have hsuffixLength := congrArg List.length hempty'
  have hsplit : s + 1 = factors.length := by
    simp only [typeIISuffixFactorList, List.length_drop,
      List.length_nil] at hsuffixLength
    omega
  have hprefixAll : typeIIPrefixFactorList factors s = factors := by
    unfold typeIIPrefixFactorList
    exact List.take_of_length_le (by omega)
  have hprefixEq := typeIIPrefix_lowerProduct_eq_scalePrefixProduct
    logIndex zbag mbag s
  have hlower : (factorLowerProduct factors : ℝ) ≤ 2 * H₀ := by
    rw [← hprefixAll]
    rw [hprefixEq]
    simpa [s, scales] using hprefixUpper
  have hupperReal : (factorUpperProduct factors : ℝ) ≤ X := by
    rw [factorUpperProduct_eq_pow_mul_lowerProduct]
    push_cast
    calc
      (2 : ℝ) ^ factors.length * (factorLowerProduct factors : ℝ) ≤
          (2 : ℝ) ^ factors.length * (2 * H₀) := by
        gcongr
      _ ≤ X := by simpa [factors] using hlarge
  have hupperFloor : factorUpperProduct factors ≤ ⌊X⌋₊ :=
    Nat.le_floor hupperReal
  by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
  · unfold maskedDynamicComponentV3
    rw [if_pos hn]
    have hnUpper : factorUpperProduct factors < n :=
      lt_of_le_of_lt hupperFloor (Finset.mem_Ioc.mp hn).1
    have hfactorsNonempty : factors ≠ [] := by
      intro hnil
      have hzeroLen : factors.length = 0 := by simp [hnil]
      omega
    obtain ⟨head, tail, hfactor⟩ :=
      List.exists_cons_of_ne_nil hfactorsNonempty
    have hzero : factorConvolution factors n = 0 := by
      rw [hfactor]
      exact factorConvolution_zero_of_upperProduct_lt head tail
        (by simpa [hfactor] using hnUpper)
    rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK]
    rw [← factorConvolution_sortedComponentFactorList logIndex zbag mbag]
    rw [dynamicComponentScalar_mul_eq_smul]
    change dynamicComponentScalarValue zbag mbag *
      factorConvolution factors n = 0
    rw [hzero, mul_zero]
  · unfold maskedDynamicComponentV3
    rw [if_neg hn]

end
end MRTLemma215DynamicTypeIIDyadicV3

#print axioms MRTLemma215DynamicTypeIIDyadicV3.factorConvolution_eq_sum_factorListDyadicCell
#print axioms MRTLemma215DynamicTypeIIDyadicV3.dynamicPreliminaryComponent_eq_sum_typeIIPackets
#print axioms MRTLemma215DynamicTypeIIDyadicV3.maskedDynamicComponentV3_eq_zero_of_typeII_emptySuffix
