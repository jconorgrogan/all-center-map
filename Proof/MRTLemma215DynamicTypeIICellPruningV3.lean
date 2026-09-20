import MRTLemma215DynamicTypeIIMaskedPacketsV3

/-!
# Exact lower-support pruning for dynamic Type-II cells

The standard output-shell partition starts at scale one.  Cells whose upper
dyadic endpoint is still below the product of the factors' lower endpoints
are identically zero.  This is needed to retain the classifier's
`X^delta` saving after re-dyadicization.
-/

namespace MRTLemma215DynamicTypeIICellPruningV3

open scoped ArithmeticFunction
open ArithmeticFunction
open MAPMRTCorollary25 MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215OpenIntervalCutoffV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicTypeIIFactorizationV3

noncomputable section

/-- Every standard output-shell scale is strictly below the ambient upper
support endpoint. -/
theorem two_pow_sourceDyadicCell_lt
    {N : ℕ} (hN : 2 ≤ N) (cell : Fin (sourceDyadicCount N)) :
    2 ^ (cell : ℕ) < N := by
  have hcell : (cell : ℕ) ≤ (N - 1).log2 := by
    have := cell.isLt
    simpa [sourceDyadicCount] using this
  have hp : 2 ^ (cell : ℕ) ≤ 2 ^ (N - 1).log2 :=
    Nat.pow_le_pow_right (by omega) hcell
  have hlog : 2 ^ (N - 1).log2 ≤ N - 1 :=
    Nat.log2_self_le (by omega)
  omega

/-- A collected output cell below the strict product-support threshold is
the zero arithmetic function. -/
theorem factorListDyadicCell_eq_zero_of_upper_le_lower
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))))
    (hsmall : 2 * 2 ^ (cell : ℕ) ≤
      factorLowerProduct (head :: tail)) :
    factorListDyadicCell (head :: tail) cell = 0 := by
  ext n
  unfold factorListDyadicCell sourceDyadicArithmetic sourceDyadicCoeff
  change (if 2 ≤ n ∧ n ≤ factorUpperProduct (head :: tail) ∧
      (n - 1).log2 = (cell : ℕ) then
        factorConvolution (head :: tail) n else 0) = 0
  split_ifs with hn
  · have hdyadic : n ∈ Finset.Ioc (2 ^ (cell : ℕ))
        (2 * 2 ^ (cell : ℕ)) :=
      (log2_sub_one_eq_iff_mem_Ioc hn.1).mp hn.2.2
    have hupper : n ≤ 2 * 2 ^ (cell : ℕ) :=
      (Finset.mem_Ioc.mp hdyadic).2
    exact factorConvolution_zero_of_le head tail
      (hupper.trans hsmall)
  · rfl

theorem factorListDyadicCell_eq_zero_of_upper_le_lower_of_ne_nil
    (factors : List NatDyadicFactor) (hne : factors ≠ [])
    (cell : Fin (sourceDyadicCount (factorUpperProduct factors)))
    (hsmall : 2 * 2 ^ (cell : ℕ) ≤ factorLowerProduct factors) :
    factorListDyadicCell factors cell = 0 := by
  cases factors with
  | nil => exact (hne rfl).elim
  | cons head tail =>
      exact factorListDyadicCell_eq_zero_of_upper_le_lower
        head tail cell hsmall

/-- The HB scalar absorbed into a prefix cell does not change the preceding
lower-support pruning. -/
theorem scaledTypeIIPrefixCell_eq_zero_of_upper_le_lower
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (head : NatDyadicFactor) (tail : List NatDyadicFactor)
    (cell : Fin (sourceDyadicCount (factorUpperProduct (head :: tail))))
    (hsmall : 2 * 2 ^ (cell : ℕ) ≤
      factorLowerProduct (head :: tail)) :
    scaledTypeIIPrefixCell zbag mbag (head :: tail) cell = 0 := by
  unfold scaledTypeIIPrefixCell
  rw [factorListDyadicCell_eq_zero_of_upper_le_lower head tail cell hsmall]
  exact mul_zero _

theorem scaledTypeIIPrefixCell_eq_zero_of_upper_le_lower_of_ne_nil
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (factors : List NatDyadicFactor) (hne : factors ≠ [])
    (cell : Fin (sourceDyadicCount (factorUpperProduct factors)))
    (hsmall : 2 * 2 ^ (cell : ℕ) ≤ factorLowerProduct factors) :
    scaledTypeIIPrefixCell zbag mbag factors cell = 0 := by
  unfold scaledTypeIIPrefixCell
  rw [factorListDyadicCell_eq_zero_of_upper_le_lower_of_ne_nil
    factors hne cell hsmall]
  exact mul_zero _

/-- If the short Type-II cell lies below its collected lower support, the
entire sharp-masked double cell is exactly zero. -/
theorem intervalCutoff_typeIICell_eq_zero_of_left_upper_le_lower
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (head : NatDyadicFactor) (tail suffix : List NatDyadicFactor)
    (leftCell : Fin
      (sourceDyadicCount (factorUpperProduct (head :: tail))))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)))
    (hsmall : 2 * 2 ^ (leftCell : ℕ) ≤
      factorLowerProduct (head :: tail)) :
    intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution
        (scaledTypeIIPrefixCell zbag mbag (head :: tail) leftCell)
        (factorListDyadicCell suffix suffixCell)) = 0 := by
  rw [scaledTypeIIPrefixCell_eq_zero_of_upper_le_lower
    zbag mbag head tail leftCell hsmall]
  funext n
  unfold literalDirichletConvolution intervalCutoff
  simp

/-- A nonzero sharp-masked dyadic product cell has product scale comparable
to the source block: `X/4 < N*M ≤ 2X`. -/
theorem nonzero_intervalCutoff_literalConvolution_product_bounds
    {X : ℝ} (hX : 0 ≤ X) {N M : ℕ} {alpha beta : ℕ → ℂ}
    (halpha : SupportedNatDyadic N alpha)
    (hbeta : SupportedNatDyadic M beta)
    (hnonzero : intervalCutoff (openSourceLeft X) (2 * X)
      (literalDirichletConvolution alpha beta) ≠ 0) :
    X < 4 * (N : ℝ) * (M : ℝ) ∧
      (N : ℝ) * (M : ℝ) ≤ 2 * X := by
  constructor
  · by_contra hsmall
    apply hnonzero
    exact intervalCutoff_literalConvolution_eq_zero_of_four_mul_le
      hX halpha hbeta (le_of_not_gt hsmall)
  · by_contra hlarge
    apply hnonzero
    exact intervalCutoff_literalConvolution_eq_zero_of_two_mul_lt
      hX halpha hbeta (lt_of_not_ge hlarge)

/-- Every nonzero sharp-masked cell of an actual Type-II component retains
the classifier's lower scale: its short dyadic length is greater than
`X^delta / 2`.  This is the exact fact that later produces the
`X^{-delta}` term in the normalized ledger. -/
theorem actualTypeIICell_leftScale_gt_half_rpow
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    let left := typeIIPrefixFactorList factors s
    let suffix := typeIISuffixFactorList factors s
    ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
        intervalCutoff (openSourceLeft X) (2 * X)
          (literalDirichletConvolution
            (scaledTypeIIPrefixCell zbag mbag left leftCell)
            (factorListDyadicCell suffix suffixCell)) ≠ 0 →
          Real.rpow X delta <
            2 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  intro leftCell suffixCell hnonzero
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  dsimp only at hdata
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hdata.1
  have hprefixLower := typeIIPrefix_lowerProduct_eq_scalePrefixProduct
    logIndex zbag mbag s
  have hlower : Real.rpow X delta < (factorLowerProduct left : ℝ) := by
    rw [hprefixLower]
    simpa [s, scales, left, factors] using hdata.2.1
  by_contra hscale
  have htwo : 2 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) ≤
      Real.rpow X delta := le_of_not_gt hscale
  have hnat : 2 * 2 ^ (leftCell : ℕ) ≤ factorLowerProduct left := by
    exact_mod_cast (htwo.trans_lt hlower).le
  have hleftne : left ≠ [] := typeIIPrefixFactorList_ne_nil factors hs
  have hprefixZero :
      scaledTypeIIPrefixCell zbag mbag left leftCell = 0 := by
    exact scaledTypeIIPrefixCell_eq_zero_of_upper_le_lower_of_ne_nil
      zbag mbag left hleftne leftCell hnat
  apply hnonzero
  rw [hprefixZero]
  funext n
  unfold literalDirichletConvolution intervalCutoff
  simp

/-- The other half of the Type-II short-scale geometry: every left output
cell lies below the prefix upper endpoint, hence below the classifier's
`2^length * 2H₀` envelope. -/
theorem actualTypeIICell_leftScale_lt_upper
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    let left := typeIIPrefixFactorList factors s
    ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) <
        (2 : ℝ) ^ left.length * (2 * H₀) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  let left := typeIIPrefixFactorList factors s
  intro leftCell
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  dsimp only at hdata
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hdata.1
  have hleftne : left ≠ [] := typeIIPrefixFactorList_ne_nil factors hs
  have hone : ∀ f ∈ left, 1 ≤ f.length := by
    intro f hf
    exact dynamicComponentFactorList_length_one logIndex zbag mbag
      (by simpa [left, factors, typeIIPrefixFactorList] using
        List.mem_of_mem_take hf)
  have hlowerOne : 1 ≤ factorLowerProduct left := by
    unfold factorLowerProduct
    have hprod : 0 < (left.map NatDyadicFactor.length).prod := by
      apply List.prod_pos
      intro n hn
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
      exact hone f hf
    omega
  have hlenOne : 1 ≤ left.length := by
    have : left.length ≠ 0 := by simpa using hleftne
    omega
  have hpowTwo : 2 ≤ 2 ^ left.length := by
    have := Nat.pow_le_pow_right (n := 2) (by omega) hlenOne
    simpa using this
  have hupperTwo : 2 ≤ factorUpperProduct left := by
    rw [factorUpperProduct_eq_pow_mul_lowerProduct]
    calc
      2 ≤ 2 ^ left.length * 1 := by simpa using hpowTwo
      _ ≤ 2 ^ left.length * factorLowerProduct left :=
        Nat.mul_le_mul_left _ hlowerOne
  have hcell := two_pow_sourceDyadicCell_lt hupperTwo leftCell
  have hprefixLower := typeIIPrefix_lowerProduct_eq_scalePrefixProduct
    logIndex zbag mbag s
  have hlowerUpper : (factorLowerProduct left : ℝ) ≤ 2 * H₀ := by
    rw [hprefixLower]
    simpa [s, scales, left, factors] using hdata.2.2
  calc
    ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) <
        (factorUpperProduct left : ℝ) := by exact_mod_cast hcell
    _ = (2 : ℝ) ^ left.length * (factorLowerProduct left : ℝ) := by
      rw [factorUpperProduct_eq_pow_mul_lowerProduct]
      norm_num
    _ ≤ (2 : ℝ) ^ left.length * (2 * H₀) :=
      mul_le_mul_of_nonneg_left hlowerUpper (by positivity)

end
end MRTLemma215DynamicTypeIICellPruningV3

#print axioms MRTLemma215DynamicTypeIICellPruningV3.factorListDyadicCell_eq_zero_of_upper_le_lower
#print axioms MRTLemma215DynamicTypeIICellPruningV3.two_pow_sourceDyadicCell_lt
#print axioms MRTLemma215DynamicTypeIICellPruningV3.scaledTypeIIPrefixCell_eq_zero_of_upper_le_lower
#print axioms MRTLemma215DynamicTypeIICellPruningV3.intervalCutoff_typeIICell_eq_zero_of_left_upper_le_lower
#print axioms MRTLemma215DynamicTypeIICellPruningV3.nonzero_intervalCutoff_literalConvolution_product_bounds
#print axioms MRTLemma215DynamicTypeIICellPruningV3.actualTypeIICell_leftScale_gt_half_rpow
#print axioms MRTLemma215DynamicTypeIICellPruningV3.actualTypeIICell_leftScale_lt_upper
