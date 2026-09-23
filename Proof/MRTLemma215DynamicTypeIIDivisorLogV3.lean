import MRTLemma215DynamicMultiplicityBoundsV3
import MRTLemma215DynamicTypeIICoefficientBoundsV3
import MRTLemma215DynamicTypeIIMaskedPacketsV3
import FixedCharacterPoweredBridge
import MRTCorollary25TypeD1CoefficientBound

/-! # Uniform divisor-log envelopes for dynamic Type-II cells -/

namespace MRTLemma215DynamicTypeIIDivisorLogV3

open scoped ArithmeticFunction
open ArithmeticFunction
open MAPMRTCorollary25TypeD1CoefficientBound
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MAPDynamicHBSourceV3 MAPHBPerronSourceData
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIICoefficientBoundsV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicMultiplicityBoundsV3
open MixedMellinCert

noncomputable section

/-- The collected Type-II pair has positive total divisor order.  This is
forced by the classifier: its short prefix contains the first factor that
crosses `X^delta`. -/
theorem typeIISplit_length_add_pos
    {X delta H₀ : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta)
    1 ≤ (typeIIPrefixFactorList factors s).length +
      (typeIISuffixFactorList factors s).length := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have hdata := typeII_outcome_data logIndex zbag mbag houtcome
  dsimp only at hdata
  have hsScale := hdata.1
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hsScale
  have hne : typeIIPrefixFactorList factors s ≠ [] :=
    typeIIPrefixFactorList_ne_nil factors hs
  have hlenne : (typeIIPrefixFactorList factors s).length ≠ 0 := by
    simpa using hne
  have hpos : 0 < (typeIIPrefixFactorList factors s).length :=
    Nat.pos_of_ne_zero hlenne
  have htarget : 1 ≤ (typeIIPrefixFactorList factors s).length +
      (typeIISuffixFactorList factors s).length := by omega
  simpa [factors, scales, s] using htarget

private theorem log_two_mul_le_two_log_two_add
    {n : ℕ} (hn : 2 ≤ n) :
    Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (2 + (n : ℝ)) := by
  have hpos : 0 < 2 + (n : ℝ) := by positivity
  rw [show 2 * Real.log (2 + (n : ℝ)) =
      Real.log (2 + (n : ℝ)) + Real.log (2 + (n : ℝ)) by ring,
    ← Real.log_mul hpos.ne' hpos.ne']
  apply Real.log_le_log (by positivity)
  nlinarith

private theorem log_power_cell_le
    {r n : ℕ} (hn : 2 ≤ n) :
    Real.log (2 * (n : ℝ)) ^ (2 * r) ≤
      (2 : ℝ) ^ (2 * r) * Real.log (2 + (n : ℝ)) ^ (2 * r) := by
  have hleft : 0 ≤ Real.log (2 * (n : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * n by omega))
  have hpow := pow_le_pow_left₀ hleft
    (log_two_mul_le_two_log_two_add hn) (2 * r)
  calc
    Real.log (2 * (n : ℝ)) ^ (2 * r) ≤
        (2 * Real.log (2 + (n : ℝ))) ^ (2 * r) := hpow
    _ = (2 : ℝ) ^ (2 * r) *
        Real.log (2 + (n : ℝ)) ^ (2 * r) := by rw [mul_pow]

/-- An unscaled collected cell has a global divisor-log envelope with a
constant depending only on the number of collected factors. -/
theorem factorListDyadicCell_divisorLogMajorized
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    DivisorLogMajorized sub.length (2 * sub.length)
      ((2 : ℝ) ^ (2 * sub.length))
      (factorListDyadicCell sub cell) := by
  intro n
  by_cases hncell : n ∈ DeterminantCountWeld.dyadic (2 ^ (cell : ℕ))
  · have hn : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hncell).1
      have hp : 1 ≤ 2 ^ (cell : ℕ) :=
        Nat.one_le_pow (cell : ℕ) 2 (by omega)
      omega
    have hraw := factorListDyadicCell_norm_le
      logIndex zbag mbag sub hsub cell hn
    have hpow := log_power_cell_le (r := sub.length) hn
    rw [FixedCharacterPoweredBridge.orderedDivisorCount_eq_tauAF]
    calc
      ‖factorListDyadicCell sub cell n‖ ≤
          (tauAF sub.length n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := hraw
      _ ≤ (tauAF sub.length n : ℝ) *
          ((2 : ℝ) ^ (2 * sub.length) *
            Real.log (2 + (n : ℝ)) ^ (2 * sub.length)) := by gcongr
      _ = (2 : ℝ) ^ (2 * sub.length) *
          (tauAF sub.length n : ℝ) *
            Real.log (2 + (n : ℝ)) ^ (2 * sub.length) := by ring
  · rw [factorListDyadicCell_supported sub cell n hncell]
    simp only [norm_zero]
    have hbase : (1 : ℝ) ≤ 2 + (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hlog : 0 ≤ Real.log (2 + (n : ℝ)) :=
      Real.log_nonneg hbase
    exact mul_nonneg
      (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hlog _)

/-- The scalar-absorbed prefix cell has the same global divisor-log class,
with the explicit fixed HB scalar bound included in its constant. -/
theorem scaledTypeIIPrefixCell_divisorLogMajorized
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    DivisorLogMajorized sub.length (2 * sub.length)
      (((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) *
        (2 : ℝ) ^ (2 * sub.length))
      (scaledTypeIIPrefixCell zbag mbag sub cell) := by
  intro n
  rw [show scaledTypeIIPrefixCell zbag mbag sub cell =
      dynamicComponentScalarValue zbag mbag • factorListDyadicCell sub cell by
    unfold scaledTypeIIPrefixCell
    exact dynamicComponentScalar_mul_eq_smul zbag mbag _]
  change ‖dynamicComponentScalarValue zbag mbag *
      factorListDyadicCell sub cell n‖ ≤ _
  rw [norm_mul]
  have hs := norm_dynamicComponentScalarValue_le zbag mbag
  have hf := factorListDyadicCell_divisorLogMajorized
    logIndex zbag mbag sub hsub cell n
  calc
    ‖dynamicComponentScalarValue zbag mbag‖ *
        ‖factorListDyadicCell sub cell n‖ ≤
      ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) *
        ‖factorListDyadicCell sub cell n‖ :=
      mul_le_mul_of_nonneg_right hs (norm_nonneg _)
    _ ≤ ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) *
        ((2 : ℝ) ^ (2 * sub.length) *
          (CGLProofDAG.orderedDivisorCount sub.length n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (2 * sub.length)) :=
      mul_le_mul_of_nonneg_left hf (by positivity)
    _ = _ := by ring

/-- For every actual Type-II split, every pair of dyadic cells has the
literal subpower coefficient bound required by Corollary 2.5.  All source
membership and positive-divisor-order obligations are discharged here. -/
theorem exists_actualTypeIICell_convolution_bound
    {X delta H₀ theta : ℝ} {K k : ℕ}
    (hK : 1 ≤ K) (htheta : 0 < theta)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
      .typeII) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta)
    let left := typeIIPrefixFactorList factors s
    let suffix := typeIISuffixFactorList factors s
    ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
        ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
          ‖MAPMRTCorollary25TypeD1LiteralWeld.literalDirichletConvolution
              (scaledTypeIIPrefixCell zbag mbag left leftCell)
              (factorListDyadicCell suffix suffixCell) n‖ ≤
            C * Real.rpow
              (4 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
                ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) theta := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  intro leftCell suffixCell
  let N : ℕ := 2 ^ (leftCell : ℕ)
  let M : ℕ := 2 ^ (suffixCell : ℕ)
  let A : ℝ :=
    ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) *
      (2 : ℝ) ^ (2 * left.length)
  let D : ℝ := (2 : ℝ) ^ (2 * suffix.length)
  have hleft : ∀ f ∈ left, f ∈ factors := by
    intro f hf
    exact typeIIPrefixFactor_mem_sorted factors s hf
  have hsuffix : ∀ f ∈ suffix, f ∈ factors := by
    intro f hf
    exact typeIISuffixFactor_mem_sorted factors s hf
  have horders : 1 ≤ left.length + suffix.length := by
    simpa [factors, scales, s, left, suffix] using
      typeIISplit_length_add_pos logIndex zbag mbag houtcome
  have hN : 0 < (N : ℝ) := by
    dsimp [N]
    positivity
  have hM : 0 < (M : ℝ) := by
    dsimp [M]
    positivity
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have halphaSupport := scaledTypeIIPrefixCell_supported
    zbag mbag left leftCell
  have hgammaSupport := factorListDyadicCell_supported suffix suffixCell
  have halpha := scaledTypeIIPrefixCell_divisorLogMajorized
    logIndex zbag mbag left (by simpa [factors] using hleft) leftCell
  have hgamma := factorListDyadicCell_divisorLogMajorized
    logIndex zbag mbag suffix (by simpa [factors] using hsuffix) suffixCell
  obtain ⟨C, hC, hbound⟩ :=
    MAPMRTCorollary25TypeD1CoefficientBound.literalDirichletConvolution_norm_le_productScale
      horders htheta hA hD hN hM
      (supportedDyadic_coe_of_supportedNatDyadic halphaSupport)
      (supportedDyadic_coe_of_supportedNatDyadic hgammaSupport)
      (by simpa [A] using halpha) (by simpa [D] using hgamma)
  refine ⟨C, hC, ?_⟩
  simpa [N, M, left, suffix] using! hbound

end
end MRTLemma215DynamicTypeIIDivisorLogV3

#print axioms MRTLemma215DynamicTypeIIDivisorLogV3.typeIISplit_length_add_pos
#print axioms MRTLemma215DynamicTypeIIDivisorLogV3.factorListDyadicCell_divisorLogMajorized
#print axioms MRTLemma215DynamicTypeIIDivisorLogV3.scaledTypeIIPrefixCell_divisorLogMajorized
#print axioms MRTLemma215DynamicTypeIIDivisorLogV3.exists_actualTypeIICell_convolution_bound
