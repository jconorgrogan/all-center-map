import MRTLemma215DynamicTypeIIUniformCellConstantV3
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3
import BudgetedSelectedPoweredBlockAssembly

/-! # One divisor-log majorant for every bounded HB Type-II component -/

namespace MRTLemma215DynamicTypeIIUniformMajorantV3

open CGLProofDAG
open MAPMRTCorollary25TypeD1CoefficientBound
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicSupportV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicTypeIICoefficientBoundsV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIIDivisorLogV3
open MRTLemma215DynamicTypeIIUniformCellConstantV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open BudgetedSelectedPoweredBlockAssembly

noncomputable section

/-- For a fixed HB order `K`, a single constant controls the divisor-log
factor of every Type-II split and every branch.  In particular, this constant
does not depend on `X`, the component tuple, or either dyadic cell. -/
theorem exists_uniform_typeII_divisorLog_majorant
    (K : ℕ) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {X : ℝ} (branch : Fin K)
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
        (zbag : Sym (Option
          (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1))
        (s : ℕ) (n : ℕ), 0 < n →
        let factors := sortedComponentFactorList logIndex zbag mbag
        let r := (typeIIPrefixFactorList factors s).length
        let t := (typeIISuffixFactorList factors s).length
        (orderedDivisorCount (r + t) n : ℝ) *
            Real.log (2 + (n : ℝ)) ^ (2 * r + 2 * t) ≤
          C₀ * Real.rpow n theta := by
  obtain ⟨C₀, hC₀, hmajor⟩ :=
    orderedDivisorCount_mul_log_pow_subpolynomial
      (2 * K) (4 * K) (by omega) theta htheta
  refine ⟨C₀, hC₀, ?_⟩
  intro X branch logIndex zbag mbag s n hn
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let r := (typeIIPrefixFactorList factors s).length
  let t := (typeIISuffixFactorList factors s).length
  have hparts : r + t = factors.length := by
    dsimp [r, t]
    unfold typeIIPrefixFactorList typeIISuffixFactorList
    rw [List.length_take, List.length_drop]
    omega
  have hfactor := sortedComponentFactorList_length_le logIndex zbag mbag
  have hbranch : (branch : ℕ) < K := branch.isLt
  have horder : r + t ≤ 2 * K := by
    dsimp [factors] at hparts
    omega
  have hexponent : 2 * r + 2 * t ≤ 4 * K := by omega
  have hdivNat : orderedDivisorCount (r + t) n ≤
      orderedDivisorCount (2 * K) n :=
    orderedDivisorCount_mono_order horder
  have hdiv : (orderedDivisorCount (r + t) n : ℝ) ≤
      orderedDivisorCount (2 * K) n := by exact_mod_cast hdivNat
  have hlogOne : 1 ≤ Real.log (2 + (n : ℝ)) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + (n : ℝ)) := Real.log_le_log
        (Real.exp_pos 1)
        (by
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith [Real.exp_one_lt_three])
  calc
    (orderedDivisorCount (r + t) n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ (2 * r + 2 * t) ≤
      (orderedDivisorCount (2 * K) n : ℝ) *
        Real.log (2 + (n : ℝ)) ^ (4 * K) := by
          exact mul_le_mul hdiv (pow_le_pow_right₀ hlogOne hexponent)
            (by positivity) (by positivity)
    _ ≤ C₀ * Real.rpow n theta := hmajor n hn

/-- One convolution constant works simultaneously for all branches, component
tuples, and double-dyadic cells at fixed HB order. -/
theorem exists_uniform_actualTypeIICell_convolution_bound_fixedOrder
    (K : ℕ) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X delta H₀ : ℝ} (branch : Fin K)
        (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
        (zbag : Sym (Option
          (Fin (sourceDyadicCount (hbFactorCutoff X)))) (branch : ℕ))
        (mbag : Sym (Option (Fin (sourceDyadicCount
          ⌊dynamicHBCutoff X K⌋₊))) ((branch : ℕ) + 1))
        (houtcome : dynamicComponentOutcome 8 delta H₀ logIndex zbag mbag =
          .typeII),
        let factors := sortedComponentFactorList logIndex zbag mbag
        let s := largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow X delta)
        let left := typeIIPrefixFactorList factors s
        let suffix := typeIISuffixFactorList factors s
        ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
        ∀ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
        ∀ n : ℕ,
          ‖literalDirichletConvolution
              (scaledTypeIIPrefixCell zbag mbag left leftCell)
              (factorListDyadicCell suffix suffixCell) n‖ ≤
            C * Real.rpow
              (4 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
                ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) theta := by
  obtain ⟨C₀, hC₀, hmajor⟩ :=
    exists_uniform_typeII_divisorLog_majorant K hK theta htheta
  let Smax : ℕ := K ^ (K + 1) * Nat.factorial K * Nat.factorial K
  let C : ℝ := (Smax : ℝ) * (2 : ℝ) ^ (4 * K) * C₀
  refine ⟨C, by dsimp [C, Smax]; positivity, ?_⟩
  intro X delta H₀ branch logIndex zbag mbag houtcome
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  let left := typeIIPrefixFactorList factors s
  let suffix := typeIISuffixFactorList factors s
  let r := left.length
  let t := suffix.length
  let A : ℝ :=
    ((K ^ ((branch : ℕ) + 1) * Nat.factorial (branch : ℕ) *
      Nat.factorial ((branch : ℕ) + 1) : ℕ) : ℝ) * (2 : ℝ) ^ (2 * r)
  let D : ℝ := (2 : ℝ) ^ (2 * t)
  intro leftCell suffixCell n
  have hk1 : (branch : ℕ) + 1 ≤ K := branch.isLt
  have hscalarNat :
      K ^ ((branch : ℕ) + 1) * Nat.factorial (branch : ℕ) *
          Nat.factorial ((branch : ℕ) + 1) ≤ Smax := by
    dsimp [Smax]
    have hp := pow_le_pow_right₀ hK (hk1.trans (Nat.le_succ K))
    have hf0 := Nat.factorial_le (Nat.le_trans (Nat.le_succ _) hk1)
    have hf1 := Nat.factorial_le hk1
    exact Nat.mul_le_mul (Nat.mul_le_mul hp hf0) hf1
  have hparts : r + t = factors.length := by
    dsimp [r, t, left, suffix]
    unfold typeIIPrefixFactorList typeIISuffixFactorList
    rw [List.length_take, List.length_drop]
    omega
  have hfactor := sortedComponentFactorList_length_le logIndex zbag mbag
  have hlen : r + t ≤ 2 * K := by
    dsimp [factors] at hparts
    omega
  have htwo : (2 : ℝ) ^ (2 * r + 2 * t) ≤ (2 : ℝ) ^ (4 * K) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hAD : A * D ≤ (Smax : ℝ) * (2 : ℝ) ^ (4 * K) := by
    have hs :
        (((K ^ ((branch : ℕ) + 1) * Nat.factorial (branch : ℕ) *
          Nat.factorial ((branch : ℕ) + 1) : ℕ) : ℝ)) ≤ Smax := by
      exact_mod_cast hscalarNat
    dsimp [A, D]
    have hpowEq : (2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (2 * t) =
        (2 : ℝ) ^ (2 * r + 2 * t) := (pow_add _ _ _).symm
    calc
      _ = (((K ^ ((branch : ℕ) + 1) * Nat.factorial (branch : ℕ) *
          Nat.factorial ((branch : ℕ) + 1) : ℕ) : ℝ)) *
            ((2 : ℝ) ^ (2 * r) * (2 : ℝ) ^ (2 * t)) := by ring
      _ = (((K ^ ((branch : ℕ) + 1) * Nat.factorial (branch : ℕ) *
          Nat.factorial ((branch : ℕ) + 1) : ℕ) : ℝ)) *
            (2 : ℝ) ^ (2 * r + 2 * t) := by rw [hpowEq]
      _ ≤ _ := mul_le_mul hs htwo (by positivity) (by positivity)
  have hleft : ∀ f ∈ left, f ∈ factors := by
    intro f hf
    exact typeIIPrefixFactor_mem_sorted factors s hf
  have hsuffix : ∀ f ∈ suffix, f ∈ factors := by
    intro f hf
    exact typeIISuffixFactor_mem_sorted factors s hf
  have halpha := scaledTypeIIPrefixCell_divisorLogMajorized
    logIndex zbag mbag left (by simpa [factors] using hleft) leftCell
  have hbeta := factorListDyadicCell_divisorLogMajorized
    logIndex zbag mbag suffix (by simpa [factors] using hsuffix) suffixCell
  have hraw := literalDirichletConvolution_norm_le_productScale_of_commonMajorant
    (r := r) (s := t) (ell := 2 * r) (j := 2 * t)
    (theta := theta) (A := A) (D := D) (C₀ := C₀)
    (N := ((2 ^ (leftCell : ℕ) : ℕ) : ℝ))
    (M := ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ))
    (alpha := scaledTypeIIPrefixCell zbag mbag left leftCell)
    (beta := factorListDyadicCell suffix suffixCell)
    htheta (by unfold A; positivity) (by unfold D; positivity) hC₀
    (by positivity) (by positivity)
    (supportedDyadic_coe_of_supportedNatDyadic
      (scaledTypeIIPrefixCell_supported zbag mbag left leftCell))
    (supportedDyadic_coe_of_supportedNatDyadic
      (factorListDyadicCell_supported suffix suffixCell))
    (by simpa only [A, r] using halpha) (by simpa only [D, t] using hbeta)
    (by
      intro m hm
      simpa [r, t, two_mul, add_assoc, add_left_comm, add_comm] using
        hmajor branch logIndex zbag mbag s m hm)
    n
  calc
    _ ≤ ((A * D) * C₀) * Real.rpow
        (4 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
          ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) theta := hraw
    _ ≤ C * Real.rpow
        (4 * ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) *
          ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ)) theta := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]
        exact mul_le_mul_of_nonneg_right hAD hC₀.le
      · exact Real.rpow_nonneg (by positivity) theta

end
end MRTLemma215DynamicTypeIIUniformMajorantV3

#print axioms MRTLemma215DynamicTypeIIUniformMajorantV3.exists_uniform_typeII_divisorLog_majorant
#print axioms MRTLemma215DynamicTypeIIUniformMajorantV3.exists_uniform_actualTypeIICell_convolution_bound_fixedOrder
