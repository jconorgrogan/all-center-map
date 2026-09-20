import MRTLemma215DynamicTypeIIDivisorLogV3

/-! # One coefficient constant for every cell of an actual Type-II split -/

namespace MRTLemma215DynamicTypeIIUniformCellConstantV3

open scoped ArithmeticFunction
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPMRTCorollary25TypeD1CoefficientBound
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicClassificationV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIICoefficientBoundsV3
open MRTLemma215DynamicTypeIIMaskedPacketsV3
open MRTLemma215DynamicTypeIIDivisorLogV3
open MixedMellinCert

noncomputable section

/-- Product-scale convolution bound using a caller-supplied common divisor
majorant constant.  Unlike the existential convenience theorem in the
Corollary-2.5 module, this form keeps the same `C₀` across a finite cell
family. -/
theorem literalDirichletConvolution_norm_le_productScale_of_commonMajorant
    {r s ell j : ℕ} {theta A D C₀ N M : ℝ}
    (htheta : 0 < theta) (hA : 0 < A) (hD : 0 < D) (hC₀ : 0 < C₀)
    (hN : 0 < N) (hM : 0 < M)
    {alpha beta : ℕ → ℂ}
    (halphaSupport : SupportedDyadic N alpha)
    (hbetaSupport : SupportedDyadic M beta)
    (halpha : DivisorLogMajorized r ell A alpha)
    (hbeta : DivisorLogMajorized s j D beta)
    (hmajor : ∀ n : ℕ, 0 < n →
      (CGLProofDAG.orderedDivisorCount (r + s) n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (ell + j) ≤
        C₀ * Real.rpow n theta) :
    ∀ n : ℕ,
      ‖literalDirichletConvolution alpha beta n‖ ≤
        ((A * D) * C₀) * Real.rpow (4 * N * M) theta := by
  intro n
  have hscale0 : 0 ≤ 4 * N * M := by positivity
  by_cases hblock : N * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * N * M
  · have hnposReal : (0 : ℝ) < n := (mul_pos hN hM).trans_le hblock.1
    have hnpos : 0 < n := by exact_mod_cast hnposReal
    have hraw := literalDirichletConvolution_norm_le_divisorLog
      hA.le hD.le halpha hbeta n
    have hsub : ‖literalDirichletConvolution alpha beta n‖ ≤
        ((A * D) * C₀) * Real.rpow n theta := by
      calc
        _ ≤ (A * D) *
            (CGLProofDAG.orderedDivisorCount (r + s) n : ℝ) *
              Real.log (2 + (n : ℝ)) ^ (ell + j) := hraw
        _ = (A * D) *
            ((CGLProofDAG.orderedDivisorCount (r + s) n : ℝ) *
              Real.log (2 + (n : ℝ)) ^ (ell + j)) := by ring
        _ ≤ (A * D) * (C₀ * Real.rpow n theta) :=
          mul_le_mul_of_nonneg_left (hmajor n hnpos)
            (mul_nonneg hA.le hD.le)
        _ = ((A * D) * C₀) * Real.rpow n theta := by ring
    have hrpow : Real.rpow n theta ≤ Real.rpow (4 * N * M) theta :=
      Real.rpow_le_rpow hnposReal.le hblock.2 htheta.le
    exact hsub.trans
      (mul_le_mul_of_nonneg_left hrpow
        (mul_nonneg (mul_nonneg hA.le hD.le) hC₀.le))
  · rw [literalDirichletConvolution_eq_zero_off_productBlock
      hN.le hM.le halphaSupport hbetaSupport hblock]
    simp only [norm_zero]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hA.le hD.le) hC₀.le)
      (Real.rpow_nonneg hscale0 theta)

/-- A single positive constant controls every double-dyadic cell belonging
to one actual Type-II component.  It depends on the fixed HB component but
not on either cell index. -/
theorem exists_uniform_actualTypeIICell_convolution_bound
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
    ∃ C : ℝ, 0 < C ∧
      ∀ leftCell : Fin (sourceDyadicCount (factorUpperProduct left)),
      ∀ suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)),
      ∀ n : ℕ,
        ‖literalDirichletConvolution
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
  let r := left.length
  let t := suffix.length
  let A : ℝ :=
    ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ) *
      (2 : ℝ) ^ (2 * r)
  let D : ℝ := (2 : ℝ) ^ (2 * t)
  have horders : 1 ≤ r + t := by
    simpa [factors, scales, s, left, suffix, r, t] using
      typeIISplit_length_add_pos logIndex zbag mbag houtcome
  obtain ⟨C₀, hC₀, hmajor⟩ :=
    orderedDivisorCount_mul_log_pow_subpolynomial
      (r + t) (2 * r + 2 * t) horders theta htheta
  refine ⟨(A * D) * C₀, mul_pos (mul_pos (by
    dsimp [A]
    positivity) (by
    dsimp [D]
    positivity)) hC₀, ?_⟩
  intro leftCell suffixCell n
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
  exact literalDirichletConvolution_norm_le_productScale_of_commonMajorant
    htheta (by dsimp [A]; positivity) (by dsimp [D]; positivity) hC₀
    (by positivity) (by positivity)
    (supportedDyadic_coe_of_supportedNatDyadic
      (scaledTypeIIPrefixCell_supported zbag mbag left leftCell))
    (supportedDyadic_coe_of_supportedNatDyadic
      (factorListDyadicCell_supported suffix suffixCell))
    (by simpa [A, r] using halpha) (by simpa [D, t] using hbeta)
    (by simpa [r, t, two_mul, add_assoc, add_left_comm, add_comm] using hmajor)
    n

end
end MRTLemma215DynamicTypeIIUniformCellConstantV3

#print axioms MRTLemma215DynamicTypeIIUniformCellConstantV3.literalDirichletConvolution_norm_le_productScale_of_commonMajorant
#print axioms MRTLemma215DynamicTypeIIUniformCellConstantV3.exists_uniform_actualTypeIICell_convolution_bound
