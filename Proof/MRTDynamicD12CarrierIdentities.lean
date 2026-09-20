import MRTDynamicD12UniformFullMoment

/-! First serialized d1/d2 weld: identify the finite prefix represented by
the half-line carrier.  This module intentionally stops before the
source-indexed d1/d2 tail cases and before any budget assembly. -/
namespace MRTDynamicD12CarrierIdentities

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MixedMeanFrontend
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25Minkowski
open MAPMRTProposition61TypeD1Factorization
open MAPMRTProposition61TypeD1FirstInequality
open MAPDynamicHBSourceV3
open MRTDynamicD12UniformFullMoment
open MRTDynamicD12PolynomialFactorization
open MRTDynamicD12FactorExtraction MRTDynamicD12FullMoment MRTDynamicD12ShortPrefix
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicHighPacketCertificateV3

noncomputable section

set_option maxHeartbeats 800000

/-- Finite-prefix evaluation agrees with the Corollary-2.5 half-line carrier
when the coefficient is supported up to `N` and `N` lies in the Perron
window.  The endpoint is `N`; no extra coefficient at `ceil (C*Y)` is added.
-/
theorem halfLineDirichletPolynomial_characterTwist_eq_prefixPolynomial
    {q N : ℕ} {Y C : ℝ} (f : ArithmeticFunction ℂ)
    (hCY : 0 ≤ C * Y) (hN : (N : ℝ) ≤ C * Y)
    (hsupp : ∀ n : ℕ, N < n → f n = 0)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    halfLineDirichletPolynomial Y C
        (characterTwist (fun n => chi n) (f : ℕ → ℂ)) t =
      prefixPolynomial q N f chi t := by
  unfold halfLineDirichletPolynomial prefixPolynomial
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc]
  have hNceil : N ≤ Nat.ceil (C * Y) := by
    have : (N : ℝ) ≤ (Nat.ceil (C * Y) : ℝ) :=
      hN.trans (Nat.le_ceil _)
    exact Nat.cast_le.mp this
  have hsubset : Finset.Icc 1 N ⊆
      Finset.Icc 1 (Nat.ceil (C * Y)) :=
    Finset.Icc_subset_Icc le_rfl hNceil
  have hterm (n : ℕ) :
      characterTwist (fun m => chi m) (f : ℕ → ℂ) n /
          (Real.sqrt (n : ℝ) : ℂ) * mellinPhase n t =
        normalizedAF chi t f n := by
    change (characterTwist (fun m => chi m) (f : ℕ → ℂ) n /
        (Real.sqrt (n : ℝ) : ℂ)) * MixedMeanFrontend.mellinPhase n t =
      (characterTwist (fun m => chi m) (f : ℕ → ℂ) n /
        (Real.sqrt (n : ℝ) : ℂ)) * MixedMeanFrontend.mellinPhase n t
    rfl
  trans ∑ n ∈ Finset.Icc 1 (Nat.ceil (C * Y)), normalizedAF chi t f n
  · apply Finset.sum_congr rfl
    intro n hn
    exact hterm n
  · refine (Finset.sum_subset hsubset ?_).symm
    intro n hnCeil hnN
    have hn1 := (Finset.mem_Icc.mp hnCeil).1
    have hgt : N < n := by
      have : ¬ (1 ≤ n ∧ n ≤ N) := by
        simpa [Finset.mem_Icc] using hnN
      omega
    simp [MRTDynamicD12PolynomialFactorization.normalizedAF,
      MAPMRTProposition61TypeD1Factorization.normalizedTwistedTerm,
      MAPMRTCorollary25Instantiation.characterTwist, hsupp n hgt]

theorem shortPrefixCoefficient_eq_smul
    {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor) :
    shortPrefixCoefficient zbag mbag sub =
      dynamicComponentScalarValue zbag mbag • factorConvolution sub := by
  unfold shortPrefixCoefficient
  exact dynamicComponentScalar_mul_eq_smul zbag mbag _

theorem classifierShortPrefix_eq_take
    {X delta : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    classifierShortPrefix (delta := delta) logIndex zbag mbag =
      (sortedComponentFactorList logIndex zbag mbag).take
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow X delta)) := rfl

theorem dynamicPreliminaryComponent_eq_smul_sorted
    {X : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    dynamicPreliminaryComponent (some logIndex) zbag mbag =
      dynamicComponentScalarValue zbag mbag •
        factorConvolution (sortedComponentFactorList logIndex zbag mbag) := by
  rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK,
    ← factorConvolution_sortedComponentFactorList logIndex zbag mbag,
    dynamicComponentScalar_mul_eq_smul]

theorem factorUpperProduct_le_fixedOrder_dilation
    {X : ℝ} {K k : ℕ} (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (factorUpperProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ) ≤
      (2 : ℝ) ^ (2 * K) *
        (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ) := by
  have hlen := sortedComponentFactorList_length_le logIndex zbag mbag
  have hpow : (sortedComponentFactorList logIndex zbag mbag).length ≤ 2 * K := by
    omega
  rw [factorUpperProduct_eq_pow_mul_lowerProduct]
  push_cast
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpow)
    (Nat.cast_nonneg _)

theorem perron_full_carrier_eq_prefixPolynomial
    {X : ℝ} (hX : 1 ≤ X) {K k q : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let Y := (factorLowerProduct factors : ℝ)
    let C := (2 : ℝ) ^ (2 * K)
    halfLineDirichletPolynomial Y C
        (characterTwist (fun n => chi n)
          (dynamicPreliminaryComponent (some logIndex) zbag mbag)) t =
      prefixPolynomial q (factorUpperProduct factors)
        (dynamicComponentScalarValue zbag mbag • factorConvolution factors)
        chi t := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let Y := (factorLowerProduct factors : ℝ)
  let C := (2 : ℝ) ^ (2 * K)
  have hf := dynamicPreliminaryComponent_eq_smul_sorted hX hK
    logIndex zbag mbag
  have hN : (factorUpperProduct factors : ℝ) ≤ C * Y := by
    exact factorUpperProduct_le_fixedOrder_dilation hk logIndex zbag mbag
  have hCY : 0 ≤ C * Y := by
    dsimp [C, Y]
    positivity
  have hsupp : ∀ n : ℕ, factorUpperProduct factors < n →
      (dynamicComponentScalarValue zbag mbag • factorConvolution factors) n = 0 := by
    intro n hn
    change dynamicComponentScalarValue zbag mbag * factorConvolution factors n = 0
    rw [factorConvolution_zero_above_upper factors hn, mul_zero]
  rw [hf]
  exact halfLineDirichletPolynomial_characterTwist_eq_prefixPolynomial
    (dynamicComponentScalarValue zbag mbag • factorConvolution factors)
    hCY hN hsupp chi t

theorem shortPrefixNormField_eq_norm_prefixPolynomial
    {q N : ℕ} (f : ArithmeticFunction ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    shortPrefixNormField q N (f : ℕ → ℂ) chi t =
      ‖prefixPolynomial q N f chi t‖ := by
  unfold shortPrefixNormField shortPrefixPolynomial
  rw [prefixPolynomial_eq_twistedFinitePolynomial]

theorem perron_full_carrier_eq_factored_one
    {X : ℝ} (hX : 1 ≤ X) {K k q : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ) (beta : NatDyadicFactor)
    (htail : (sortedComponentFactorList logIndex zbag mbag).drop s = [beta])
    (U t : ℝ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let Y := (factorLowerProduct factors : ℝ)
    let C := (2 : ℝ) ^ (2 * K)
    let small := factors.take s
    characterMovingMass
        (fun chi : DirichletCharacter ℂ q => fun v =>
          ‖halfLineDirichletPolynomial Y C
            (characterTwist (fun n => chi n)
              (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖) U t =
      factoredTypeD12Mass
        (shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small))
        (sourceSmoothNorm q beta) (optionalSmoothNorm q none) U t := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let Y := (factorLowerProduct factors : ℝ)
  let C := (2 : ℝ) ^ (2 * K)
  let small := factors.take s
  have hone : ∀ f ∈ factors, 1 ≤ f.length := fun f hf =>
    dynamicComponentFactorList_length_one logIndex zbag mbag hf
  have hcarry := perron_full_carrier_eq_prefixPolynomial
    (q := q) hX hK hk logIndex zbag mbag
  unfold characterMovingMass factoredTypeD12Mass movingIntegral
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro v hv
  have hpoint := hcarry chi v
  dsimp only at hpoint
  have hshort :
      shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi v =
        ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ := by
    rw [shortPrefixCoefficient_eq_smul]
    exact shortPrefixNormField_eq_norm_prefixPolynomial _ _ _
  calc
    ‖halfLineDirichletPolynomial Y C
        (characterTwist (fun n => chi n)
          (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖ =
        ‖prefixPolynomial q (factorUpperProduct factors)
          (dynamicComponentScalarValue zbag mbag • factorConvolution factors)
          chi v‖ := congrArg norm hpoint
    _ = ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ * sourceSmoothNorm q beta chi v := by
      simpa [sourceSmoothNorm, optionalSmoothNorm, small] using
        (norm_prefix_tail_one (q := q) (dynamicComponentScalarValue zbag mbag)
          factors hone s beta htail chi v)
    _ = (fun x =>
        shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi x *
          (sourceSmoothNorm q beta chi x * optionalSmoothNorm q none chi x)) v := by
      change ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ * sourceSmoothNorm q beta chi v =
        shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi v *
          (sourceSmoothNorm q beta chi v * optionalSmoothNorm q none chi v)
      rw [hshort]
      simp [optionalSmoothNorm]

theorem perron_full_carrier_eq_factored_two
    {X : ℝ} (hX : 1 ≤ X) {K k q : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ) (beta gamma : NatDyadicFactor)
    (htail : (sortedComponentFactorList logIndex zbag mbag).drop s =
      [beta, gamma]) (U t : ℝ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let Y := (factorLowerProduct factors : ℝ)
    let C := (2 : ℝ) ^ (2 * K)
    let small := factors.take s
    characterMovingMass
        (fun chi : DirichletCharacter ℂ q => fun v =>
          ‖halfLineDirichletPolynomial Y C
            (characterTwist (fun n => chi n)
              (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖) U t =
      factoredTypeD12Mass
        (shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small))
        (sourceSmoothNorm q beta) (optionalSmoothNorm q (some gamma)) U t := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let Y := (factorLowerProduct factors : ℝ)
  let C := (2 : ℝ) ^ (2 * K)
  let small := factors.take s
  have hone : ∀ f ∈ factors, 1 ≤ f.length := fun f hf =>
    dynamicComponentFactorList_length_one logIndex zbag mbag hf
  have hcarry := perron_full_carrier_eq_prefixPolynomial
    (q := q) hX hK hk logIndex zbag mbag
  have hshort (chi : DirichletCharacter ℂ q) (v : ℝ) :
      shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi v =
        ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ := by
    rw [shortPrefixCoefficient_eq_smul]
    exact shortPrefixNormField_eq_norm_prefixPolynomial _ _ _
  unfold characterMovingMass factoredTypeD12Mass movingIntegral
  apply Finset.sum_congr rfl
  intro chi hchi
  apply intervalIntegral.integral_congr
  intro v hv
  have hpoint := hcarry chi v
  dsimp only at hpoint
  calc
    ‖halfLineDirichletPolynomial Y C
        (characterTwist (fun n => chi n)
          (dynamicPreliminaryComponent (some logIndex) zbag mbag)) v‖ =
        ‖prefixPolynomial q (factorUpperProduct factors)
          (dynamicComponentScalarValue zbag mbag • factorConvolution factors)
          chi v‖ := congrArg norm hpoint
    _ = ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ * sourceSmoothNorm q beta chi v *
          optionalSmoothNorm q (some gamma) chi v := by
      simpa [sourceSmoothNorm, optionalSmoothNorm, small, mul_assoc] using
        (norm_prefix_tail_two (q := q) (dynamicComponentScalarValue zbag mbag)
          factors hone s beta gamma htail chi v)
    _ = (fun x =>
        shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi x *
          (sourceSmoothNorm q beta chi x * optionalSmoothNorm q (some gamma) chi x)) v := by
      dsimp
      change ‖prefixPolynomial q (factorUpperProduct small)
          (dynamicComponentScalarValue zbag mbag • factorConvolution small)
          chi v‖ * sourceSmoothNorm q beta chi v *
          optionalSmoothNorm q (some gamma) chi v =
        shortPrefixNormField q (factorUpperProduct small)
          (shortPrefixCoefficient zbag mbag small) chi v *
          (sourceSmoothNorm q beta chi v *
            optionalSmoothNorm q (some gamma) chi v)
      rw [hshort chi v]
      simp [mul_assoc]

end
end MRTDynamicD12CarrierIdentities

#print axioms
  MRTDynamicD12CarrierIdentities.halfLineDirichletPolynomial_characterTwist_eq_prefixPolynomial
