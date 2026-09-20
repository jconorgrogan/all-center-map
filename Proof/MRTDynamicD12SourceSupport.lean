import MRTDynamicD12PolynomialFactorization
import MRTDynamicD12LiteralMass
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3
import MRTLemma215DynamicHighPacketCertificateV3

/-! # Actual fixed-order support for the dynamic d1/d2 Perron transfer -/
namespace MRTDynamicD12SourceSupport

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTDynamicD12PolynomialFactorization

noncomputable section

theorem factorLowerProduct_one (factors : List NatDyadicFactor)
    (hone : ∀ f ∈ factors, 1 ≤ f.length) : 1 ≤ factorLowerProduct factors := by
  induction factors with
  | nil => simp
  | cons f factors ih =>
      rw [factorLowerProduct_cons]
      exact Nat.succ_le_iff.mpr (Nat.mul_pos
        (by have := hone f (by simp); omega)
        (by have := ih (fun g hg => hone g (by simp [hg])); omega))

/-- The actual lower product is the Perron scale. Its fixed support dilation
keeps every dyadic factor of two visible and depends only on the HB order. -/
theorem factorConvolution_supportedNear
    (factors : List NatDyadicFactor) (hne : factors ≠ [])
    (hone : ∀ f ∈ factors, 1 ≤ f.length)
    {C : ℝ} (hC : 1 ≤ C) (hpow : (2 : ℝ)^factors.length ≤ C) :
    SupportedNear (factorLowerProduct factors : ℝ) C (factorConvolution factors) := by
  intro n hn
  have hY : 0 ≤ (factorLowerProduct factors : ℝ) := by positivity
  obtain ⟨head, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  rcases hn with hlo | hhi
  · have hdiv : (factorLowerProduct (head :: tail) : ℝ) / C ≤
        factorLowerProduct (head :: tail) := div_le_self hY hC
    have hnle : n ≤ factorLowerProduct (head :: tail) := by
      exact_mod_cast (hlo.trans_le hdiv).le
    exact factorConvolution_zero_of_le head tail hnle
  · have hu : (factorUpperProduct (head :: tail) : ℝ) ≤
        C * factorLowerProduct (head :: tail) := by
      rw [factorUpperProduct_eq_pow_mul_lowerProduct]
      push_cast
      exact mul_le_mul_of_nonneg_right hpow hY
    have hnhi : factorUpperProduct (head :: tail) < n := by
      exact_mod_cast hu.trans_lt hhi
    exact factorConvolution_zero_of_upperProduct_lt head tail hnhi

/-- Fixed-order support of the unmasked component, including its exact
signed binomial and multinomial scalar. -/
theorem dynamicPreliminaryComponent_supportedNear_fixedOrder
    {X : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k+1)) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    SupportedNear (factorLowerProduct factors : ℝ) ((2 : ℝ)^(2*K))
      (dynamicPreliminaryComponent (some logIndex) zbag mbag) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  have hlen : factors.length ≤ 2*K := by
    have h := sortedComponentFactorList_length_le logIndex zbag mbag
    dsimp [factors]
    omega
  have hne : factors ≠ [] := by
    intro h
    have hperm := sortedComponentFactorList_perm logIndex zbag mbag
    have hlength := hperm.length_eq
    change factors.length = _ at hlength
    rw [h] at hlength
    simp [dynamicComponentFactorList] at hlength
  have hone : ∀ f ∈ factors, 1 ≤ f.length := fun f hf =>
    dynamicComponentFactorList_length_one logIndex zbag mbag hf
  have hsupport := factorConvolution_supportedNear factors hne hone
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hlen)
  rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK,
    ← factorConvolution_sortedComponentFactorList logIndex zbag mbag,
    dynamicComponentScalar_mul_eq_smul]
  intro n hn
  change dynamicComponentScalarValue zbag mbag * factorConvolution factors n = 0
  rw [hsupport n hn, mul_zero]

end
end MRTDynamicD12SourceSupport

#print axioms MRTDynamicD12SourceSupport.dynamicPreliminaryComponent_supportedNear_fixedOrder
