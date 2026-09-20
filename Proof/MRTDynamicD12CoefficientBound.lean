import MRTLemma215DynamicCoefficientBoundsV3
import MRTLemma215DynamicHighPointwiseV3
import MRTLemma215DynamicMultiplicityBoundsV3
import MRTDynamicD12SourceSupport
import MRTDynamicD12LiteralMass
import MRTCorollary25TypeD1CoefficientBound

/-! First serialized coefficient weld.  The bound is pointwise in `n`, with
one fixed constant before `X` and all source bags.  It is deliberately not an
L1 coefficient sum. -/
namespace MRTDynamicD12CoefficientBound

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open CGLProofDAG FixedCharacterPoweredBridge
open MAPMRTCorollary25 MAPMRTCorollary25TypeD1CoefficientBound
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicMultiplicityBoundsV3
open MRTLemma215DynamicHighPointwiseV3
open MRTDynamicD12LiteralMass
open MRTDynamicD12SourceSupport
open MixedMellinCert ShiuAnalyticLayer

noncomputable section

set_option maxHeartbeats 1000000

def d12ScalarMajorant (K : ℕ) : ℝ :=
  ((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)

theorem d12ScalarMajorant_nonneg (K : ℕ) :
    0 ≤ d12ScalarMajorant K := by
  unfold d12ScalarMajorant
  positivity

theorem norm_dynamicComponentScalarValue_le_majorant
    {X : ℝ} {K k : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    ‖dynamicComponentScalarValue zbag mbag‖ ≤
      d12ScalarMajorant K := by
  have h := norm_dynamicComponentScalarValue_le zbag mbag
  unfold d12ScalarMajorant
  refine h.trans ?_
  exact_mod_cast Nat.mul_le_mul
    (Nat.mul_le_mul
      (pow_le_pow_right₀ hK (show k + 1 ≤ K by omega))
      (Nat.factorial_le (show k ≤ K by omega)))
    (Nat.factorial_le (show k + 1 ≤ K by omega))

theorem sorted_factorConvolution_norm_le
    {X : ℝ} {K k n : ℕ} (hn : 2 ≤ n)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    ‖factorConvolution factors n‖ ≤
      (tauAF factors.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * factors.length) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  have hn0 : n ≠ 0 := by omega
  have hA : 0 ≤ Real.log (2 * (n : ℝ)) ^ 2 := sq_nonneg _
  have hcoeff : ∀ f ∈ factors, ∀ d, d ∣ n →
      ‖f.coeff d‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
    intro f hf d hd
    have hbase := sortedDynamicComponentFactor_coeff_le_logSq
      logIndex zbag mbag hf d
    have hd0 : d ≠ 0 := by
      intro hdz
      subst d
      exact hn0 (by simpa using hd)
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
    have hlogNonneg : 0 ≤ Real.log (2 * (d : ℝ)) :=
      log_two_mul_nonneg (by omega)
    have hlogLe : Real.log (2 * (d : ℝ)) ≤
        Real.log (2 * (n : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.mul_le_mul_left 2 hdle
    exact hbase.trans (pow_le_pow_left₀ hlogNonneg hlogLe 2)
  have hbound := factorConvolution_norm_le_tauAF_const factors hn0 hA
    hcoeff (dvd_refl n)
  simpa [pow_mul] using hbound

theorem exists_fixedOrder_fullComponent_coefficient_bound
    (K : ℕ) (hK : 1 ≤ K) :
    ∃ S : ℝ, 0 < S ∧
      ∀ {X : ℝ} {k : ℕ}, k < K →
        ∀ (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
          (zbag : Sym (Option (Fin (sourceDyadicCount
            (hbFactorCutoff X)))) k)
          (mbag : Sym (Option (Fin (sourceDyadicCount
            ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) (n : ℕ),
          ‖(dynamicComponentScalarValue zbag mbag •
              factorConvolution
                (sortedComponentFactorList logIndex zbag mbag)) n‖ ≤
            S * (tauAF (2 * K) n : ℝ) *
              Real.log (2 * (n : ℝ)) ^ (4 * K) := by
  let S : ℝ := d12ScalarMajorant K + 1
  refine ⟨S, by dsimp [S]; linarith [d12ScalarMajorant_nonneg K], ?_⟩
  intro X k hk logIndex zbag mbag n
  let factors := sortedComponentFactorList logIndex zbag mbag
  have hlen : factors.length ≤ 2 * K := by
    dsimp [factors]
    have := sortedComponentFactorList_length_le logIndex zbag mbag
    omega
  have hscalar := norm_dynamicComponentScalarValue_le_majorant hK hk zbag mbag
  change ‖dynamicComponentScalarValue zbag mbag * factorConvolution factors n‖ ≤ _
  rw [norm_mul]
  by_cases hn : 2 ≤ n
  · have hconv := sorted_factorConvolution_norm_le hn logIndex zbag mbag
    have htau : (tauAF factors.length n : ℝ) ≤
        (tauAF (2 * K) n : ℝ) := by
      exact_mod_cast tauAF_mono_order hlen n
    have hlog1 : 1 ≤ Real.log (2 * (n : ℝ)) :=
      one_le_log_two_mul_of_two_le hn
    have hpow : Real.log (2 * (n : ℝ)) ^ (2 * factors.length) ≤
        Real.log (2 * (n : ℝ)) ^ (4 * K) :=
      pow_le_pow_right₀ hlog1 (by omega)
    have hS : ‖dynamicComponentScalarValue zbag mbag‖ ≤ S := by
      dsimp [S]
      linarith [d12ScalarMajorant_nonneg K]
    have hS0 : 0 ≤ S := by
      dsimp [S]
      linarith [d12ScalarMajorant_nonneg K]
    calc
      ‖dynamicComponentScalarValue zbag mbag‖ *
          ‖factorConvolution factors n‖ ≤
          S * ((tauAF factors.length n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ (2 * factors.length)) :=
        mul_le_mul hS hconv (norm_nonneg _) (by
          dsimp [S]
          linarith [d12ScalarMajorant_nonneg K])
      _ ≤ S * ((tauAF (2 * K) n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (4 * K)) := by
        gcongr
      _ = _ := by ring
  · have hn1 : n = 0 ∨ n = 1 := by omega
    have hzero : factorConvolution factors n = 0 := by
      rcases hn1 with rfl | rfl
      · exact (factorConvolution factors).map_zero'
      · have hne : factors ≠ [] := by
          intro h
          have hperm := sortedComponentFactorList_perm logIndex zbag mbag
          have hlen' := hperm.length_eq
          change factors.length = _ at hlen'
          rw [h] at hlen'
          simp [dynamicComponentFactorList] at hlen'
        obtain ⟨head, tail, hcons⟩ := List.exists_cons_of_ne_nil hne
        have hmem : ∀ f ∈ head :: tail, f ∈
            sortedComponentFactorList logIndex zbag mbag := by
          intro f hf
          have hperm := sortedComponentFactorList_perm logIndex zbag mbag
          have hf_factors : f ∈ factors := by
            rw [hcons]
            exact hf
          simpa [factors] using hf_factors
        have hone : 1 ≤ factorLowerProduct (head :: tail) :=
          factorLowerProduct_one (head :: tail) (fun f hf =>
            dynamicComponentFactorList_length_one logIndex zbag mbag
              (hmem f hf))
        rw [hcons]
        exact factorConvolution_zero_of_le head tail (by omega)
    have hS0 : 0 ≤ S := by
      dsimp [S]
      linarith [d12ScalarMajorant_nonneg K]
    rw [hzero]
    have hlog0 : 0 ≤ Real.log (2 * (n : ℝ)) ^ (4 * K) := by
      rcases hn1 with rfl | rfl
      · simp
      · have hlog2 : 0 ≤ Real.log (2 : ℝ) :=
          Real.log_nonneg (by norm_num)
        simpa using (pow_nonneg hlog2 (4 * K))
    have hτ : 0 ≤ (tauAF (2 * K) n : ℝ) := Nat.cast_nonneg _
    simp only [norm_zero, mul_zero]
    exact mul_nonneg (mul_nonneg hS0 hτ) hlog0

end
end MRTDynamicD12CoefficientBound
