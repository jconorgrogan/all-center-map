import MRTLemma215DynamicHighPacketMixedMeanV3
import MRTLemma215DynamicMultiplicityBoundsV3
import MRTLemma215DynamicTypeIIFiniteEnvelopeV3

/-! # Fixed-order coefficient exponents for every unscaled high packet -/

namespace MRTLemma215DynamicHighUniformUnscaledV3

open scoped BigOperators
open MAPDynamicHBSourceV3 MAPHBPerronSourceData
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215DynamicHighPacketCertificateV3 MRTLemma215DynamicHighPacketIndexV3
open MRTLemma215DynamicMultiplicityBoundsV3 MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel MixedMeanFrontend
open MAPNormalizedWrapper ShiuFinalCertification
open MRTLemma215DynamicHighPacketMixedMeanV3

noncomputable section
set_option maxHeartbeats 1200000

theorem exists_fixedOrder_selectedFactor_log_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ a : ℕ, ∀ {X : ℝ} {k : ℕ}, k < K →
      ∀ (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
      (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
      (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
      (short : NatDyadicFactor),
      short ∈ sortedComponentFactorList logIndex zbag mbag → 2 ≤ short.length →
      ∀ n ∈ DeterminantCountWeld.dyadic short.length,
        ‖(scaledSelectedFactor zbag mbag short).coeff n‖ ≤ Real.log (2 * (n : ℝ)) ^ a := by
  let S : ℝ := ((K ^ (K + 1) * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)
  have hbase : 1 < Real.log (6 : ℝ) := by
    exact (Real.lt_log_iff_exp_lt (by norm_num)).2 (Real.exp_one_lt_three.trans (by norm_num))
  obtain ⟨e, he⟩ := exists_nat_pow_ge_of_one_lt (C := S) hbase
  refine ⟨e + 2, ?_⟩
  intro X k hk logIndex zbag mbag short hmem hM n hn
  have hscalar := norm_dynamicComponentScalarValue_le zbag mbag
  have hS : ‖dynamicComponentScalarValue zbag mbag‖ ≤ S := by
    apply hscalar.trans
    dsimp [S]
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul
      (pow_le_pow_right₀ hK (show k + 1 ≤ K + 1 by omega))
      (Nat.factorial_le (show k ≤ K by omega))) (Nat.factorial_le (show k + 1 ≤ K by omega))
  have hn3 : 3 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
  have hlog : 0 ≤ Real.log (2 * (n : ℝ)) := log_two_mul_nonneg (by omega)
  have hmono : Real.log (6 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    exact_mod_cast (show 6 ≤ 2 * n by omega)
  have hp : S ≤ Real.log (2 * (n : ℝ)) ^ e :=
    he.trans (pow_le_pow_left₀ (by linarith) hmono e)
  have hraw := sortedDynamicComponentFactor_coeff_le_logSq logIndex zbag mbag hmem n
  change ‖(dynamicComponentScalar zbag mbag * short.coeff) n‖ ≤ _
  rw [dynamicComponentScalar_mul_eq_smul]
  change ‖dynamicComponentScalarValue zbag mbag * short.coeff n‖ ≤ _
  rw [norm_mul, pow_add]
  exact mul_le_mul (hS.trans hp) hraw (norm_nonneg _) (pow_nonneg hlog _)

/-- The exponent and divisor order are fixed before `X`, every component,
and every high packet; no packet-local logarithmic choice remains. -/
theorem exists_fixedOrder_highPacket_coefficientBounds (K : ℕ) (hK : 1 ≤ K) :
    ∃ a : ℕ, ∀ {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
      (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K),
      (∀ n ∈ DeterminantCountWeld.dyadic (highPacketShortLengthV3 packet),
        ‖highPacketShortCoeffV3 packet n‖ ≤ Real.log (2 * (n : ℝ)) ^ a) ∧
      (∀ n ∈ DeterminantCountWeld.dyadic (highPacketLongLengthV3 packet),
        ‖highPacketLongCoeffV3 packet n‖ ≤
          (MixedMellinCert.tauAF (2 * K) n : ℝ) * Real.log (2 * (n : ℝ)) ^ a) := by
  obtain ⟨a₀, hshort⟩ := exists_fixedOrder_selectedFactor_log_bound K hK
  refine ⟨max a₀ (4 * K), ?_⟩
  intro X delta H₀ hX hdelta packet
  let factors := highFactorsV3 packet.1
  let s := highSelectedIndexV3 packet.1
  have hk := (rawBranchV3 packet.1.1).isLt
  have hflen := sortedComponentFactorList_length_le
    (rawLogIndexV3 packet.1.1) (rawZetaBagV3 packet.1.1) (rawMoebiusBagV3 packet.1.1)
  have hlen : (highComplementV3 packet.1).length ≤ 2 * K := by
    dsimp [highComplementV3, complementFactorList]
    simp only [List.length_append, List.length_take, List.length_drop]
    dsimp [rawBranchV3] at hk
    dsimp [highFactorsV3] at *
    omega
  constructor
  · intro n hn
    have hs := hshort hk (rawLogIndexV3 packet.1.1) (rawZetaBagV3 packet.1.1)
      (rawMoebiusBagV3 packet.1.1) (highSelectedFactorV3 hX hdelta packet.1)
      (List.getElem_mem (highSelectedIndexIsLtV3 hX hdelta packet.1))
      (highSelectedFactorV3_two hX hdelta packet.1) n hn
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; have := (highPacket_geometryV3 packet).1; omega
    exact hs.trans (pow_le_pow_right₀ (one_le_log_two_mul_of_two_le hn2) (Nat.le_max_left _ _))
  · intro n hn
    have hn2 : 2 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; have := (highPacket_geometryV3 packet).2.1; omega
    have hb := dyadicComplement_norm_le (rawLogIndexV3 packet.1.1)
      (rawZetaBagV3 packet.1.1) (rawMoebiusBagV3 packet.1.1)
      (highSelectedIndexV3 packet.1) packet.2.1 hn2
    have htau : (MixedMellinCert.tauAF (highComplementV3 packet.1).length n : ℝ) ≤
        (MixedMellinCert.tauAF (2 * K) n : ℝ) := by
      exact_mod_cast ShiuAnalyticLayer.tauAF_mono_order hlen n
    have hpow := pow_le_pow_right₀ (one_le_log_two_mul_of_two_le hn2)
      (show 2 * (highComplementV3 packet.1).length ≤ max a₀ (4 * K) by omega)
    exact hb.trans (mul_le_mul htau hpow
      (pow_nonneg ((one_le_log_two_mul_of_two_le hn2).trans' zero_le_one) _) (by positivity))

/-- The mixed-mean constant is quantified before the modulus, lengths and
coefficient families, as in the certified manuscript lemma. -/
theorem exists_uniform_characterPairMixedMass_bound
    (a k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M N : ℕ) (t₀ T U : ℝ)
      (beta long : Fin q → Fin q → ℕ → ℂ),
      2 ≤ M → 2 ≤ N → (1 / 2 : ℝ) * (M : ℝ) ^ 2 ≤ N →
      1 ≤ T → 1 ≤ U →
      (∀ chi chi', PaperCoefficientBounds M N a k (beta chi chi') (long chi chi')) →
      characterPairMixedMass q M N beta long t₀ T U ≤
        U * (q : ℝ) ^ 2 * C * Real.log (2 * (M : ℝ) * N) ^
          (4 * a + 2 * max 2 (k * k) + 2) *
          (U * T + U * (N : ℝ) + (M : ℝ) * N + T) := by
  obtain ⟨C, hC, hb⟩ := certifiedPaperMixedMeanLemma21 (1 / 2 : ℝ) a k (by norm_num) hk
  refine ⟨C, hC, ?_⟩
  intro q M N t₀ T U beta long hM hN hMN hT hU hcoeff
  let E := C * Real.log (2 * (M : ℝ) * N) ^ (4 * a + 2 * max 2 (k * k) + 2) *
    (U * T + U * (N : ℝ) + (M : ℝ) * N + T)
  have hsum : (∑ chi : Fin q, ∑ chi' : Fin q,
      (MixedMeanMajorantWeld.paperLiteralMixedMean M N (beta chi chi') (long chi chi') t₀ T U).re) ≤
      (q : ℝ) ^ 2 * E := by
    calc
      _ ≤ ∑ chi : Fin q, ∑ chi' : Fin q, E := by
        apply Finset.sum_le_sum
        intro chi hc
        apply Finset.sum_le_sum
        intro chi' hc'
        exact hb M N (beta chi chi') (long chi chi') t₀ T U hM hN hMN hT hU (hcoeff chi chi')
      _ = _ := by simp; ring
  have hmul := mul_le_mul_of_nonneg_left hsum (show 0 ≤ U by linarith)
  unfold characterPairMixedMass
  convert hmul using 1 <;> dsimp [E] <;> ring

/-- Uniform mixed mean for the actual unscaled high source packet. Cauchy
and Perron scales should be retained multiplicatively, not converted to
packet-local logarithmic exponents. -/
theorem exists_fixedOrder_highPacket_mixedMass_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
        (q : ℕ) [NeZero q] (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
        (t₀ T U : ℝ), 1 ≤ T → 1 ≤ U →
        characterPairMixedMass q (highPacketShortLengthV3 packet) (highPacketLongLengthV3 packet)
          (pairShortFamily (paddedCharacterTwist q q le_rfl (highPacketShortCoeffV3 packet)))
          (pairLongFamily (paddedCharacterTwist q q le_rfl (highPacketLongCoeffV3 packet))) t₀ T U ≤
          U * (q : ℝ) ^ 2 * C *
            Real.log (2 * (highPacketShortLengthV3 packet : ℝ) * (highPacketLongLengthV3 packet : ℝ)) ^
              (4 * a + 2 * max 2 ((2 * K) * (2 * K)) + 2) *
            (U * T + U * (highPacketLongLengthV3 packet : ℝ) +
              (highPacketShortLengthV3 packet : ℝ) * (highPacketLongLengthV3 packet : ℝ) + T) := by
  obtain ⟨a, hcoeff⟩ := exists_fixedOrder_highPacket_coefficientBounds K hK
  obtain ⟨C, hC, hmean⟩ := exists_uniform_characterPairMixedMass_bound a (2 * K) (by omega)
  refine ⟨a, C, hC, ?_⟩
  intro X delta H₀ hX hdelta q _ packet t₀ T U hT hU
  obtain ⟨hs, hl⟩ := hcoeff packet
  have hsupp := highPacket_supportV3 packet
  have hgeom := highPacket_geometryV3 packet
  have hlog0 (n : ℕ) : 0 ≤ Real.log (2 * (n : ℝ)) ^ a := by
    by_cases hn : n = 0
    · subst n; simp
    · exact pow_nonneg (log_two_mul_nonneg (Nat.one_le_iff_ne_zero.mpr hn)) _
  have hspad := paddedCharacterTwist_bound (q := q) (highPacketShortCoeffV3 packet)
    (fun n => Real.log (2 * (n : ℝ)) ^ a) hlog0 (fun n => by
      by_cases hn : n ∈ DeterminantCountWeld.dyadic (highPacketShortLengthV3 packet)
      · exact hs n hn
      · rw [hsupp.1 n hn, norm_zero]; exact hlog0 n)
  have hlpad := paddedCharacterTwist_bound (q := q) (highPacketLongCoeffV3 packet)
    (fun n => (MixedMellinCert.tauAF (2 * K) n : ℝ) * Real.log (2 * (n : ℝ)) ^ a)
    (fun n => mul_nonneg (by positivity) (hlog0 n)) (fun n => by
      by_cases hn : n ∈ DeterminantCountWeld.dyadic (highPacketLongLengthV3 packet)
      · exact hl n hn
      · rw [hsupp.2 n hn, norm_zero]; exact mul_nonneg (Nat.cast_nonneg _) (hlog0 n))
  exact hmean q _ _ t₀ T U _ _ hgeom.1 hgeom.2.1 hgeom.2.2 hT hU
    (pairFamilies_coefficientBounds (fun chi n hn => hspad chi n) (fun chi n hn => hlpad chi n))

end
end MRTLemma215DynamicHighUniformUnscaledV3

#print axioms MRTLemma215DynamicHighUniformUnscaledV3.exists_fixedOrder_highPacket_coefficientBounds

#print axioms MRTLemma215DynamicHighUniformUnscaledV3.exists_fixedOrder_highPacket_mixedMass_bound
