import MRTLemma215DynamicHighPacketIndexV3
import FarAnnulusMRTConnector

/-!
# Mixed-mean transport for literal dynamic high packets

Character twisting, zero padding, and the real Perron scale are applied to
the actual packet coefficients.  Their losses are absorbed into a
packet-local logarithmic exponent before invoking the certified mixed-mean
lemma with the honest constant `c=1/2`.
-/

namespace MRTLemma215DynamicHighPacketMixedMeanV3

open scoped BigOperators ArithmeticFunction
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel
open MAPHBPerronSourceData
open MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicHighPacketIndexV3

noncomputable section

theorem paddedCharacterTwist_bound
    {q : ℕ} [NeZero q] (f : ℕ → ℂ) (B : ℕ → ℝ)
    (hB : ∀ n, 0 ≤ B n) (hf : ∀ n, ‖f n‖ ≤ B n) :
    ∀ chi n, ‖paddedCharacterTwist q q le_rfl f chi n‖ ≤ B n := by
  unfold paddedCharacterTwist
  apply zeroPadFamily_bound
  · exact hB
  · intro chi n
    rw [norm_mul]
    calc
      ‖chi n‖ * ‖f n‖ ≤ 1 * B n :=
        mul_le_mul (chi.norm_le_one n) (hf n) (norm_nonneg _) zero_le_one
      _ = B n := one_mul _

/-- A fixed real scaling of a dyadically supported log-power coefficient can
be absorbed into a larger log-power exponent. -/
theorem exists_scaledPaddedPacketBounds
    {q M N a₀ k : ℕ} [NeZero q]
    (hM : 2 ≤ M) (hN : 2 ≤ N) (c : ℝ)
    (short long : ℕ → ℂ)
    (hshortSupport : SupportedNatDyadic M short)
    (hlongSupport : SupportedNatDyadic N long)
    (hshort : ∀ n ∈ DeterminantCountWeld.dyadic M,
      ‖short n‖ ≤ Real.log (2 * (n : ℝ)) ^ a₀)
    (hlong : ∀ n ∈ DeterminantCountWeld.dyadic N,
      ‖long n‖ ≤ (MixedMellinCert.tauAF k n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ a₀) :
    ∃ a : ℕ,
      (∀ chi n, n ∈ DeterminantCountWeld.dyadic M →
        ‖paddedCharacterTwist q q le_rfl short chi n‖ ≤
          Real.log (2 * (n : ℝ)) ^ a) ∧
      (∀ chi n, n ∈ DeterminantCountWeld.dyadic N →
        ‖scaleCoeffFamily c (paddedCharacterTwist q q le_rfl long) chi n‖ ≤
          (MixedMellinCert.tauAF k n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a) := by
  let base := Real.log (2 * ((N + 1 : ℕ) : ℝ))
  obtain ⟨e, he⟩ := exists_nat_pow_ge_of_one_lt
    (C := |c|) (by simpa [base] using one_lt_log_two_mul_succ hN)
  let a := a₀ + e
  have hlogPowNonneg : ∀ n : ℕ,
      0 ≤ Real.log (2 * (n : ℝ)) ^ a₀ := by
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp
    · exact pow_nonneg
        (log_two_mul_nonneg (Nat.one_le_iff_ne_zero.mpr hn0)) _
  refine ⟨a, ?_, ?_⟩
  · have hpadded := paddedCharacterTwist_bound (q := q) short
      (fun n => Real.log (2 * (n : ℝ)) ^ a₀)
      hlogPowNonneg (fun n => by
        by_cases hn : n ∈ DeterminantCountWeld.dyadic M
        · exact hshort n hn
        · rw [hshortSupport n hn]
          simp
          exact hlogPowNonneg n)
    intro chi n hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hlogOne := one_le_log_two_mul_of_two_le hn2
    exact (hpadded chi n).trans
      (pow_le_pow_right₀ hlogOne (by simp [a]))
  · intro chi n hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    have hlongPad := paddedCharacterTwist_bound (q := q) long
      (fun d => (MixedMellinCert.tauAF k d : ℝ) *
        Real.log (2 * (d : ℝ)) ^ a₀)
      (fun d => mul_nonneg (by positivity) (hlogPowNonneg d)) (fun d => by
        by_cases hd : d ∈ DeterminantCountWeld.dyadic N
        · exact hlong d hd
        · rw [hlongSupport d hd]
          simp
          exact mul_nonneg (by positivity) (hlogPowNonneg d))
    have hbaseLe : base ≤ Real.log (2 * (n : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.mul_le_mul_left 2 (by
        have := (Finset.mem_Ioc.mp hn).1
        omega : N + 1 ≤ n)
    have hbaseNonneg : 0 ≤ base :=
      (one_lt_log_two_mul_succ hN).le.trans' zero_le_one
    have hlogNonneg := log_two_mul_nonneg (show 1 ≤ n by omega)
    have hpow := pow_le_pow_left₀ hbaseNonneg hbaseLe e
    have he' : |c| ≤ base ^ e := by simpa [base] using he
    unfold scaleCoeffFamily
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      |c| * ‖paddedCharacterTwist q q le_rfl long chi n‖ ≤
          base ^ e * ((MixedMellinCert.tauAF k n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a₀) :=
        mul_le_mul he' (hlongPad chi n) (norm_nonneg _)
          (pow_nonneg hbaseNonneg _)
      _ ≤ Real.log (2 * (n : ℝ)) ^ e *
          ((MixedMellinCert.tauAF k n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a₀) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ = (MixedMellinCert.tauAF k n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ a := by
        simp only [a, pow_add]
        ring

/-- Actual character-padded, Perron-scaled coefficients of one literal packet
satisfy the manuscript coefficient hypotheses. -/
theorem highPacket_exists_paddedScaledBoundsV3
    {q K : ℕ} [NeZero q]
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (perronScale : ℝ) :
    ∃ a : ℕ,
      (∀ chi n, n ∈ DeterminantCountWeld.dyadic
          (highPacketShortLengthV3 packet) →
        ‖paddedCharacterTwist q q le_rfl
            (highPacketShortCoeffV3 packet) chi n‖ ≤
          Real.log (2 * (n : ℝ)) ^ a) ∧
      (∀ chi n, n ∈ DeterminantCountWeld.dyadic
          (highPacketLongLengthV3 packet) →
        ‖scaleCoeffFamily perronScale
            (paddedCharacterTwist q q le_rfl
              (highPacketLongCoeffV3 packet)) chi n‖ ≤
          (MixedMellinCert.tauAF (highComplementV3 packet.1).length n : ℝ) *
            Real.log (2 * (n : ℝ)) ^ a) := by
  obtain ⟨a₀, hshort, hlong⟩ :=
    highPacket_exists_coefficientBoundsV3 packet
  have hgeom := highPacket_geometryV3 packet
  have hsupp := highPacket_supportV3 packet
  exact exists_scaledPaddedPacketBounds hgeom.1 hgeom.2.1 perronScale
    (highPacketShortCoeffV3 packet) (highPacketLongCoeffV3 packet)
    hsupp.1 hsupp.2 hshort hlong

/-- Certified mixed-mean bound for one actual V3 high packet after character
padding and Perron scaling. -/
theorem exists_highPacket_mixedMass_boundV3
    {q K : ℕ} [NeZero q]
    {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K)
    (perronScale t₀ T U : ℝ) (hT : 1 ≤ T) (hU : 1 ≤ U) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      characterPairMixedMass q
        (highPacketShortLengthV3 packet)
        (highPacketLongLengthV3 packet)
        (pairShortFamily (paddedCharacterTwist q q le_rfl
          (highPacketShortCoeffV3 packet)))
        (pairLongFamily (scaleCoeffFamily perronScale
          (paddedCharacterTwist q q le_rfl
            (highPacketLongCoeffV3 packet))))
        t₀ T U ≤
      U * (q : ℝ) ^ 2 * C *
        Real.log (2 * (highPacketShortLengthV3 packet : ℝ) *
          (highPacketLongLengthV3 packet : ℝ)) ^
          (4 * a + 2 * max 2
            ((highComplementV3 packet.1).length *
              (highComplementV3 packet.1).length) + 2) *
        (U * T + U * (highPacketLongLengthV3 packet : ℝ) +
          (highPacketShortLengthV3 packet : ℝ) *
            (highPacketLongLengthV3 packet : ℝ) + T) := by
  obtain ⟨a, hshort, hlong⟩ :=
    highPacket_exists_paddedScaledBoundsV3 (q := q) packet perronScale
  have hgeom := highPacket_geometryV3 packet
  have hk := highComplementV3_length_one hX hdelta packet.1
  have hcoeff := pairFamilies_coefficientBounds hshort hlong
  obtain ⟨C, hC, hbound⟩ := exists_characterPairMixedMass_bound
    (c := (1 / 2 : ℝ)) (a := a)
    (k := (highComplementV3 packet.1).length)
    (by norm_num) hk hgeom.1 hgeom.2.1 hgeom.2.2
    hT hU _ _ hcoeff
  exact ⟨a, C, hC, hbound⟩

end
end MRTLemma215DynamicHighPacketMixedMeanV3

#print axioms MRTLemma215DynamicHighPacketMixedMeanV3.highPacket_exists_paddedScaledBoundsV3
#print axioms MRTLemma215DynamicHighPacketMixedMeanV3.exists_highPacket_mixedMass_boundV3
