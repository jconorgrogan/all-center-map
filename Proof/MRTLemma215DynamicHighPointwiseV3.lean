import MRTLemma215DynamicHighUniformUnscaledV3
import MRTCorollary25TypeD1CoefficientBound

/-! Uniform pointwise bounds for the literal unscaled high-packet convolution.
The subpower constant is chosen before every packet and analytic parameter. -/
namespace MRTLemma215DynamicHighPointwiseV3
open scoped BigOperators
open MAPHBPerronSourceData CGLProofDAG FixedCharacterPoweredBridge
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215DynamicHighUniformUnscaledV3
open MAPMRTCorollary25TypeD1CoefficientBound MAPMRTCorollary25TypeD1LiteralWeld
noncomputable section

lemma log_two_mul_pow_le (a n : ℕ) (hn : 1 ≤ n) :
    Real.log (2 * (n : ℝ)) ^ a ≤
      (2 : ℝ) ^ a * Real.log (2 + (n : ℝ)) ^ a := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < 2 + (n : ℝ) := by positivity
  have hlog : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (2 + (n : ℝ)) := by
    rw [show 2 * Real.log (2 + (n : ℝ)) =
        Real.log (2 + (n : ℝ)) + Real.log (2 + (n : ℝ)) by ring,
      ← Real.log_mul hpos.ne' hpos.ne']
    apply Real.log_le_log (by positivity)
    nlinarith
  simpa only [mul_pow] using pow_le_pow_left₀
    (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * n)) hlog a

lemma supportedDyadic_of_supportedNatDyadic {M : ℕ} {f : ℕ → ℂ}
    (hf : SupportedNatDyadic M f) : SupportedDyadic (M : ℝ) f := by
  intro n hn
  apply hf n
  intro hmem
  apply hn
  have hh := Finset.mem_Ioc.mp hmem
  constructor
  · exact_mod_cast hh.1.le
  · exact_mod_cast hh.2

/-- The fixed-order logarithmic exponent yields global divisor-log envelopes.
The short factor contains the original HB scalar; it is not renormalized here. -/
theorem exists_fixedOrder_highPacket_divisorLogMajorized (K : ℕ) (hK : 1 ≤ K) :
    ∃ a : ℕ, ∀ {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
      (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K),
      DivisorLogMajorized 1 a ((2 : ℝ) ^ a) (highPacketShortCoeffV3 packet) ∧
      DivisorLogMajorized (2 * K) a ((2 : ℝ) ^ a) (highPacketLongCoeffV3 packet) := by
  obtain ⟨a, hcoeff⟩ := exists_fixedOrder_highPacket_coefficientBounds K hK
  refine ⟨a, ?_⟩
  intro X delta H₀ hX hdelta packet
  obtain ⟨hs, hl⟩ := hcoeff packet
  have hsupp := highPacket_supportV3 packet
  have hgeom := highPacket_geometryV3 packet
  have hnonneg (r n : ℕ) : 0 ≤ (2 : ℝ) ^ a * (orderedDivisorCount r n : ℝ) *
      Real.log (2 + (n : ℝ)) ^ a := by
    apply mul_nonneg (by positivity)
    exact pow_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) _
  constructor
  · intro n
    by_cases hn : n ∈ DeterminantCountWeld.dyadic (highPacketShortLengthV3 packet)
    · have hnpos : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hdiv : orderedDivisorCount 1 n = 1 := by
        simp [orderedDivisorCount, ArithmeticFunction.zeta_apply, Nat.ne_of_gt hnpos]
      rw [hdiv, Nat.cast_one, mul_one]
      exact (hs n hn).trans (log_two_mul_pow_le a n hnpos)
    · rw [hsupp.1 n hn, norm_zero]
      exact hnonneg 1 n
  · intro n
    by_cases hn : n ∈ DeterminantCountWeld.dyadic (highPacketLongLengthV3 packet)
    · have hnpos : 0 < n := by have := (Finset.mem_Ioc.mp hn).1; omega
      rw [orderedDivisorCount_eq_tauAF]
      calc
        _ ≤ (MixedMellinCert.tauAF (2 * K) n : ℝ) * Real.log (2 * (n : ℝ)) ^ a := hl n hn
        _ ≤ (MixedMellinCert.tauAF (2 * K) n : ℝ) *
            ((2 : ℝ) ^ a * Real.log (2 + (n : ℝ)) ^ a) :=
          mul_le_mul_of_nonneg_left (log_two_mul_pow_le a n hnpos) (by positivity)
        _ = _ := by ring
    · rw [hsupp.2 n hn, norm_zero]
      exact hnonneg (2 * K) n

/-- A common pointwise coefficient bound on the literal product scale. The
ordered-divisor subpower constant is fixed before `X`, every mask and packet,
and `n`; this is not an L¹ bound for a coefficient envelope. -/
theorem exists_fixedOrder_highPacket_convolution_bound
    (K : ℕ) (hK : 1 ≤ K) (theta : ℝ) (htheta : 0 < theta) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
      (packet : DynamicHighPacketIndexV3 (H₀ := H₀) hX hdelta K) (n : ℕ),
      ‖literalDirichletConvolution (highPacketLongCoeffV3 packet)
          (highPacketShortCoeffV3 packet) n‖ ≤
        C * Real.rpow
          (4 * (highPacketLongLengthV3 packet : ℝ) * (highPacketShortLengthV3 packet : ℝ)) theta := by
  obtain ⟨a, hcoeff⟩ := exists_fixedOrder_highPacket_divisorLogMajorized K hK
  obtain ⟨C₀, hC₀, hmajor⟩ := orderedDivisorCount_mul_log_pow_subpolynomial
    (2 * K + 1) (a + a) (by omega) theta htheta
  let D : ℝ := (2 : ℝ) ^ a * (2 : ℝ) ^ a
  refine ⟨D * C₀, mul_pos (by dsimp [D]; positivity) hC₀, ?_⟩
  intro X delta H₀ hX hdelta packet n
  obtain ⟨hs, hl⟩ := hcoeff packet
  have hsupp := highPacket_supportV3 packet
  have hgeom := highPacket_geometryV3 packet
  let N : ℝ := highPacketLongLengthV3 packet
  let M : ℝ := highPacketShortLengthV3 packet
  have hN : 0 < N := by dsimp [N]; exact_mod_cast (by omega : 0 < highPacketLongLengthV3 packet)
  have hM : 0 < M := by dsimp [M]; exact_mod_cast (by omega : 0 < highPacketShortLengthV3 packet)
  have hsReal := supportedDyadic_of_supportedNatDyadic hsupp.1
  have hlReal := supportedDyadic_of_supportedNatDyadic hsupp.2
  change _ ≤ (D * C₀) * Real.rpow (4 * N * M) theta
  by_cases hblock : N * M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 4 * N * M
  · have hnR : (0 : ℝ) < n := (mul_pos hN hM).trans_le hblock.1
    have hn : 0 < n := by exact_mod_cast hnR
    have hc := literalDirichletConvolution_norm_le_divisorLog
      (by positivity : 0 ≤ (2 : ℝ) ^ a) (by positivity : 0 ≤ (2 : ℝ) ^ a) hl hs n
    have hm := mul_le_mul_of_nonneg_left (hmajor n hn) (by dsimp [D]; positivity : 0 ≤ D)
    have hp := Real.rpow_le_rpow hnR.le hblock.2 htheta.le
    calc
      _ ≤ D * ((orderedDivisorCount (2 * K + 1) n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (a + a)) := by simpa [D, mul_assoc] using hc
      _ ≤ D * (C₀ * Real.rpow n theta) := hm
      _ = (D * C₀) * Real.rpow n theta := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by dsimp [D]; positivity)
  · rw [literalDirichletConvolution_eq_zero_off_productBlock hN.le hM.le hlReal hsReal hblock]
    simpa using mul_nonneg (mul_nonneg (by dsimp [D]; positivity) hC₀.le)
      (Real.rpow_nonneg (by positivity : 0 ≤ 4 * N * M) theta)

end
end MRTLemma215DynamicHighPointwiseV3
#print axioms MRTLemma215DynamicHighPointwiseV3.exists_fixedOrder_highPacket_divisorLogMajorized
#print axioms MRTLemma215DynamicHighPointwiseV3.exists_fixedOrder_highPacket_convolution_bound
