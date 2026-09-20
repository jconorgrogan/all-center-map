import MRTLemma215DynamicHighUniformUnscaledV3
import MAPDynamicHBScaledPacketMixedMeanV3
import MAPDynamicHBScaledPacketSourceRefinedV3

/-! # Uniform mixed mean with the exact Cauchy and Perron scales retained -/

namespace MRTProposition61HighUniformScaledMixedV3

open scoped BigOperators
open MAPFarAnnulusMRT MAPFarAnnulusSourceToModel MixedMeanFrontend MixedMeanMajorantWeld
open MAPMRTCorollary25Instantiation MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPDynamicHBSourceV3 MAPDynamicHBScaledPacketSourceV3 MAPDynamicHBScaledPacketSourceRefinedV3
open MAPDynamicHBSourcePacketBoundRefinedV3 MAPDynamicHBScaledPacketMixedMeanV3
open MRTLemma215DynamicHighPacketIndexV3 MRTLemma215DynamicHighUniformUnscaledV3

noncomputable section
set_option maxHeartbeats 1400000

theorem paperMixedMass_re_scale_long
    (M N : ℕ) (beta long : ℕ → ℂ) (c t₀ T U : ℝ) :
    (paperLiteralMixedMean M N beta (fun n => (c : ℂ) * long n) t₀ T U).re =
      c ^ 2 * (paperLiteralMixedMean M N beta long t₀ T U).re := by
  have hpoly (t : ℝ) : longFactor N (invSqrtCoeff (fun n => (c : ℂ) * long n)) t =
      (c : ℂ) * longFactor N (invSqrtCoeff long) t := by
    unfold longFactor dirichletPoly invSqrtCoeff
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  simp only [paperLiteralMixedMean, literalMixedMean_eq_ofReal, Complex.ofReal_re]
  unfold literalMixedMeanReal
  simp_rw [hpoly, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  ring

theorem characterPairMixedMass_scale_long
    {q : ℕ} (M N : ℕ) (beta long : Fin q → ℕ → ℂ) (c t₀ T U : ℝ) :
    characterPairMixedMass q M N (pairShortFamily beta) (pairLongFamily (scaleCoeffFamily c long)) t₀ T U =
      c ^ 2 * characterPairMixedMass q M N (pairShortFamily beta) (pairLongFamily long) t₀ T U := by
  unfold characterPairMixedMass pairShortFamily pairLongFamily scaleCoeffFamily
  simp_rw [paperMixedMass_re_scale_long, ← Finset.mul_sum]
  ring

/-- Exact homogeneity: the refined source weight is kept outside the mixed
mean, so it cannot make the chosen coefficient exponent depend on `X`. -/
theorem refinedPacketMixedMass_eq_weight_mul
    {q : ℕ} [NeZero q] {X delta H₀ : ℝ} {hX : 2 ≤ X} {hdelta : 0 < delta}
    (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
    (c t₀ T U : ℝ) :
    characterPairMixedMass q (highPacketShortLengthV3 (allPacketGlobalV3 packet))
      (highPacketLongLengthV3 (allPacketGlobalV3 packet))
      (pairShortFamily (paddedCharacterTwist q q le_rfl (allPacketShortCoeffV3 packet)))
      (pairLongFamily (scaleCoeffFamily c
        (paddedCharacterTwist q q le_rfl (scaledAllPacketLongCoeffRefinedV3 packet)))) t₀ T U =
      c ^ 2 * dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
      characterPairMixedMass q (highPacketShortLengthV3 (allPacketGlobalV3 packet))
        (highPacketLongLengthV3 (allPacketGlobalV3 packet))
        (pairShortFamily (paddedCharacterTwist q q le_rfl (allPacketShortCoeffV3 packet)))
        (pairLongFamily (paddedCharacterTwist q q le_rfl (highPacketLongCoeffV3 (allPacketGlobalV3 packet))))
        t₀ T U := by
  unfold scaledAllPacketLongCoeffRefinedV3
  rw [scaleCoeffFamily_padded_scaleNatCoefficient]
  rw [characterPairMixedMass_scale_long, mul_pow, dynamicPacketScaleRefinedV3_sq]

/-- One constant and coefficient exponent controls all actual refined high
packets, all moduli, all centers and all free Perron scales. -/
theorem exists_uniform_refinedPacketMixedMass_bound
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ a : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {X H₀ : ℝ} {hX : 2 ≤ X} (q : ℕ) [NeZero q]
        (packet : DynamicAllHighPacketIndexV3 (H₀ := H₀) hX hdelta)
        (c t₀ T U : ℝ), 1 ≤ T → 1 ≤ U →
        characterPairMixedMass q (highPacketShortLengthV3 (allPacketGlobalV3 packet))
          (highPacketLongLengthV3 (allPacketGlobalV3 packet))
          (pairShortFamily (paddedCharacterTwist q q le_rfl (allPacketShortCoeffV3 packet)))
          (pairLongFamily (scaleCoeffFamily c
            (paddedCharacterTwist q q le_rfl (scaledAllPacketLongCoeffRefinedV3 packet)))) t₀ T U ≤
          c ^ 2 * dynamicBranchHighWeightRefinedV3 (H₀ := H₀) hX hdelta packet.1 *
            (U * (q : ℝ) ^ 2 * C *
              Real.log (2 * (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
                (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ)) ^
                (4 * a + 2 * max 2 ((2 * hbOrder delta) * (2 * hbOrder delta)) + 2) *
              (U * T + U * (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) +
                (highPacketShortLengthV3 (allPacketGlobalV3 packet) : ℝ) *
                  (highPacketLongLengthV3 (allPacketGlobalV3 packet) : ℝ) + T)) := by
  obtain ⟨a, C, hC, hmean⟩ := exists_fixedOrder_highPacket_mixedMass_bound
    (hbOrder delta) (hbOrder_one hdelta)
  refine ⟨a, C, hC, ?_⟩
  intro X H₀ hX q _ packet c t₀ T U hT hU
  rw [refinedPacketMixedMass_eq_weight_mul]
  apply mul_le_mul_of_nonneg_left
    (hmean q (allPacketGlobalV3 packet) t₀ T U hT hU)
  exact mul_nonneg (sq_nonneg _) (dynamicBranchHighWeightRefinedV3_nonneg hX hdelta packet.1)

end
end MRTProposition61HighUniformScaledMixedV3

#print axioms MRTProposition61HighUniformScaledMixedV3.exists_uniform_refinedPacketMixedMass_bound
