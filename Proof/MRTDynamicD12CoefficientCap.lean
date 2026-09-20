import MRTDynamicD12AnnulusMomentAssembly
import MRTDynamicD12CoefficientBound
import MRTLemma215DynamicTypeIIGlobalCountV3
import MRTCorollary25TypeD1CoefficientBound

namespace MRTDynamicD12CoefficientCap

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPDynamicHBSourceV3 MAPHBPerronSourceData
open MAPMRTCorollary25TypeD1CoefficientBound
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicTypeIIGlobalCountV3
open MRTLemma215DynamicTypeIIFiniteEnvelopeV3
open MRTLemma215DynamicSupportV3 MRTDynamicD12PolynomialFactorization
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicHighPacketCertificateV3 MRTLemma215DynamicSupportV3
open MRTDynamicD12CoefficientBound MRTDynamicD12CarrierIdentities
open FixedCharacterPoweredBridge
open MixedMellinCert

noncomputable section
set_option maxHeartbeats 1400000

/-- Fixed epsilon cap for the actual unmasked component.  The support scale
is allowed to reach `X^(6K)`; this never assumes `n ≤ X`. -/
theorem exists_d12_component_coefficient_cap
    (K : ℕ) (hK : 1 ≤ K) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ D : ℝ, 0 < D ∧
      ∀ {X delta H₀ : ℝ} {k : ℕ}, 3 ≤ X → 0 ≤ delta → k < K →
        ∀ (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
          (zbag : Sym (Option (Fin (sourceDyadicCount
            (hbFactorCutoff X)))) k)
          (mbag : Sym (Option (Fin
            (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) (n : ℕ),
        ‖dynamicPreliminaryComponent (some logIndex) zbag mbag n‖ ≤
          D * Real.rpow X epsilon := by
  obtain ⟨S, hS, hcoeff⟩ := exists_fixedOrder_fullComponent_coefficient_bound K hK
  have htheta : 0 < epsilon / (6 * K : ℝ) := by
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    positivity
  obtain ⟨C₀, hC₀, hmajor⟩ :=
    orderedDivisorCount_mul_log_pow_subpolynomial (2 * K) (8 * K)
      (by omega) (epsilon / (6 * K : ℝ)) htheta
  let L : ℝ := (2 : ℝ) ^ (4 * K)
  refine ⟨S * (L * C₀), mul_pos hS (mul_pos (by dsimp [L]; positivity) hC₀), ?_⟩
  intro X delta H₀ k hX hdelta hk logIndex zbag mbag n
  have hX1 : 1 ≤ X := by linarith
  have hpre := dynamicPreliminaryComponent_eq_smul_sorted hX1 hK
    logIndex zbag mbag
  let factors := sortedComponentFactorList logIndex zbag mbag
  have hfacLen : ∀ f ∈ factors, (f.length : ℝ) ≤ 2 * X := by
    intro f hf
    exact sortedComponentFactor_length_le_two_mul hX hK logIndex zbag mbag hf
  have hupper := factorUpperProduct_le_cube_pow hX factors hfacLen
  have hlen : factors.length ≤ 2 * K := by
    dsimp [factors]
    have hh := sortedComponentFactorList_length_le logIndex zbag mbag
    omega
  have hpow : (X ^ 3) ^ factors.length ≤ X ^ (6 * K) := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by linarith) (by omega)
  have hsupport : (factorUpperProduct factors : ℝ) ≤ X ^ (6 * K) := by
    exact hupper.trans hpow
  have hpoweq : Real.rpow (X ^ (6 * K)) (epsilon / (6 * K : ℝ)) =
      Real.rpow X epsilon := by
    calc
      Real.rpow (X ^ (6 * K)) (epsilon / (6 * K : ℝ)) =
          Real.rpow (Real.rpow X (6 * K : ℝ))
            (epsilon / (6 * K : ℝ)) := by
        rw [← Real.rpow_natCast X (6 * K)]
        congr 1
        norm_num
      _ = Real.rpow X ((6 * K : ℝ) * (epsilon / (6 * K : ℝ))) := by
        exact (Real.rpow_mul (by positivity : 0 ≤ X) _ _).symm
      _ = Real.rpow X epsilon := by congr 1; field_simp
  rw [hpre]
  change ‖dynamicComponentScalarValue zbag mbag * factorConvolution factors n‖ ≤ _
  by_cases hn0 : n = 0
  · subst n
    have hz : factorConvolution factors 0 = 0 := (factorConvolution factors).map_zero'
    rw [hz, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hS.le (mul_nonneg (by dsimp [L]; positivity) hC₀.le))
      (Real.rpow_nonneg (by linarith) _)
  have hnpos : 0 < n := by omega
  by_cases hnupper : factorUpperProduct factors < n
  · rw [factorConvolution_zero_above_upper factors hnupper, mul_zero, norm_zero]
    exact mul_nonneg (mul_nonneg hS.le (mul_nonneg (by dsimp [L]; positivity) hC₀.le))
      (Real.rpow_nonneg (by linarith) _)
  have hnle : n ≤ factorUpperProduct factors := by omega
  have hnR : (n : ℝ) ≤ (factorUpperProduct factors : ℝ) := by exact_mod_cast hnle
  have hnX : (n : ℝ) ≤ X ^ (6 * K) := hnR.trans hsupport
  have hraw := hcoeff hk logIndex zbag mbag n
  have hmaj := hmajor n hnpos
  rw [orderedDivisorCount_eq_tauAF] at hmaj
  have hlog : Real.log (2 * (n : ℝ)) ≤ 2 * Real.log (2 + (n : ℝ)) := by
    calc
      Real.log (2 * (n : ℝ)) ≤ Real.log ((2 + (n : ℝ)) ^ 2) :=
        Real.log_le_log (by positivity) (by
          nlinarith [sq_nonneg ((n : ℝ) - 2)])
      _ = 2 * Real.log (2 + (n : ℝ)) := by
        rw [Real.log_pow]
        norm_num
  have hlog_nonneg : 0 ≤ Real.log (2 + (n : ℝ)) :=
    Real.log_nonneg (by linarith)
  have hlog_one : 1 ≤ Real.log (2 + (n : ℝ)) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 + (n : ℝ)) := Real.log_le_log
        (Real.exp_pos 1)
        (by
          have hn1 : (1 : ℝ) ≤ n := by
            exact_mod_cast (show (1 : ℕ) ≤ n by omega)
          linarith [Real.exp_one_lt_three])
  have hpowlog : Real.log (2 * (n : ℝ)) ^ (4 * K) ≤
      L * Real.log (2 + (n : ℝ)) ^ (8 * K) := by
    have hn1R : (1 : ℝ) ≤ n := by
      exact_mod_cast (show (1 : ℕ) ≤ n by omega)
    calc
      Real.log (2 * (n : ℝ)) ^ (4 * K) ≤
          (2 * Real.log (2 + (n : ℝ))) ^ (4 * K) :=
        pow_le_pow_left₀ (Real.log_nonneg (by linarith [hn1R])) hlog _
      _ = L * Real.log (2 + (n : ℝ)) ^ (4 * K) := by
        dsimp [L]
        rw [mul_pow]
      _ ≤ L * Real.log (2 + (n : ℝ)) ^ (8 * K) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hlog_one (by omega)) (by positivity)
  have hsub : ‖dynamicComponentScalarValue zbag mbag * factorConvolution factors n‖ ≤
      (S * (L * C₀)) * Real.rpow n (epsilon / (6 * K : ℝ)) := by
    calc
      _ = ‖(dynamicComponentScalarValue zbag mbag • factorConvolution factors) n‖ := by
        rfl
      _ ≤ S * ((tauAF (2 * K) n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (4 * K)) := by
        simpa [mul_assoc] using hraw
      _ ≤ S * (L * ((tauAF (2 * K) n : ℝ) *
          Real.log (2 + (n : ℝ)) ^ (8 * K))) := by
        exact mul_le_mul_of_nonneg_left
          (calc
            (tauAF (2 * K) n : ℝ) * Real.log (2 * (n : ℝ)) ^ (4 * K) ≤
                (tauAF (2 * K) n : ℝ) *
                  (L * Real.log (2 + (n : ℝ)) ^ (8 * K)) :=
              mul_le_mul_of_nonneg_left hpowlog (by positivity)
            _ = L * ((tauAF (2 * K) n : ℝ) *
                Real.log (2 + (n : ℝ)) ^ (8 * K)) := by ring)
          hS.le
      _ ≤ S * (L * (C₀ * Real.rpow n (epsilon / (6 * K : ℝ)))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmaj (by positivity)) hS.le
      _ ≤ (S * (L * C₀)) * Real.rpow n (epsilon / (6 * K : ℝ)) := by
        convert le_rfl using 1 <;> ring
  exact hsub.trans <| by
    calc
      (S * (L * C₀)) * Real.rpow n (epsilon / (6 * K : ℝ)) ≤
          (S * (L * C₀)) * Real.rpow (X ^ (6 * K)) (epsilon / (6 * K : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by exact_mod_cast hnpos.le) hnX htheta.le)
          (mul_nonneg hS.le (mul_nonneg (by dsimp [L]; positivity) hC₀.le))
      _ = (S * (L * C₀)) * Real.rpow X epsilon := by rw [hpoweq]

end
end MRTDynamicD12CoefficientCap

#print axioms MRTDynamicD12CoefficientCap.exists_d12_component_coefficient_cap
