import MRTProposition61TypeIIUniformEnergyV3
import MontgomeryMollifierSecondMoment

namespace MRTDynamicD12ShortPrefix
open scoped BigOperators ArithmeticFunction
open MeasureTheory ArithmeticFunction MixedMellinCert
open MRTLemma215HBExpansion MAPHBPerronSourceData MAPDynamicHBSourceV3 MRTLemma215DyadicPartition
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicCoefficientBoundsV3 MRTLemma215DynamicMultiplicityBoundsV3
open MRTProposition61TypeIILemma210InstantiationV3
open MAPMRTLemma210SameResidueHilbert MAPMRTLemma210OrthogonalityReduction
open MontgomeryVaughanFiniteReduction RamachandraShiftedCoefficientEnergy
noncomputable section

def shortPrefixCoefficient {X : ℝ} {K k : ℕ}
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1))
    (sub : List NatDyadicFactor) : ArithmeticFunction ℂ :=
  dynamicComponentScalar zbag mbag * factorConvolution sub

def shortPrefixPolynomial (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℂ :=
  twistedFinitePolynomial q (Finset.Icc 1 N) (criticalDyadicCoefficient f) chi t

def shortPrefixNormField (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ‖shortPrefixPolynomial q N f chi t‖

theorem continuous_shortPrefixNormField (q N : ℕ) (f : ℕ → ℂ)
    (chi : DirichletCharacter ℂ q) : Continuous (shortPrefixNormField q N f chi) := by
  unfold shortPrefixNormField shortPrefixPolynomial twistedFinitePolynomial twistedPhase
  fun_prop

theorem shortPrefix_energy {X : ℝ} {K k N : ℕ} (hN : 1 ≤ N)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag) :
    residuePacketEnergy (Finset.Icc 1 N)
      (criticalDyadicCoefficient (shortPrefixCoefficient zbag mbag sub)) ≤
    (((K^(k+1)*Nat.factorial k*Nat.factorial (k+1) : ℕ) : ℝ))^2 *
      (1 + Real.log (2*(N:ℝ)))^(4*sub.length+sub.length*sub.length) := by
  let L : ℝ := 1 + Real.log (2*(N:ℝ))
  let S : ℝ := ((K^(k+1)*Nat.factorial k*Nat.factorial (k+1) : ℕ) : ℝ)
  have hlog : 0 ≤ Real.log (2*(N:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*N by omega))
  have hL : 0 ≤ L := by dsimp [L]; linarith
  have hcoeff (n : ℕ) (hn : n ∈ Finset.Icc 1 N) :
      ‖shortPrefixCoefficient zbag mbag sub n‖ ≤ S * (tauAF sub.length n : ℝ) * L^(2*sub.length) := by
    have hn' := Finset.mem_Icc.mp hn
    have hb := factorConvolution_norm_le_tauAF_const sub (by omega : n ≠ 0)
      (sq_nonneg L) (fun f hf d hd => by
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
        have hdle : d ≤ N := (Nat.le_of_dvd (by omega) hd).trans hn'.2
        have hh := sortedDynamicComponentFactor_coeff_le_logSq logIndex zbag mbag (hsub f hf) d
        have hlo : 0 ≤ Real.log (2*(d:ℝ)) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2*d by omega))
        have hhi : Real.log (2*(d:ℝ)) ≤ L := by
          have hh := Real.log_le_log (by positivity : 0 < 2*(d:ℝ)) (show 2*(d:ℝ) ≤ 2*(N:ℝ) by exact_mod_cast Nat.mul_le_mul_left 2 hdle)
          dsimp [L]; linarith
        exact hh.trans (pow_le_pow_left₀ hlo hhi 2)) (dvd_refl n)
    unfold shortPrefixCoefficient
    rw [dynamicComponentScalar_mul_eq_smul]
    change ‖dynamicComponentScalarValue zbag mbag * factorConvolution sub n‖ ≤ _
    rw [norm_mul]
    have hs := norm_dynamicComponentScalarValue_le zbag mbag
    calc
      _ ≤ S * ((tauAF sub.length n : ℝ) * (L^2)^sub.length) :=
        mul_le_mul (by simpa [S] using hs) hb (norm_nonneg _) (by dsimp [S]; positivity)
      _ = _ := by rw [← pow_mul]; ring
  unfold residuePacketEnergy
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, S^2 * L^(4*sub.length) * ((tauAF (sub.length*sub.length) n : ℝ)/(n:ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      rw [norm_criticalDyadicCoefficient_sq _ (by omega)]
      have hc := pow_le_pow_left₀ (norm_nonneg _) (hcoeff n hn) 2
      have ht : (tauAF sub.length n : ℝ)^2 ≤ tauAF (sub.length*sub.length) n := by
        exact_mod_cast ShiuAnalyticLayer.tauAF_square_le_tauAF_mul sub.length n
      calc
        _ ≤ (S * (tauAF sub.length n : ℝ) * L^(2*sub.length))^2 / (n:ℝ) := div_le_div_of_nonneg_right hc (by positivity)
        _ = S^2 * L^(4*sub.length) * ((tauAF sub.length n : ℝ)^2/(n:ℝ)) := by
          rw [show 4*sub.length = (2*sub.length)*2 by omega, pow_mul]; ring
        _ ≤ _ := by gcongr
    _ = S^2 * L^(4*sub.length) * ∑ n ∈ Finset.Ioc 0 N, ((tauAF (sub.length*sub.length) n : ℝ)/(n:ℝ)) := by
      rw [Finset.mul_sum]
      congr 1
    _ ≤ S^2 * L^(4*sub.length) * (harmonic N : ℝ)^(sub.length*sub.length) :=
      mul_le_mul_of_nonneg_left (sum_tauAF_div_cast_le_harmonic_pow _ _) (by positivity)
    _ ≤ S^2 * L^(4*sub.length) * L^(sub.length*sub.length) := by
      have hh : (harmonic N : ℝ) ≤ L := by
        have hb := harmonic_le_one_add_log N
        have hm := Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) (show (N:ℝ) ≤ 2*(N:ℝ) by have : (0:ℝ) ≤ N := Nat.cast_nonneg N; linarith)
        dsimp [L]; linarith
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by exact_mod_cast (harmonic_pos (by omega : N ≠ 0)).le) hh _) (by positivity)
    _ = _ := by dsimp [S, L]; rw [pow_add]; ring

 theorem shortPrefix_localMeanSquare {X U : ℝ} {K k N q : ℕ} [NeZero q]
    (hN : 1 ≤ N) (hU : 0 ≤ U) (t : ℝ)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k+1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub, f ∈ sortedComponentFactorList logIndex zbag mbag) :
    (∫ v in (t-U)..(t+U), ∑ chi : DirichletCharacter ℂ q,
      (shortPrefixNormField q N (shortPrefixCoefficient zbag mbag sub) chi v)^2) ≤
    ((q:ℝ)*(2*U)+8*Real.pi*(N:ℝ)) *
    (((K^(k+1)*Nat.factorial k*Nat.factorial (k+1) : ℕ) : ℝ))^2 *
      (1 + Real.log (2*(N:ℝ)))^(4*sub.length+sub.length*sub.length) := by
  have hm := MAPMontgomeryMollifierSecondMoment.prefix_twisted_character_mean_square_interval_le
    (q := q) hN (criticalDyadicCoefficient (shortPrefixCoefficient zbag mbag sub)) (t-U) (T := 2*U) (by positivity)
  rw [show t-U+2*U=t+U by ring] at hm
  exact hm.trans (by
    have he := shortPrefix_energy hN logIndex zbag mbag sub hsub
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left he (show 0 ≤ (q:ℝ)*(2*U)+8*Real.pi*(N:ℝ) by positivity))
end
end MRTDynamicD12ShortPrefix
#print axioms MRTDynamicD12ShortPrefix.shortPrefix_localMeanSquare
