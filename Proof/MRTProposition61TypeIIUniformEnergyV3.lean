import MRTProposition61TypeIILemma210InstantiationV3
import MRTLemma215DynamicMultiplicityBoundsV3

/-! # Explicit constant-bearing energy bound for Type-II cells -/

namespace MRTProposition61TypeIIUniformEnergyV3

open scoped BigOperators
open RamachandraShiftedCoefficientEnergy
open MRTProposition61TypeIILemma210InstantiationV3
open MontgomeryVaughanFiniteReduction
open MixedMellinCert
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicTypeIIDyadicV3
open MRTLemma215DynamicTypeIICoefficientBoundsV3
open MRTLemma215DynamicMultiplicityBoundsV3

noncomputable section

/-- The coefficient-energy log-power estimate with a multiplicative
coefficient constant retained explicitly. -/
theorem coefficientEnergy_critical_le_logPow_const
    {N r a : ℕ} {A : ℝ} (hN : 1 ≤ N) (hA : 0 ≤ A)
    (f : ℕ → ℂ)
    (hf : ∀ n ∈ dyadicSupport N,
      ‖f n‖ ≤ A * (tauAF r n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ a) :
    coefficientEnergy (criticalDyadicCoefficient f) N ≤
      A ^ 2 * (1 + Real.log (4 * (N : ℝ))) ^
        (2 * a + r * r) := by
  let L : ℝ := 1 + Real.log (4 * (N : ℝ))
  have hlog4 : 0 ≤ Real.log (4 * (N : ℝ)) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ 4 * N by omega)
  have hL : 0 ≤ L := by dsimp [L]; linarith
  unfold coefficientEnergy
  calc
    (∑ n ∈ dyadicSupport N, ‖criticalDyadicCoefficient f n‖ ^ 2) ≤
        ∑ n ∈ dyadicSupport N,
          A ^ 2 * L ^ (2 * a) *
            ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Ioc.mp hn
      have hnpos : 0 < n := Nat.zero_lt_of_lt hnBounds.1
      rw [norm_criticalDyadicCoefficient_sq f hnpos]
      have hlogNonneg : 0 ≤ Real.log (2 * (n : ℝ)) := by
        apply Real.log_nonneg
        exact_mod_cast (show 1 ≤ 2 * n by omega)
      have hlogLe : Real.log (2 * (n : ℝ)) ≤ L := by
        dsimp [L]
        have hmono : Real.log (2 * (n : ℝ)) ≤
            Real.log (4 * (N : ℝ)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast (show 2 * n ≤ 4 * N by omega)
        linarith
      have hraw := hf n hn
      have hcoeff : ‖f n‖ ≤ A * (tauAF r n : ℝ) * L ^ a :=
        hraw.trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ hlogNonneg hlogLe a)
          (mul_nonneg hA (by positivity)))
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
      have htau : (tauAF r n : ℝ) ^ 2 ≤ tauAF (r * r) n := by
        exact_mod_cast ShiuAnalyticLayer.tauAF_square_le_tauAF_mul r n
      calc
        ‖f n‖ ^ 2 / (n : ℝ) ≤
            (A * (tauAF r n : ℝ) * L ^ a) ^ 2 / (n : ℝ) :=
          div_le_div_of_nonneg_right hsq (by positivity)
        _ = A ^ 2 * L ^ (2 * a) *
            ((tauAF r n : ℝ) ^ 2 / (n : ℝ)) := by
          rw [show 2 * a = a * 2 by omega, pow_mul]
          ring
        _ ≤ A ^ 2 * L ^ (2 * a) *
            ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by gcongr
    _ ≤ ∑ n ∈ Finset.Ioc 0 (2 * N),
          A ^ 2 * L ^ (2 * a) *
            ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (dyadicSupport_subset_Ioc_zero_two_mul N)
      intro n hn hnot
      positivity
    _ = A ^ 2 * L ^ (2 * a) *
        ∑ n ∈ Finset.Ioc 0 (2 * N),
          ((tauAF (r * r) n : ℝ) / (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ A ^ 2 * L ^ (2 * a) *
        (harmonic (2 * N) : ℝ) ^ (r * r) := by
      exact mul_le_mul_of_nonneg_left
        (sum_tauAF_div_cast_le_harmonic_pow (r * r) (2 * N))
        (mul_nonneg (sq_nonneg _) (pow_nonneg hL _))
    _ ≤ A ^ 2 * L ^ (2 * a) * L ^ (r * r) := by
      have hharm : (harmonic (2 * N) : ℝ) ≤ L := by
        have hbase := harmonic_le_one_add_log (2 * N)
        have hmono : Real.log (2 * (N : ℝ)) ≤
            Real.log (4 * (N : ℝ)) := by
          apply Real.log_le_log (by positivity)
          exact_mod_cast (show 2 * N ≤ 4 * N by omega)
        have hbase' : (harmonic (2 * N) : ℝ) ≤
            1 + Real.log (2 * (N : ℝ)) := by
          simpa [Nat.cast_mul] using hbase
        exact hbase'.trans (by dsimp [L]; linarith)
      have hharm0 : 0 ≤ (harmonic (2 * N) : ℝ) := by
        exact_mod_cast (harmonic_pos (by omega : 2 * N ≠ 0)).le
      gcongr
    _ = A ^ 2 * L ^ (2 * a + r * r) := by rw [pow_add]; ring
    _ = _ := by rfl

/-- Explicit, cell-uniform exponent and HB scalar constant for the short
Type-II coefficient energy. -/
theorem scaledTypeIIPrefixCell_energy_le_logPow_const
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    let S : ℝ :=
      ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ)
    coefficientEnergy
        (criticalDyadicCoefficient
          (scaledTypeIIPrefixCell zbag mbag sub cell))
        (2 ^ (cell : ℕ)) ≤
      S ^ 2 *
        (1 + Real.log (4 * ((2 ^ (cell : ℕ) : ℕ) : ℝ))) ^
          (4 * sub.length + sub.length * sub.length) := by
  dsimp only
  let N : ℕ := 2 ^ (cell : ℕ)
  let S : ℝ :=
    ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ)
  have hN : 1 ≤ N := by
    dsimp [N]
    exact Nat.one_le_pow (cell : ℕ) 2 (by omega)
  have hs := norm_dynamicComponentScalarValue_le zbag mbag
  have hfbound : ∀ n ∈ dyadicSupport N,
      ‖scaledTypeIIPrefixCell zbag mbag sub cell n‖ ≤
        S * (tauAF sub.length n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := by
    intro n hn
    have hn2 : 2 ≤ n := by
      have := (Finset.mem_Ioc.mp hn).1
      omega
    unfold scaledTypeIIPrefixCell
    rw [dynamicComponentScalar_mul_eq_smul]
    change ‖dynamicComponentScalarValue zbag mbag *
        factorListDyadicCell sub cell n‖ ≤ _
    rw [norm_mul]
    have hf := factorListDyadicCell_norm_le
      logIndex zbag mbag sub hsub cell hn2
    calc
      ‖dynamicComponentScalarValue zbag mbag‖ *
          ‖factorListDyadicCell sub cell n‖ ≤
        S * ‖factorListDyadicCell sub cell n‖ :=
          mul_le_mul_of_nonneg_right (by simpa [S] using hs) (norm_nonneg _)
      _ ≤ S * ((tauAF sub.length n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (2 * sub.length)) :=
        mul_le_mul_of_nonneg_left hf (by dsimp [S]; positivity)
      _ = S * (tauAF sub.length n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := by ring
  have henergy := coefficientEnergy_critical_le_logPow_const
    (N := N) (r := sub.length) (a := 2 * sub.length)
    hN (by dsimp [S]; positivity)
    (scaledTypeIIPrefixCell zbag mbag sub cell) hfbound
  simpa [N, S, show 2 * (2 * sub.length) = 4 * sub.length by omega]
    using henergy

/-- Both actual cell energies admit one fixed-order log-power envelope.
The scale hypotheses are supplied by the nonzero-cell product bound. -/
theorem typeIICell_energy_product_le_fixedOrder_logPow
    {X : ℝ} {K k : ℕ} (hX : 1 ≤ X) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (left suffix : List NatDyadicFactor)
    (hleft : ∀ f ∈ left, f ∈ sortedComponentFactorList logIndex zbag mbag)
    (hsuffix : ∀ f ∈ suffix, f ∈ sortedComponentFactorList logIndex zbag mbag)
    (hlen : left.length + suffix.length ≤ 2 * K)
    (leftCell : Fin (sourceDyadicCount (factorUpperProduct left)))
    (suffixCell : Fin (sourceDyadicCount (factorUpperProduct suffix)))
    (hN : ((2 ^ (leftCell : ℕ) : ℕ) : ℝ) ≤ 2 * X)
    (hM : ((2 ^ (suffixCell : ℕ) : ℕ) : ℝ) ≤ 2 * X) :
    coefficientEnergy (criticalDyadicCoefficient
        (scaledTypeIIPrefixCell zbag mbag left leftCell)) (2 ^ (leftCell : ℕ)) *
      coefficientEnergy (criticalDyadicCoefficient
        (factorListDyadicCell suffix suffixCell)) (2 ^ (suffixCell : ℕ)) ≤
      (((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)) ^ 2 *
        (1 + Real.log (8 * X)) ^ (8 * K + 4 * K * K) := by
  let L := 1 + Real.log (8 * X)
  let S : ℝ := ((K ^ (k + 1) * Nat.factorial k * Nat.factorial (k + 1) : ℕ) : ℝ)
  let Smax : ℝ := ((K ^ K * Nat.factorial K * Nat.factorial K : ℕ) : ℝ)
  have hL : 1 ≤ L := by
    dsimp [L]
    have := Real.log_nonneg (by linarith : 1 ≤ 8 * X)
    linarith
  have hs : S ≤ Smax := by
    have hp := pow_le_pow_right₀ (show 1 ≤ K by omega) (show k + 1 ≤ K by omega)
    have hf0 := Nat.factorial_le (show k ≤ K by omega)
    have hf1 := Nat.factorial_le (show k + 1 ≤ K by omega)
    dsimp [S, Smax]
    exact_mod_cast Nat.mul_le_mul (Nat.mul_le_mul hp hf0) hf1
  have hlog (n : ℕ) (hn : 1 ≤ n) (hnX : (n : ℝ) ≤ 2 * X) :
      0 ≤ 1 + Real.log (4 * (n : ℝ)) ∧
        1 + Real.log (4 * (n : ℝ)) ≤ L := by
    constructor
    · have := Real.log_nonneg (show 1 ≤ 4 * (n : ℝ) by exact_mod_cast (show 1 ≤ 4 * n by omega))
      linarith
    · have := Real.log_le_log (show 0 < 4 * (n : ℝ) by positivity)
        (show 4 * (n : ℝ) ≤ 8 * X by linarith)
      dsimp [L]
      linarith
  have hl := hlog (2 ^ (leftCell : ℕ)) (Nat.one_le_pow _ _ (by omega)) hN
  have hm := hlog (2 ^ (suffixCell : ℕ)) (Nat.one_le_pow _ _ (by omega)) hM
  have heleft := scaledTypeIIPrefixCell_energy_le_logPow_const
    logIndex zbag mbag left hleft leftCell
  have heright := factorListDyadicCell_energy_le_logPow
    logIndex zbag mbag suffix hsuffix suffixCell
  dsimp only at heleft
  have hel : coefficientEnergy (criticalDyadicCoefficient
      (scaledTypeIIPrefixCell zbag mbag left leftCell)) (2 ^ (leftCell : ℕ)) ≤
      Smax ^ 2 * L ^ (4 * left.length + left.length * left.length) := by
    exact heleft.trans (mul_le_mul
      (pow_le_pow_left₀ (by dsimp [S]; positivity) hs 2)
      (pow_le_pow_left₀ hl.1 hl.2 _) (pow_nonneg hl.1 _) (sq_nonneg _))
  have her : coefficientEnergy (criticalDyadicCoefficient
      (factorListDyadicCell suffix suffixCell)) (2 ^ (suffixCell : ℕ)) ≤
      L ^ (4 * suffix.length + suffix.length * suffix.length) :=
    heright.trans (pow_le_pow_left₀ hm.1 hm.2 _)
  have hexp : 4 * left.length + left.length * left.length +
      (4 * suffix.length + suffix.length * suffix.length) ≤ 8 * K + 4 * K * K := by
    nlinarith [Nat.mul_self_le_mul_self hlen]
  calc
    _ ≤ (Smax ^ 2 * L ^ (4 * left.length + left.length * left.length)) *
        L ^ (4 * suffix.length + suffix.length * suffix.length) := by
      apply mul_le_mul hel her
      · unfold coefficientEnergy
        positivity
      · positivity
    _ = Smax ^ 2 * L ^ (4 * left.length + left.length * left.length +
        (4 * suffix.length + suffix.length * suffix.length)) := by rw [pow_add]; ring
    _ ≤ Smax ^ 2 * L ^ (8 * K + 4 * K * K) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hL hexp) (sq_nonneg _)
    _ = _ := rfl

end
end MRTProposition61TypeIIUniformEnergyV3

#print axioms MRTProposition61TypeIIUniformEnergyV3.coefficientEnergy_critical_le_logPow_const
#print axioms MRTProposition61TypeIIUniformEnergyV3.scaledTypeIIPrefixCell_energy_le_logPow_const

#print axioms MRTProposition61TypeIIUniformEnergyV3.typeIICell_energy_product_le_fixedOrder_logPow
