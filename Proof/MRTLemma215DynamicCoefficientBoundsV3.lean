import MRTLemma215ComplementDyadicV3

/-!
# Pointwise coefficient bounds for dynamic Type-d packets

This module keeps the coefficient ledger source-facing.  Each literal shell
is bounded directly, and an abstract induction converts per-factor bounds
into the exact `tau_r` majorant for a convolution of `r` factors.
-/

namespace MRTLemma215DynamicCoefficientBoundsV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215ComplementDyadicV3
open MixedMellinCert
open MAPHeathBrownFiniteIdentity

noncomputable section

theorem one_le_log_two_mul_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.log (2 * (n : ℝ)) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  have hthree : (3 : ℝ) ≤ 2 * (n : ℝ) := by
    exact_mod_cast (show 3 ≤ 2 * n by omega)
  exact Real.exp_one_lt_three.le.trans hthree

theorem log_two_mul_nonneg {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ Real.log (2 * (n : ℝ)) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ 2 * n by omega)

theorem one_le_log_two_mul_sq_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
  have h := one_le_log_two_mul_of_two_le hn
  nlinarith

theorem norm_complexLogAF_le_logSq {n : ℕ} (hn : 2 ≤ n) :
    ‖complexLogAF n‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hmono : Real.log (n : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log hnpos
    nlinarith
  have hone := one_le_log_two_mul_of_two_le hn
  change ‖((ArithmeticFunction.log n : ℝ) : ℂ)‖ ≤
    Real.log (2 * (n : ℝ)) ^ 2
  rw [ArithmeticFunction.log_apply]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
  nlinarith

theorem norm_complexZetaAF_le_logSq {n : ℕ} (hn : 2 ≤ n) :
    ‖complexZetaAF n‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  change ‖(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) n : ℝ) : ℂ)‖ ≤
    Real.log (2 * (n : ℝ)) ^ 2
  simpa [ArithmeticFunction.zeta_apply, hn0] using
    one_le_log_two_mul_sq_of_two_le hn

theorem norm_dynamicComplexTruncatedMoebiusAF_le_logSq
    {X : ℝ} {K n : ℕ} (hn : 2 ≤ n) :
    ‖dynamicComplexTruncatedMoebiusAF X K n‖ ≤
      Real.log (2 * (n : ℝ)) ^ 2 := by
  have hone := one_le_log_two_mul_sq_of_two_le hn
  unfold dynamicComplexTruncatedMoebiusAF complexifyArithmetic
    realTruncatedMoebius
  change ‖((if (n : ℝ) ≤ dynamicHBCutoff X K then
      (ArithmeticFunction.moebius n : ℝ) else 0 : ℝ) : ℂ)‖ ≤
    Real.log (2 * (n : ℝ)) ^ 2
  by_cases hcut : (n : ℝ) ≤ dynamicHBCutoff X K
  · rw [if_pos hcut]
    have hmu := ArithmeticFunction.abs_moebius_le_one (n := n)
    have hnorm : ‖((ArithmeticFunction.moebius n : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact_mod_cast hmu
    exact hnorm.trans hone
  · rw [if_neg hcut]
    simp
    positivity

theorem norm_sourceDyadicArithmetic_le_logSq_of_base
    {N n : ℕ} {f : ArithmeticFunction ℂ}
    (hbase : ‖f n‖ ≤ Real.log (2 * (n : ℝ)) ^ 2)
    (j : Fin (sourceDyadicCount N)) :
    ‖sourceDyadicArithmetic N f j n‖ ≤
      Real.log (2 * (n : ℝ)) ^ 2 := by
  change ‖(if 2 ≤ n ∧ n ≤ N ∧ (n - 1).log2 = (j : ℕ)
      then f n else 0)‖ ≤ Real.log (2 * (n : ℝ)) ^ 2
  split_ifs
  · exact hbase
  · simp
    positivity

theorem norm_dynamicLogFactor_coeff_le_logSq
    {X : ℝ}
    (j : Fin (sourceDyadicCount (hbFactorCutoff X))) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖(dynamicLogFactor X j).coeff n‖ ≤
      Real.log (2 * (n : ℝ)) ^ 2 :=
  norm_sourceDyadicArithmetic_le_logSq_of_base
    (norm_complexLogAF_le_logSq hn) j

theorem norm_dynamicZetaFactor_coeff_le_logSq
    {X : ℝ}
    (j : Fin (sourceDyadicCount (hbFactorCutoff X))) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖(dynamicZetaFactor X j).coeff n‖ ≤
      Real.log (2 * (n : ℝ)) ^ 2 :=
  norm_sourceDyadicArithmetic_le_logSq_of_base
    (norm_complexZetaAF_le_logSq hn) j

theorem norm_dynamicMoebiusFactor_coeff_le_logSq
    {X : ℝ} {K : ℕ}
    (j : Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)) {n : ℕ}
    (hn : 2 ≤ n) :
    ‖(dynamicMoebiusFactor X K j).coeff n‖ ≤
      Real.log (2 * (n : ℝ)) ^ 2 :=
  norm_sourceDyadicArithmetic_le_logSq_of_base
    (norm_dynamicComplexTruncatedMoebiusAF_le_logSq hn) j

/-- Exact ordered-factorization count behind `tau_(r+1)`. -/
theorem sum_tauAF_right_antidiagonal (r n : ℕ) (hn : n ≠ 0) :
    (∑ z ∈ n.divisorsAntidiagonal, tauAF r z.2) = tauAF (r + 1) n := by
  have hpow : (tauAF (r + 1) : ArithmeticFunction ℕ) =
      (ArithmeticFunction.zeta : ArithmeticFunction ℕ) * tauAF r := by
    unfold tauAF
    rw [pow_succ']
  rw [hpow, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro z hz
  have hz1 : z.1 ≠ 0 := by
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hz).1
    intro h
    rw [h] at hmul
    simp at hmul
    exact hn hmul.symm
  rw [ArithmeticFunction.zeta_apply_ne hz1]
  simp

/-- An `r`-factor convolution whose factors are bounded by `A` on every
divisor of `N` is bounded by `tau_r(n) A^r` at every `n | N`. -/
theorem factorConvolution_norm_le_tauAF_const
    (factors : List NatDyadicFactor) {N : ℕ} (hN : N ≠ 0)
    {A : ℝ} (hA : 0 ≤ A)
    (hcoeff : ∀ f ∈ factors, ∀ d, d ∣ N → ‖f.coeff d‖ ≤ A)
    {n : ℕ} (hn : n ∣ N) :
    ‖factorConvolution factors n‖ ≤
      (tauAF factors.length n : ℝ) * A ^ factors.length := by
  induction factors generalizing n with
  | nil =>
      have hn0 : n ≠ 0 := fun h => hN (by simpa [h] using hn)
      by_cases hn1 : n = 1
      · subst n
        simp [factorConvolution, tauAF]
      · simp [factorConvolution, tauAF, ArithmeticFunction.one_apply_ne hn1]
  | cons head tail ih =>
      have hn0 : n ≠ 0 := fun h => hN (by simpa [h] using hn)
      rw [factorConvolution, ArithmeticFunction.mul_apply]
      calc
        ‖∑ z ∈ n.divisorsAntidiagonal,
            head.coeff z.1 * factorConvolution tail z.2‖ ≤
            ∑ z ∈ n.divisorsAntidiagonal,
              ‖head.coeff z.1 * factorConvolution tail z.2‖ :=
          norm_sum_le _ _
        _ ≤ ∑ z ∈ n.divisorsAntidiagonal,
            A * ((tauAF tail.length z.2 : ℝ) * A ^ tail.length) := by
          apply Finset.sum_le_sum
          intro z hz
          have hmul := (Nat.mem_divisorsAntidiagonal.mp hz).1
          have hz1dvd : z.1 ∣ n := ⟨z.2, hmul.symm⟩
          have hz2dvd : z.2 ∣ n :=
            ⟨z.1, by simpa [Nat.mul_comm] using hmul.symm⟩
          have hhead := hcoeff head (by simp) z.1 (hz1dvd.trans hn)
          have htailCoeff : ∀ f ∈ tail, ∀ d, d ∣ N → ‖f.coeff d‖ ≤ A := by
            intro f hf
            exact hcoeff f (by simp [hf])
          have htail := ih htailCoeff (hz2dvd.trans hn)
          rw [norm_mul]
          exact mul_le_mul hhead htail (norm_nonneg _) hA
        _ = (tauAF (head :: tail).length n : ℝ) *
            A ^ (head :: tail).length := by
          rw [List.length_cons, pow_succ]
          have htau := sum_tauAF_right_antidiagonal tail.length n hn0
          push_cast at htau
          rw [← htau]
          rw [Nat.cast_sum]
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro z hz
          ring

/-- Every factor in the sorted literal HB component obeys the same
log-square pointwise envelope.  At `n = 0,1` this follows from the strict
left endpoint of its dyadic support, so no artificial positive-index
hypothesis is passed to later convolution estimates. -/
theorem sortedDynamicComponentFactor_coeff_le_logSq
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {f : NatDyadicFactor}
    (hf : f ∈ sortedComponentFactorList logIndex zbag mbag) (n : ℕ) :
    ‖f.coeff n‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
  by_cases hn : 2 ≤ n
  · have hperm := sortedComponentFactorList_perm logIndex zbag mbag
    have hfOriginal : f ∈ dynamicComponentFactorList logIndex zbag mbag :=
      (hperm.mem_iff).mp hf
    unfold dynamicComponentFactorList at hfOriginal
    simp only [List.mem_cons, List.mem_append] at hfOriginal
    rcases hfOriginal with hlog | hzeta | hmoebius
    · subst f
      exact norm_dynamicLogFactor_coeff_le_logSq logIndex hn
    · obtain ⟨j, hj, rfl⟩ :=
        MRTLemma215DynamicHighProvenanceV3.mem_bagFactorList_exists
          (dynamicZetaFactor X) zbag hzeta
      exact norm_dynamicZetaFactor_coeff_le_logSq j hn
    · obtain ⟨j, hj, rfl⟩ :=
        MRTLemma215DynamicHighProvenanceV3.mem_bagFactorList_exists
          (dynamicMoebiusFactor X K) mbag hmoebius
      exact norm_dynamicMoebiusFactor_coeff_le_logSq j hn
  · have hnle : n ≤ f.length := by
      have hfone := dynamicComponentFactorList_length_one
        logIndex zbag mbag hf
      omega
    have hnmem : n ∉ DeterminantCountWeld.dyadic f.length := by
      simp only [DeterminantCountWeld.dyadic, Finset.mem_Ioc]
      omega
    rw [f.support n hnmem]
    simp
    positivity

/-- The complement left after selecting one high Type-d factor inherits the
same literal pointwise envelope factor by factor. -/
theorem complementDynamicFactor_coeff_le_logSq
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ) {f : NatDyadicFactor}
    (hf : f ∈ complementFactorList
      (sortedComponentFactorList logIndex zbag mbag) s) (n : ℕ) :
    ‖f.coeff n‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
  apply sortedDynamicComponentFactor_coeff_le_logSq logIndex zbag mbag
  · unfold complementFactorList at hf
    rcases List.mem_append.mp hf with hf | hf
    · exact List.mem_of_mem_take hf
    · exact List.mem_of_mem_drop hf

/-- The literal Type-d complement has the published divisor-function
majorant, with the precise number of active factors as divisor order. -/
theorem complementFactorConvolution_norm_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s n : ℕ) (hn : 2 ≤ n) :
    let complement := complementFactorList
      (sortedComponentFactorList logIndex zbag mbag) s
    ‖factorConvolution complement n‖ ≤
      (tauAF complement.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * complement.length) := by
  dsimp only
  let complement := complementFactorList
    (sortedComponentFactorList logIndex zbag mbag) s
  have hn0 : n ≠ 0 := by omega
  have hA : 0 ≤ Real.log (2 * (n : ℝ)) ^ 2 := sq_nonneg _
  have hcoeff : ∀ f ∈ complement, ∀ d, d ∣ n →
      ‖f.coeff d‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
    intro f hf d hd
    have hbase := complementDynamicFactor_coeff_le_logSq
      logIndex zbag mbag s hf d
    have hd0 : d ≠ 0 := by
      intro hdz
      subst d
      simp at hd
      exact hn0 hd
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hd
    have hdpos : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
    have hlogNonneg : 0 ≤ Real.log (2 * (d : ℝ)) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ 2 * d by omega)
    have hlogLe : Real.log (2 * (d : ℝ)) ≤
        Real.log (2 * (n : ℝ)) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.mul_le_mul_left 2 hdle
    exact hbase.trans (by nlinarith)
  have hbound := factorConvolution_norm_le_tauAF_const complement hn0 hA
    hcoeff (dvd_refl n)
  simpa [pow_mul, complement] using hbound

/-- Restricting the complement to one standard dyadic output shell preserves
the exact divisor-order/logarithmic coefficient envelope. -/
theorem dyadicComplement_norm_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (s : ℕ)
    (j : Fin (sourceDyadicCount (factorUpperProduct
      (complementFactorList
        (sortedComponentFactorList logIndex zbag mbag) s))))
    {n : ℕ} (hn : 2 ≤ n) :
    let complement := complementFactorList
      (sortedComponentFactorList logIndex zbag mbag) s
    ‖sourceDyadicArithmetic (factorUpperProduct complement)
        (factorConvolution complement) j n‖ ≤
      (tauAF complement.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * complement.length) := by
  dsimp only
  change ‖(if 2 ≤ n ∧ n ≤ factorUpperProduct
      (complementFactorList
        (sortedComponentFactorList logIndex zbag mbag) s) ∧
      (n - 1).log2 = (j : ℕ) then
        factorConvolution (complementFactorList
          (sortedComponentFactorList logIndex zbag mbag) s) n else 0)‖ ≤ _
  split_ifs
  · exact complementFactorConvolution_norm_le logIndex zbag mbag s n hn
  · simp
    exact mul_nonneg (by positivity)
      (pow_nonneg (log_two_mul_nonneg (by omega)) _)

end
end MRTLemma215DynamicCoefficientBoundsV3

#print axioms MRTLemma215DynamicCoefficientBoundsV3.sum_tauAF_right_antidiagonal
#print axioms MRTLemma215DynamicCoefficientBoundsV3.factorConvolution_norm_le_tauAF_const
#print axioms MRTLemma215DynamicCoefficientBoundsV3.sortedDynamicComponentFactor_coeff_le_logSq
#print axioms MRTLemma215DynamicCoefficientBoundsV3.complementDynamicFactor_coeff_le_logSq
#print axioms MRTLemma215DynamicCoefficientBoundsV3.complementFactorConvolution_norm_le
#print axioms MRTLemma215DynamicCoefficientBoundsV3.dyadicComplement_norm_le
