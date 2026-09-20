import MRTLemma215DynamicTypeIIDyadicV3
import MRTLemma215DynamicCoefficientBoundsV3

/-!
# Coefficient bounds for dynamic Type-II packets

Both collected Type-II factors are sublists of the sorted literal HB factor
list.  Their convolutions therefore inherit the exact `tau_r log^(2r)`
majorant, and restriction to an output dyadic cell preserves it.
-/

namespace MRTLemma215DynamicTypeIICoefficientBoundsV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215DynamicCoefficientBoundsV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTLemma215DynamicTypeIIFactorizationV3
open MRTLemma215DynamicTypeIIDyadicV3
open MixedMellinCert

noncomputable section

/-- Any collected sublist of one sorted component has the same precise
divisor-order/logarithmic majorant as the high complement. -/
theorem subFactorConvolution_norm_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖factorConvolution sub n‖ ≤
      (tauAF sub.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := by
  have hn0 : n ≠ 0 := by omega
  have hA : 0 ≤ Real.log (2 * (n : ℝ)) ^ 2 := sq_nonneg _
  have hcoeff : ∀ f ∈ sub, ∀ d, d ∣ n →
      ‖f.coeff d‖ ≤ Real.log (2 * (n : ℝ)) ^ 2 := by
    intro f hf d hd
    have hbase := sortedDynamicComponentFactor_coeff_le_logSq
      logIndex zbag mbag (hsub f hf) d
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
  have hbound := factorConvolution_norm_le_tauAF_const sub hn0 hA
    hcoeff (dvd_refl n)
  simpa [pow_mul] using hbound

theorem typeIIPrefixFactor_mem_sorted
    (factors : List NatDyadicFactor) (s : ℕ)
    {f : NatDyadicFactor}
    (hf : f ∈ typeIIPrefixFactorList factors s) : f ∈ factors :=
  List.mem_of_mem_take hf

theorem typeIISuffixFactor_mem_sorted
    (factors : List NatDyadicFactor) (s : ℕ)
    {f : NatDyadicFactor}
    (hf : f ∈ typeIISuffixFactorList factors s) : f ∈ factors :=
  List.mem_of_mem_drop hf

/-- A dyadic output cell of either collected factor retains the exact
`tau_r log^(2r)` envelope. -/
theorem factorListDyadicCell_norm_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub)))
    {n : ℕ} (hn : 2 ≤ n) :
    ‖factorListDyadicCell sub cell n‖ ≤
      (tauAF sub.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * sub.length) := by
  change ‖(if 2 ≤ n ∧ n ≤ factorUpperProduct sub ∧
      (n - 1).log2 = (cell : ℕ) then factorConvolution sub n else 0)‖ ≤ _
  split_ifs
  · exact subFactorConvolution_norm_le
      logIndex zbag mbag sub hsub n hn
  · simp
    exact mul_nonneg (by positivity)
      (pow_nonneg (log_two_mul_nonneg (by omega)) _)

/-- The prefix cell, after absorbing the finite HB scalar, still has a
fixed divisor-order/power-log coefficient bound. -/
theorem exists_scaledTypeIIPrefixCell_bound
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (sub : List NatDyadicFactor)
    (hsub : ∀ f ∈ sub,
      f ∈ sortedComponentFactorList logIndex zbag mbag)
    (cell : Fin (sourceDyadicCount (factorUpperProduct sub))) :
    ∃ a : ℕ, ∀ n ∈ DeterminantCountWeld.dyadic (2 ^ (cell : ℕ)),
      ‖scaledTypeIIPrefixCell zbag mbag sub cell n‖ ≤
        (tauAF sub.length n : ℝ) * Real.log (2 * (n : ℝ)) ^ a := by
  let M : ℕ := 2 ^ (cell : ℕ)
  let base := Real.log (2 * ((M + 1 : ℕ) : ℝ))
  have hMone : 1 ≤ M := by
    simpa [M] using Nat.one_le_pow (cell : ℕ) 2 (by omega)
  have hbaseOne : 1 < base := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact Real.exp_one_lt_three.trans_le (by
      exact_mod_cast (show 3 ≤ 2 * (M + 1) by omega))
  obtain ⟨e, he⟩ := exists_nat_pow_ge_of_one_lt
    (C := ‖dynamicComponentScalarValue zbag mbag‖) hbaseOne
  refine ⟨e + 2 * sub.length, ?_⟩
  intro n hn
  have hnBounds := Finset.mem_Ioc.mp hn
  have hn2 : 2 ≤ n := by omega
  have hraw := factorListDyadicCell_norm_le
    logIndex zbag mbag sub hsub cell hn2
  have hbaseLe : base ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast Nat.mul_le_mul_left 2 (by omega : M + 1 ≤ n)
  have hbaseNonneg : 0 ≤ base := hbaseOne.le.trans' zero_le_one
  have hlogNonneg := log_two_mul_nonneg (show 1 ≤ n by omega)
  have hpow := pow_le_pow_left₀ hbaseNonneg hbaseLe e
  have he' : ‖dynamicComponentScalarValue zbag mbag‖ ≤ base ^ e := by
    simpa [base] using he
  unfold scaledTypeIIPrefixCell
  rw [dynamicComponentScalar_mul_eq_smul]
  change ‖dynamicComponentScalarValue zbag mbag *
      factorListDyadicCell sub cell n‖ ≤ _
  rw [norm_mul]
  calc
    ‖dynamicComponentScalarValue zbag mbag‖ *
        ‖factorListDyadicCell sub cell n‖ ≤
      base ^ e * ((tauAF sub.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (2 * sub.length)) :=
      mul_le_mul he' hraw (norm_nonneg _) (pow_nonneg hbaseNonneg _)
    _ ≤ Real.log (2 * (n : ℝ)) ^ e *
        ((tauAF sub.length n : ℝ) *
          Real.log (2 * (n : ℝ)) ^ (2 * sub.length)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (tauAF sub.length n : ℝ) *
        Real.log (2 * (n : ℝ)) ^ (e + 2 * sub.length) := by
      rw [pow_add]
      ring

end
end MRTLemma215DynamicTypeIICoefficientBoundsV3

#print axioms MRTLemma215DynamicTypeIICoefficientBoundsV3.subFactorConvolution_norm_le
#print axioms MRTLemma215DynamicTypeIICoefficientBoundsV3.factorListDyadicCell_norm_le
#print axioms MRTLemma215DynamicTypeIICoefficientBoundsV3.exists_scaledTypeIIPrefixCell_bound
