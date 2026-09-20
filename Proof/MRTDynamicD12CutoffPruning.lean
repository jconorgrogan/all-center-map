import MRTDynamicD12CarrierIdentities
import MRTDynamicD12PerronMassAssembly
import MRTDynamicD12LiteralMass
import MRTDynamicD12SourceSupport
import MRTLemma215OpenIntervalCutoffV3

/-! Literal support pruning for the D12 Perron error.

The public `SupportedNear` interface is deliberately a dilated support
statement, so it alone does not imply vanishing below `2X`.  The exact
factor-convolution identity supplies the sharper lower endpoint.  This weld
keeps the source mask and all scalar/bag data intact and only prunes a bag
whose actual lower product lies above the literal `(X,2X]` source interval.
-/
namespace MRTDynamicD12CutoffPruning

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPMRTCorollary53Source MAPHBPerronSourceData
open MAPMRTCorollary25
open MAPDynamicHBSourceV3 MAPFinishDynamicThreeTypeTrace
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicClassificationV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighPacketCertificateV3
open MRTDynamicD12LiteralMass MRTDynamicD12SourceSupport
open MRTDynamicD12CarrierIdentities
open MRTLemma215OpenIntervalCutoffV3

noncomputable section

set_option maxHeartbeats 800000

/-- If the literal lower support product exceeds `2X`, the actual masked
D12 coefficient is identically zero. -/
theorem dynamicD12FactorizedCoeff_eq_zero_of_lower_gt_twoX
    {X delta : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin
      (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hprod : 2 * X <
      (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ)) :
    dynamicD12FactorizedCoeff delta logIndex zbag mbag = 0 := by
  let factors := sortedComponentFactorList logIndex zbag mbag
  have hne : factors ≠ [] := by
    intro h
    have hperm := sortedComponentFactorList_perm logIndex zbag mbag
    have hlength := hperm.length_eq
    change factors.length = _ at hlength
    rw [h] at hlength
    simp [dynamicComponentFactorList] at hlength
  have hpre := dynamicPreliminaryComponent_eq_smul_sorted hX hK
    logIndex zbag mbag
  have hzero : (fun n : ℕ =>
      if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
        dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0) = 0 := by
    funext n
    by_cases hn : n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊
    · rw [if_pos hn, hpre]
      obtain ⟨head, tail, hcons⟩ := List.exists_cons_of_ne_nil hne
      have hcons' : sortedComponentFactorList logIndex zbag mbag =
          head :: tail := by
        simpa [factors] using hcons
      have hnReal : (n : ℝ) ≤ 2 * X := by
        have hfloor : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by
          exact_mod_cast (Finset.mem_Ioc.mp hn).2
        exact hfloor.trans (Nat.floor_le (by positivity))
      have hprod' : 2 * X <
          (factorLowerProduct (head :: tail) : ℝ) := by
        simpa [factors, hcons] using hprod
      have hnle : n ≤ factorLowerProduct (head :: tail) := by
        exact_mod_cast (hnReal.trans_lt hprod').le
      rw [hcons']
      change dynamicComponentScalarValue zbag mbag *
        factorConvolution (head :: tail) n = 0
      rw [factorConvolution_zero_of_le head tail hnle, mul_zero]
    · rw [if_neg hn]
      rfl
  calc
    dynamicD12FactorizedCoeff delta logIndex zbag mbag =
        maskedDynamicComponentV3 logIndex zbag mbag :=
      dynamicD12FactorizedCoeff_eq_masked hX delta hK logIndex zbag mbag
    _ = intervalCutoff (openSourceLeft X) (2 * X)
        (dynamicPreliminaryComponent (some logIndex) zbag mbag) :=
      maskedDynamicComponentV3_eq_intervalCutoff (by linarith : 0 ≤ X)
        logIndex zbag mbag
    _ = (fun n : ℕ =>
        if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
          dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0) :=
      (openMask_eq_intervalCutoff (by linarith : 0 ≤ X) _).symm
    _ = 0 := hzero

/-- The component integral is zero under the same literal lower-product
condition, so such a bag may be removed before applying the Perron error. -/
theorem componentIntegral_d12_eq_zero_of_lower_gt_twoX
    {X H beta eta : ℝ} {q : ℕ} {delta : ℝ} {K k : ℕ}
    (hX : 1 ≤ X) (hK : 1 ≤ K) (hk : k < K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin
      (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hprod : 2 * X <
      (factorLowerProduct (sortedComponentFactorList logIndex zbag mbag) : ℝ))
    (component : OuterComponent) :
    componentIntegral X H 1 q
      (dynamicD12FactorizedCoeff delta logIndex zbag mbag)
      beta eta component = 0 := by
  rw [dynamicD12FactorizedCoeff_eq_zero_of_lower_gt_twoX hX hK hk
    logIndex zbag mbag hprod]
  simp [componentIntegral, characterWindow, criticalDirichletPolynomial]

end
end MRTDynamicD12CutoffPruning

#print axioms MRTDynamicD12CutoffPruning.dynamicD12FactorizedCoeff_eq_zero_of_lower_gt_twoX
#print axioms MRTDynamicD12CutoffPruning.componentIntegral_d12_eq_zero_of_lower_gt_twoX
