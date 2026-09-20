import MRTLemma215DynamicTypeIICellPruningV3

/-! # Fixed finite envelopes for dynamic Type-II aggregation -/

namespace MRTLemma215DynamicTypeIIFiniteEnvelopeV3

open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicTypeIIFactorizationV3

noncomputable section

theorem bagFactorList_length_le
    {n k : ℕ} (factor : Fin n → NatDyadicFactor)
    (bag : Sym (Option (Fin n)) k) :
    (bagFactorList factor bag).length ≤ k := by
  unfold bagFactorList
  calc
    (List.filterMap (optionFactor factor)
      (multisetRepresentative (↑bag : Multiset (Option (Fin n))))).length ≤
        (multisetRepresentative
          (↑bag : Multiset (Option (Fin n)))).length :=
      List.length_filterMap_le _ _
    _ = k := by
      have hcoe := coe_multisetRepresentative
        (↑bag : Multiset (Option (Fin n)))
      have hcard := congrArg Multiset.card hcoe
      simpa using hcard

theorem dynamicComponentFactorList_length_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (dynamicComponentFactorList logIndex zbag mbag).length ≤ 2 * k + 2 := by
  unfold dynamicComponentFactorList
  simp only [List.length_cons, List.length_append]
  have hz := bagFactorList_length_le (dynamicZetaFactor X) zbag
  have hm := bagFactorList_length_le (dynamicMoebiusFactor X K) mbag
  omega

theorem sortedComponentFactorList_length_le
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (sortedComponentFactorList logIndex zbag mbag).length ≤ 2 * k + 2 := by
  have hperm := sortedComponentFactorList_perm logIndex zbag mbag
  rw [hperm.length_eq]
  exact dynamicComponentFactorList_length_le logIndex zbag mbag

/-- For a branch `k<K`, every prefix dilation is bounded by the fixed
`2^(2K)` factor. -/
theorem typeIIPrefix_pow_length_le_branchEnvelope
    {X : ℝ} {K : ℕ} (branch : Fin K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X))))
      (branch : ℕ))
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊)))
      ((branch : ℕ) + 1))
    (s : ℕ) :
    2 ^ (typeIIPrefixFactorList
      (sortedComponentFactorList logIndex zbag mbag) s).length ≤
      2 ^ (2 * K) := by
  apply Nat.pow_le_pow_right (by omega)
  have hpref : (typeIIPrefixFactorList
      (sortedComponentFactorList logIndex zbag mbag) s).length ≤
      (sortedComponentFactorList logIndex zbag mbag).length := by
    unfold typeIIPrefixFactorList
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  have hall := sortedComponentFactorList_length_le logIndex zbag mbag
  omega

end
end MRTLemma215DynamicTypeIIFiniteEnvelopeV3

#print axioms MRTLemma215DynamicTypeIIFiniteEnvelopeV3.bagFactorList_length_le
#print axioms MRTLemma215DynamicTypeIIFiniteEnvelopeV3.dynamicComponentFactorList_length_le
#print axioms MRTLemma215DynamicTypeIIFiniteEnvelopeV3.typeIIPrefix_pow_length_le_branchEnvelope
