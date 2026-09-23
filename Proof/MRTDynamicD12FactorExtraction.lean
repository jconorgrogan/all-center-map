import MRTLemma215DynamicHighProvenanceV3
import MAPFinishDynamicThreeTypeTrace

/-!
# Literal smooth-tail extraction for the dynamic d1/d2 branches

The whole tail after the classifier's small prefix consists of original log
or zeta shells. Its length is exactly the classifier label. No source mask,
scalar multiplicity, or dyadic bag is removed in this extraction.
-/
namespace MRTDynamicD12FactorExtraction

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicPreliminaryV3 MRTLemma215DynamicSupportV3
open MRTLemma215DynamicFactorExtractionV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicOutcomeWeldV3 MRTLemma215DynamicRegroupingV3
open MRTLemma215DynamicHighProvenanceV3 MRTLemma215DynamicClassificationV3
open MAPFinishDynamicThreeTypeTrace

noncomputable section

/-- Source provenance, including the literal upper cutoff of each shell. -/
def IsSourceSmoothFactor (X : ℝ)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (f : NatDyadicFactor) : Prop :=
  f = dynamicLogFactor X logIndex ∨
    ∃ zetaIndex, f = dynamicZetaFactor X zetaIndex

theorem selected_le_of_mem_drop
    {factors : List NatDyadicFactor}
    (hsorted : factors.Pairwise (fun f g => f.length ≤ g.length))
    {s : ℕ} (hs : s < factors.length) {f : NatDyadicFactor}
    (hf : f ∈ factors.drop s) : factors[s].length ≤ f.length := by
  rw [List.drop_eq_getElem_cons hs, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact le_rfl
  · have hp := hsorted.drop (i := s)
    rw [List.drop_eq_getElem_cons hs] at hp
    exact (List.pairwise_cons.mp hp).1 f hf

/-- Every tail factor, not just the selected first one, is a literal smooth
shell. The Moebius exclusion uses the actual dynamic cutoff. -/
theorem typeD_tail_is_sourceSmooth
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {k m : ℕ} (hm : 1 ≤ m) (hdeltaM : delta < (m : ℝ)⁻¹)
    (hgeom : Real.rpow X delta *
      (2 * Real.rpow X ((m : ℝ)⁻¹)) ≤ 2 * H₀)
    (hcut : 2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) (k + 1))
    (j : Fin m)
    (hout : dynamicComponentOutcome m delta H₀ logIndex zbag mbag = .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
    ∀ f ∈ factors.drop s, IsSourceSmoothFactor X logIndex f := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
  obtain ⟨hs, hlarge⟩ := typeD_selected_gt_tailThreshold hX hdelta hm hgeom
    logIndex zbag mbag j hout
  intro f hf
  have hle := selected_le_of_mem_drop
    (sortedComponentFactorList_pairwise logIndex zbag mbag) hs hf
  have hsmall : Real.rpow X delta < (f.length : ℝ) := by
    have hsel := (tailThreshold_gt_smallScale hX hm hdeltaM).trans hlarge
    exact hsel.trans_le (by exact_mod_cast hle)
  have hmem : f ∈ dynamicComponentFactorList logIndex zbag mbag :=
    (sortedComponentFactorList_perm logIndex zbag mbag).mem_iff.mp
      (List.mem_of_mem_drop hf)
  unfold dynamicComponentFactorList at hmem
  simp only [List.mem_cons, List.mem_append] at hmem
  rcases hmem with hlog | hzeta | hmoebius
  · exact Or.inl hlog
  · exact Or.inr (mem_bagFactorList_exists (dynamicZetaFactor X) zbag hzeta)
  · obtain ⟨i, hi⟩ := mem_bagFactorList_exists
      (dynamicMoebiusFactor X (hbOrder delta)) mbag hmoebius
    have hbound := dynamicMoebiusShellScale_le_rpow hX hdelta hcut i
    rw [hi] at hsmall
    have : Real.rpow X delta < (2 ^ (i : ℕ) : ℝ) := by
      simpa [dynamicMoebiusFactor] using hsmall
    exact False.elim (not_lt_of_ge hbound this)

/-- The prefix bound is in the original classifier normalization; the upper
support keeps the exact power of two for the number of active factors. -/
theorem smallPrefix_upperProduct_le
    {X delta : ℝ} (hX : 1 ≤ X) (hdelta : 0 ≤ delta) {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
    (factorLowerProduct (factors.take s) : ℝ) ≤ Real.rpow X delta ∧
      (factorUpperProduct (factors.take s) : ℝ) ≤
        (2 : ℝ) ^ (factors.take s).length * Real.rpow X delta := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have heq : (factorLowerProduct (factors.take s) : ℝ) =
      scalePrefixProduct scales s := by
    unfold factorLowerProduct scalePrefixProduct
    rw [Nat.cast_list_prod]
    have h := congrArg (fun l : List ℝ => (l.take s).prod)
      (sortedComponent_realLengths_eq_scaleList logIndex zbag mbag)
    simpa only [List.map_map, Function.comp_def, List.map_take] using! h
  have hsmall : (factorLowerProduct (factors.take s) : ℝ) ≤ Real.rpow X delta := by
    rw [heq]
    exact largestSmallPrefix_spec (Real.one_le_rpow hX hdelta)
  refine ⟨hsmall, ?_⟩
  rw [factorUpperProduct_eq_pow_mul_lowerProduct, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact mul_le_mul_of_nonneg_left hsmall (by positivity)

/-- The dynamic label is precisely the length of the actual sorted tail. -/
theorem typeD_tail_length
    {X delta H₀ : ℝ} {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin m)
    (hout : dynamicComponentOutcome m delta H₀ logIndex zbag mbag = .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
    (factors.drop s).length = (j : ℕ) := by
  dsimp only
  obtain ⟨hs, hj, hregroup⟩ := typeD_regrouping_geometry logIndex zbag mbag j hout
  simpa only [List.length_drop] using hj.symm

/-- Exact product split, retaining the source scalar and sharp `(X,2X]` mask. -/
theorem maskedDynamicComponent_eq_prefix_mul_tail
    {X delta : ℝ} (hX : 1 ≤ X) {K k : ℕ} (hK : 1 ≤ K)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin (sourceDyadicCount
      ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) (n : ℕ) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag) (Real.rpow X delta)
    maskedDynamicComponentV3 logIndex zbag mbag n =
      if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
        (dynamicComponentScalar zbag mbag *
          (factorConvolution (factors.take s) * factorConvolution (factors.drop s))) n
      else 0 := by
  dsimp only
  unfold maskedDynamicComponentV3
  split_ifs with hn
  · rw [dynamicPreliminaryComponent_some_eq_factorConvolution hX hK]
    rw [← factorConvolution_sortedComponentFactorList logIndex zbag mbag]
    rw [← factorConvolution_append, List.take_append_drop]
  · rfl

end
end MRTDynamicD12FactorExtraction

#print axioms MRTDynamicD12FactorExtraction.typeD_tail_is_sourceSmooth
#print axioms MRTDynamicD12FactorExtraction.smallPrefix_upperProduct_le
#print axioms MRTDynamicD12FactorExtraction.typeD_tail_length
#print axioms MRTDynamicD12FactorExtraction.maskedDynamicComponent_eq_prefix_mul_tail
