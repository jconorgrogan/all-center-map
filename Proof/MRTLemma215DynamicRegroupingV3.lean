import MRTLemma215DynamicOutcomeWeldV3

/-!
# Exact regrouping of surviving dynamic Type-d components

The published Type-`d_j` argument sorts the active dyadic factors, selects
the shortest large factor, and convolves every other factor into its
complement.  This file performs that regrouping literally and proves the
`M^2 <= N` geometry for `j >= 3`.
-/

namespace MRTLemma215DynamicRegroupingV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicPreliminaryV3
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3

noncomputable section

def sortedComponentFactorList
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    List NatDyadicFactor :=
  (dynamicComponentFactorList logIndex zbag mbag).mergeSort
    (fun f g => decide (f.length ≤ g.length))

theorem sortedComponentFactorList_perm
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (sortedComponentFactorList logIndex zbag mbag).Perm
      (dynamicComponentFactorList logIndex zbag mbag) := by
  exact List.mergeSort_perm _ _

theorem sortedComponentFactorList_pairwise
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (sortedComponentFactorList logIndex zbag mbag).Pairwise
      (fun f g => f.length ≤ g.length) := by
  exact List.pairwise_mergeSort' (fun f g : NatDyadicFactor =>
    f.length ≤ g.length) _

theorem factorConvolution_eq_coeff_prod (factors : List NatDyadicFactor) :
    factorConvolution factors =
      (factors.map NatDyadicFactor.coeff).prod := by
  induction factors with
  | nil => rfl
  | cons f factors ih =>
      simp only [factorConvolution, List.map_cons, List.prod_cons, ih]

theorem factorConvolution_eq_of_perm
    {factors₁ factors₂ : List NatDyadicFactor}
    (hperm : factors₁.Perm factors₂) :
    factorConvolution factors₁ = factorConvolution factors₂ := by
  rw [factorConvolution_eq_coeff_prod, factorConvolution_eq_coeff_prod]
  exact (hperm.map NatDyadicFactor.coeff).prod_eq

theorem factorConvolution_sortedComponentFactorList
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    factorConvolution (sortedComponentFactorList logIndex zbag mbag) =
      factorConvolution (dynamicComponentFactorList logIndex zbag mbag) :=
  factorConvolution_eq_of_perm
    (sortedComponentFactorList_perm logIndex zbag mbag)

/-- Sorting literal factors by natural length produces exactly the real scale
list used by the classifier. -/
theorem sortedComponent_realLengths_eq_scaleList
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    (sortedComponentFactorList logIndex zbag mbag).map
        (fun f => (f.length : ℝ)) =
      dynamicPreliminaryScaleList (some logIndex) zbag mbag := by
  let sorted := sortedComponentFactorList logIndex zbag mbag
  let original := dynamicComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  have hpermFactors : sorted.Perm original := by
    exact sortedComponentFactorList_perm logIndex zbag mbag
  have hcoeff := dynamicComponent_realLengths_eq_scaleMultiset
    logIndex zbag mbag
  have hscales : (↑scales : Multiset ℝ) =
      choiceScaleMultiset (some logIndex) +
        bagScaleMultiset zbag + bagScaleMultiset mbag := by
    exact Multiset.sort_eq
      (choiceScaleMultiset (some logIndex) +
        bagScaleMultiset zbag + bagScaleMultiset mbag) (· ≤ ·)
  have hcoe :
      (↑(sorted.map (fun f => (f.length : ℝ))) : Multiset ℝ) =
        ↑scales := by
    calc
      (↑(sorted.map (fun f => (f.length : ℝ))) : Multiset ℝ) =
          ↑(original.map (fun f => (f.length : ℝ))) :=
        Multiset.coe_eq_coe.mpr (hpermFactors.map _)
      _ = choiceScaleMultiset (some logIndex) +
          bagScaleMultiset zbag + bagScaleMultiset mbag := by
        simpa [original] using hcoeff
      _ = ↑scales := hscales.symm
  have hperm : (sorted.map (fun f => (f.length : ℝ))).Perm scales :=
    Multiset.coe_eq_coe.mp hcoe
  have hsortedFactors : sorted.Pairwise
      (fun f g => f.length ≤ g.length) := by
    exact sortedComponentFactorList_pairwise logIndex zbag mbag
  have hsortedReal : (sorted.map (fun f => (f.length : ℝ))).Pairwise
      (· ≤ ·) := by
    rw [List.pairwise_map]
    exact hsortedFactors.imp (fun h => by exact_mod_cast h)
  have hsortedScales : scales.Pairwise (· ≤ ·) := by
    exact dynamicPreliminaryScaleList_pairwise (some logIndex) zbag mbag
  exact hperm.eq_of_pairwise' hsortedReal hsortedScales

def complementFactorList (factors : List NatDyadicFactor) (s : ℕ) :
    List NatDyadicFactor :=
  factors.take s ++ factors.drop (s + 1)

/-- Exact convolution regrouping at one selected factor. -/
theorem factorConvolution_regroup_at
    (factors : List NatDyadicFactor) {s : ℕ} (hs : s < factors.length) :
    factorConvolution factors =
      factors[s].coeff * factorConvolution (complementFactorList factors s) := by
  have hdecomp : factors =
      factors.take s ++ factors[s] :: factors.drop (s + 1) := by
    calc
      factors = factors.take s ++ factors.drop s :=
        (List.take_append_drop s factors).symm
      _ = factors.take s ++ factors[s] :: factors.drop (s + 1) := by
        rw [List.drop_eq_getElem_cons hs]
  calc
    factorConvolution factors = factorConvolution
        (factors.take s ++ factors[s] :: factors.drop (s + 1)) :=
      congrArg factorConvolution hdecomp
    _ = factors[s].coeff *
        factorConvolution (complementFactorList factors s) := by
      rw [factorConvolution_append]
      simp only [factorConvolution]
      unfold complementFactorList
      rw [factorConvolution_append]
      ring

/-- Every literal dynamic factor has positive natural dyadic length. -/
theorem dynamicComponentFactorList_length_one
    {X : ℝ} {K k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    {f : NatDyadicFactor}
    (hf : f ∈ sortedComponentFactorList logIndex zbag mbag) :
    1 ≤ f.length := by
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hmem : (f.length : ℝ) ∈
      dynamicPreliminaryScaleList (some logIndex) zbag mbag := by
    rw [← hlengths]
    exact List.mem_map.mpr ⟨f, hf, rfl⟩
  have hone := dynamicPreliminaryScaleList_one
    (some logIndex) zbag mbag hmem
  exact_mod_cast hone

/-- In a sorted factor list, if at least three factors remain at `s`, then
the complement of the shortest tail factor has lower support at least its
square. -/
theorem square_selected_le_complementLowerProduct
    (factors : List NatDyadicFactor)
    (hsorted : factors.Pairwise (fun f g => f.length ≤ g.length))
    (hone : ∀ f ∈ factors, 1 ≤ f.length)
    {s : ℕ} (hs : s < factors.length)
    (htail : 3 ≤ factors.length - s) :
    factors[s].length ^ 2 ≤ factorLowerProduct (complementFactorList factors s) := by
  let M : ℝ := factors[s].length
  let prefixScales := (factors.take s).map (fun f => (f.length : ℝ))
  let restScales := (factors.drop (s + 1)).map (fun f => (f.length : ℝ))
  have hMone : 1 ≤ M := by
    change (1 : ℝ) ≤ (factors[s].length : ℝ)
    exact_mod_cast hone factors[s] (List.getElem_mem hs)
  have hrestLen : 2 ≤ restScales.length := by
    simp only [restScales, List.length_map, List.length_drop]
    omega
  have hrestLower : ∀ x ∈ restScales, M ≤ x := by
    intro x hx
    simp only [restScales, List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    have hfDropS : f ∈ factors.drop s := by
      rw [List.drop_eq_getElem_cons hs]
      exact List.mem_cons_of_mem _ hf
    let lengthScales := factors.map (fun f => (f.length : ℝ))
    have hsortedReal : lengthScales.Pairwise (· ≤ ·) := by
      dsimp only [lengthScales]
      rw [List.pairwise_map]
      exact hsorted.imp (fun h => by exact_mod_cast h)
    have hsReal : s < lengthScales.length := by simpa [lengthScales] using hs
    have hfReal : (f.length : ℝ) ∈ lengthScales.drop s := by
      dsimp only [lengthScales]
      rw [← List.map_drop]
      exact List.mem_map.mpr ⟨f, hfDropS, rfl⟩
    have hbound := drop_scales_ge_head hsortedReal hsReal hfReal
    simpa [lengthScales, M] using hbound
  have hpowRest : M ^ restScales.length ≤ restScales.prod :=
    pow_length_le_prod (by linarith) hrestLower
  have hpowTwo : M ^ 2 ≤ M ^ restScales.length :=
    pow_le_pow_right₀ hMone hrestLen
  have hprefixOne : 1 ≤ prefixScales.prod := by
    apply one_le_prod_of_one_le
    intro x hx
    simp only [prefixScales, List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    exact_mod_cast hone f (List.mem_of_mem_take hf)
  have hrestNonneg : 0 ≤ restScales.prod := by
    apply List.prod_nonneg
    intro x hx
    simp only [restScales, List.mem_map] at hx
    obtain ⟨f, hf, rfl⟩ := hx
    positivity
  have hreal : M ^ 2 ≤ prefixScales.prod * restScales.prod := by
    calc
      M ^ 2 ≤ M ^ restScales.length := hpowTwo
      _ ≤ restScales.prod := hpowRest
      _ = 1 * restScales.prod := by ring
      _ ≤ prefixScales.prod * restScales.prod :=
        mul_le_mul_of_nonneg_right hprefixOne hrestNonneg
  have hcast :
      ((factors[s].length ^ 2 : ℕ) : ℝ) ≤
        (factorLowerProduct (complementFactorList factors s) : ℝ) := by
    simpa [M, prefixScales, restScales, complementFactorList,
      factorLowerProduct, List.map_append, List.prod_append] using hreal
  exact_mod_cast hcast

/-- The exact `j >= 3` high-packet geometry used by the mixed-mean theorem. -/
theorem typeD_high_regrouping_geometry
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin m) (hjthree : 3 ≤ (j : ℕ))
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      2 ≤ factors[s].length ∧
        factors[s].length ^ 2 ≤
          factorLowerProduct (complementFactorList factors s) ∧
        factorConvolution (dynamicComponentFactorList logIndex zbag mbag) =
          factors[s].coeff *
            factorConvolution (complementFactorList factors s) := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  have hlengths := sortedComponent_realLengths_eq_scaleList
    logIndex zbag mbag
  have hdata := typeD_outcome_data logIndex zbag mbag j houtcome
  dsimp only at hdata
  rcases hdata with ⟨hsScale, hnotII, hjEq, hjone⟩
  have hlenEq : factors.length = scales.length := by
    have := congrArg List.length hlengths
    simpa [factors, scales] using this
  have hs : s < factors.length := by
    rw [hlenEq]
    simpa [s, scales] using hsScale
  have htail : 3 ≤ factors.length - s := by
    rw [hlenEq]
    have : 3 ≤ scales.length - s := by
      calc
        3 ≤ (j : ℕ) := hjthree
        _ = scales.length - s := by simpa [s, scales] using hjEq
    exact this
  have hone : ∀ f ∈ factors, 1 ≤ f.length := by
    intro f hf
    exact dynamicComponentFactorList_length_one logIndex zbag mbag
      (by simpa [factors] using hf)
  have hsquare := square_selected_le_complementLowerProduct factors
    (by simpa [factors] using
      sortedComponentFactorList_pairwise logIndex zbag mbag)
    hone hs htail
  have hshort : 2 ≤ factors[s].length := by
    have honeShort := hone factors[s] (List.getElem_mem hs)
    by_contra h
    have hle : factors[s].length ≤ 1 := by omega
    have heq : factors[s].length = 1 := le_antisymm hle honeShort
    have hscaleAt : scales[s] = (factors[s].length : ℝ) := by
      have hlengths' : factors.map (fun f => (f.length : ℝ)) = scales := by
        simpa [factors, scales] using hlengths
      have hsMap : s < (factors.map (fun f => (f.length : ℝ))).length := by
        simpa using hs
      have hget := congrArg (fun l : List ℝ => l[s]?) hlengths'
      change (factors.map (fun f => (f.length : ℝ)))[s]? = scales[s]? at hget
      rw [List.getElem?_eq_getElem hsMap,
        List.getElem?_eq_getElem hsScale] at hget
      simpa using hget.symm
    have hprefixSmall := largestSmallPrefix_succ_not_small
      (scales := scales) (smallScale := Real.rpow X delta) hsScale
    have hsmall : 1 ≤ Real.rpow X delta :=
      Real.one_le_rpow (by linarith) hdelta.le
    have hprefix := largestSmallPrefix_spec (scales := scales) hsmall
    change scalePrefixProduct scales s ≤ Real.rpow X delta at hprefix
    apply hprefixSmall
    rw [scalePrefixProduct_succ scales hsScale]
    rw [show scales[s] = 1 by simpa [heq] using hscaleAt]
    simpa using hprefix
  have hregroup : factorConvolution
        (dynamicComponentFactorList logIndex zbag mbag) =
      factors[s].coeff * factorConvolution (complementFactorList factors s) := by
    rw [← factorConvolution_sortedComponentFactorList logIndex zbag mbag]
    exact factorConvolution_regroup_at factors hs
  exact ⟨hs, hshort, hsquare, hregroup⟩

end
end MRTLemma215DynamicRegroupingV3

#print axioms MRTLemma215DynamicRegroupingV3.sortedComponent_realLengths_eq_scaleList
#print axioms MRTLemma215DynamicRegroupingV3.factorConvolution_regroup_at
#print axioms MRTLemma215DynamicRegroupingV3.typeD_high_regrouping_geometry
