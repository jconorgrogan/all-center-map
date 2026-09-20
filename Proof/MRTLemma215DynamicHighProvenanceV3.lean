import MRTLemma215DynamicRegroupingV3

/-!
# Source provenance of the selected high Type-d factor

For `j >= 3`, the selected shortest tail factor must be one of the displayed
zeta/log factors in MRT Lemma 2.15.  It cannot be a truncated Moebius factor,
because every such factor lies below `X^delta` while the selected tail lies
above `2 X^(1/m)`.
-/

namespace MRTLemma215DynamicHighProvenanceV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicPreliminaryV3
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215ScaleClassifierV3 MRTLemma215DynamicOutcomeWeldV3
open MRTLemma215DynamicRegroupingV3

noncomputable section

theorem mem_bagFactorList_exists
    {n r : ℕ} (factor : Fin n → NatDyadicFactor)
    (bag : Sym (Option (Fin n)) r) {f : NatDyadicFactor}
    (hf : f ∈ bagFactorList factor bag) :
    ∃ j : Fin n, f = factor j := by
  unfold bagFactorList at hf
  obtain ⟨c, hc, heq⟩ := List.mem_filterMap.mp hf
  cases c with
  | none => simp [optionFactor] at heq
  | some j =>
      simp only [optionFactor, Option.some.injEq] at heq
      exact ⟨j, heq.symm⟩

/-- The selected Type-d tail factor lies above the exact source threshold. -/
theorem typeD_selected_gt_tailThreshold
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k m : ℕ} (hmone : 1 ≤ m)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((m : ℝ)⁻¹)) ≤ 2 * H₀)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin m)
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      2 * Real.rpow X ((m : ℝ)⁻¹) < (factors[s].length : ℝ) := by
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
  have hpos : ∀ x ∈ scales, 0 < x := by
    intro x hx
    exact dynamicPreliminaryScaleList_pos (some logIndex) zbag mbag hx
  have hsmall : 1 ≤ Real.rpow X delta :=
    Real.one_le_rpow (by linarith) hdelta.le
  have hfirst : 2 * Real.rpow X ((m : ℝ)⁻¹) < scales[s] := by
    exact firstLargeScale_gt hpos hsmall hgeom
      (by simpa [s, scales] using hsScale)
      (by simpa [s, scales] using hnotII)
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
  exact ⟨hs, by simpa [hscaleAt] using hfirst⟩

theorem tailThreshold_gt_smallScale
    {X delta : ℝ} (hX : 2 ≤ X) {m : ℕ} (hmone : 1 ≤ m)
    (hdelta : delta < (m : ℝ)⁻¹) :
    Real.rpow X delta < 2 * Real.rpow X ((m : ℝ)⁻¹) := by
  have hpow := Real.rpow_lt_rpow_of_exponent_lt (by linarith : 1 < X) hdelta
  change Real.rpow X delta < Real.rpow X ((m : ℝ)⁻¹) at hpow
  have hrootPos : 0 < Real.rpow X ((m : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by linarith) _
  exact hpow.trans (by linarith)

/-- Exact source identity of the selected high beta factor. -/
theorem typeD_high_selected_is_log_or_zeta
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {k m : ℕ} (hmone : 1 ≤ m)
    (hdeltaM : delta < (m : ℝ)⁻¹)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((m : ℝ)⁻¹)) ≤ 2 * H₀)
    (hcut : 2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount
        ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) (k + 1))
    (j : Fin m)
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeD j) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    ∃ hs : s < factors.length,
      factors[s] = dynamicLogFactor X logIndex ∨
        ∃ zetaIndex, factors[s] = dynamicZetaFactor X zetaIndex := by
  dsimp only
  let factors := sortedComponentFactorList logIndex zbag mbag
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  obtain ⟨hs, hlarge⟩ := typeD_selected_gt_tailThreshold
    hX hdelta hmone hgeom logIndex zbag mbag j houtcome
  have hsmallLarge : Real.rpow X delta < (factors[s].length : ℝ) :=
    (tailThreshold_gt_smallScale hX hmone hdeltaM).trans hlarge
  have hmemSorted : factors[s] ∈ factors := List.getElem_mem hs
  have hperm := sortedComponentFactorList_perm logIndex zbag mbag
  have hmemOriginal : factors[s] ∈
      dynamicComponentFactorList logIndex zbag mbag := by
    exact (hperm.mem_iff).mp (by simpa [factors] using hmemSorted)
  unfold dynamicComponentFactorList at hmemOriginal
  simp only [List.mem_cons, List.mem_append] at hmemOriginal
  rcases hmemOriginal with hlog | hzeta | hmoebius
  · exact ⟨hs, Or.inl hlog⟩
  · obtain ⟨zetaIndex, hzetaEq⟩ :=
      mem_bagFactorList_exists (dynamicZetaFactor X) zbag hzeta
    exact ⟨hs, Or.inr ⟨zetaIndex, hzetaEq⟩⟩
  · obtain ⟨moebiusIndex, hmoebiusEq⟩ :=
      mem_bagFactorList_exists
        (dynamicMoebiusFactor X (hbOrder delta)) mbag hmoebius
    have hmoebiusSmall := dynamicMoebiusShellScale_le_rpow
      hX hdelta hcut moebiusIndex
    rw [hmoebiusEq] at hsmallLarge
    have hlarge' : Real.rpow X delta <
        (2 ^ (moebiusIndex : ℕ) : ℝ) := by
      simpa [dynamicMoebiusFactor] using hsmallLarge
    exact False.elim ((not_lt_of_ge hmoebiusSmall) hlarge')

end
end MRTLemma215DynamicHighProvenanceV3

#print axioms MRTLemma215DynamicHighProvenanceV3.typeD_selected_gt_tailThreshold
#print axioms MRTLemma215DynamicHighProvenanceV3.typeD_high_selected_is_log_or_zeta
