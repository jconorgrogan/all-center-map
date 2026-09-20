import MRTDynamicD12LiteralMass

/-! Elimination of the active D12 classifier into the literal one-shell or
two-shell witness required by the per-bag moment ledger. -/
namespace MRTDynamicD12ActiveTailWitnesses

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPMRTCorollary53Source MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215DynamicRegroupingV3 MRTLemma215ScaleClassifierV3
open MRTLemma215DynamicClassificationV3 MRTLemma215DynamicOutcomeWeldV3
open MRTDynamicD12FactorExtraction MRTDynamicD12LiteralMass
open MRTLemma215DynamicHighProvenanceV3

noncomputable section
set_option maxHeartbeats 1200000

theorem exists_active_d12_tail_witnesses
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    (hdelta8 : delta < (8 : ℝ)⁻¹)
    (hgeom : Real.rpow X delta *
      (2 * Real.rpow X ((8 : ℝ)⁻¹)) ≤ 2 * H₀)
    (hcut : 2 ≤ ⌊dynamicHBCutoff X (hbOrder delta)⌋₊)
    {k : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym (Option (Fin
      (sourceDyadicCount ⌊dynamicHBCutoff X (hbOrder delta)⌋₊))) (k + 1))
    (hactive : dynamicD12IsActive delta H₀ logIndex zbag mbag) :
    let factors := sortedComponentFactorList logIndex zbag mbag
    let s := largestSmallPrefix
      (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
      (Real.rpow X delta)
    (∃ beta : NatDyadicFactor,
      factors.drop s = [beta] ∧
      IsSourceSmoothFactor X logIndex beta ∧ 2 ≤ beta.length) ∨
    (∃ beta gamma : NatDyadicFactor,
      factors.drop s = [beta, gamma] ∧
      IsSourceSmoothFactor X logIndex beta ∧ 2 ≤ beta.length ∧
      IsSourceSmoothFactor X logIndex gamma ∧ 2 ≤ gamma.length) := by
  let factors := sortedComponentFactorList logIndex zbag mbag
  let s := largestSmallPrefix
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow X delta)
  have hspec := activeD12_tail_spec (X := X) (delta := delta) (H₀ := H₀)
    hX hdelta hdelta8 hgeom hcut logIndex zbag mbag hactive
  dsimp only [factors, s] at hspec ⊢
  rcases hspec with ⟨hlen, hsmooth, hprefix⟩
  obtain ⟨j, hout, hj⟩ := hactive
  obtain ⟨hs, hlarge⟩ := typeD_selected_gt_tailThreshold
    (X := X) (delta := delta) (H₀ := H₀) (K := hbOrder delta)
    (k := k) (m := 8) hX hdelta (by norm_num) hgeom logIndex zbag mbag j hout
  have hroot : 1 ≤ Real.rpow X ((8 : ℝ)⁻¹) := by
    apply Real.one_le_rpow
    · linarith
    · norm_num
  have hsel2 : 2 ≤ (sortedComponentFactorList logIndex zbag mbag)[
      largestSmallPrefix
        (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
        (Real.rpow X delta)].length := by
    have hlt := hlarge
    have htwo : (2 : ℝ) ≤ 2 * Real.rpow X ((8 : ℝ)⁻¹) := by nlinarith
    have hlt2 : (2 : ℝ) <
        ((sortedComponentFactorList logIndex zbag mbag)[
          largestSmallPrefix
            (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
            (Real.rpow X delta)].length : ℝ) := htwo.trans_lt hlt
    exact_mod_cast hlt2.le
  have hfactor2 : ∀ f ∈
      (sortedComponentFactorList logIndex zbag mbag).drop
        (largestSmallPrefix
          (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
          (Real.rpow X delta)),
      2 ≤ f.length := by
    intro f hf
    have hle := selected_le_of_mem_drop
      (sortedComponentFactorList_pairwise logIndex zbag mbag) hs hf
    exact hsel2.trans hle
  rcases hlen with hlen | hlen
  · obtain ⟨beta, hbeta⟩ := List.length_eq_one_iff.mp hlen
    left
    refine ⟨beta, hbeta, ?_, ?_⟩
    · exact hsmooth beta (by rw [hbeta]; simp)
    · exact hfactor2 beta (by rw [hbeta]; simp)
  · obtain ⟨beta, tail, hcons⟩ :=
      List.exists_cons_of_length_eq_add_one (n := 1) hlen
    have htailLen : tail.length = 1 := by
      rw [hcons] at hlen
      simpa using hlen
    obtain ⟨gamma, hgamma⟩ := List.length_eq_one_iff.mp htailLen
    have htail :
        (sortedComponentFactorList logIndex zbag mbag).drop
            (largestSmallPrefix
              (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
              (Real.rpow X delta)) = [beta, gamma] := by
      rw [hcons, hgamma]
    right
    refine ⟨beta, gamma, htail, ?_, ?_, ?_, ?_⟩
    · exact hsmooth beta (by rw [htail]; simp)
    · exact hfactor2 beta (by rw [htail]; simp)
    · exact hsmooth gamma (by rw [htail]; simp)
    · exact hfactor2 gamma (by rw [htail]; simp)

end
end MRTDynamicD12ActiveTailWitnesses

#print axioms MRTDynamicD12ActiveTailWitnesses.exists_active_d12_tail_witnesses
