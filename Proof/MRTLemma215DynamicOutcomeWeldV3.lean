import MRTLemma215DynamicFactorExtractionV3

/-!
# Total outcome weld for the dynamic MRT decomposition

This module turns the exact scale classifier into a statement about the
literal masked arithmetic component.  In particular, both branches labelled
`vanishing` by MRT Lemma 2.15 are proved to be zero: the all-small branch by
upper support and the `j >= m` branch by lower support.
-/

namespace MRTLemma215DynamicOutcomeWeldV3

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction
open MAPHBPerronSourceData MAPDynamicHBSourceV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215PreliminaryExpansion MRTLemma215DynamicPreliminaryV3
open MRTLemma215DynamicSupportV3 MRTLemma215DynamicFactorExtractionV3
open MRTLemma215ScaleClassifierV3

noncomputable section

def dynamicComponentOutcome
    {X : ℝ} {K k : ℕ} (m : ℕ) (delta H₀ : ℝ)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1)) :
    MRTScaleOutcome m :=
  classifyScaleList m
    (dynamicPreliminaryScaleList (some logIndex) zbag mbag)
    (Real.rpow X delta) H₀

/-- A `vanishing` classifier result is an actual pointwise zero statement,
not a discarded error term.  The two explicit numerical hypotheses are the
literal versions of `H₀ >= X^(1/m+delta)` and `X` sufficiently large in
MRT Lemma 2.15. -/
theorem maskedDynamicPreliminaryComponent_eq_zero_of_outcome_vanishing
    {X delta H₀ : ℝ} (hX : 2 ≤ X) (hdelta : 0 < delta)
    {K k m : ℕ} (hK : 1 ≤ K) (hmone : 1 ≤ m)
    (hgeom : Real.rpow X delta *
        (2 * Real.rpow X ((m : ℝ)⁻¹)) ≤ 2 * H₀)
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (hsize : (2 : ℝ) ^
        (dynamicComponentFactorList logIndex zbag mbag).length *
          Real.rpow X delta ≤ X)
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .vanishing)
    (n : ℕ) :
    (if n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊ then
      dynamicPreliminaryComponent (some logIndex) zbag mbag n else 0) = 0 := by
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  by_cases hs : s < scales.length
  · by_cases hII : scalePrefixProduct scales (s + 1) ≤ 2 * H₀
    · have htype : dynamicComponentOutcome m delta H₀
          logIndex zbag mbag = .typeII := by
        exact classifyScaleList_typeII
          (by simpa [s, scales] using hs)
          (by simpa [s, scales] using hII)
      rw [htype] at houtcome
      cases houtcome
    · by_cases hj : scales.length - s < m
      · have htype : dynamicComponentOutcome m delta H₀
            logIndex zbag mbag =
          .typeD ⟨scales.length - s, hj⟩ := by
          exact classifyScaleList_typeD
            (by simpa [s, scales] using hs)
            (by simpa [s, scales] using hII)
            (by simpa [s, scales] using hj)
        rw [htype] at houtcome
        cases houtcome
      · exact maskedDynamicPreliminaryComponent_eq_zero_of_largeTail
          hX hdelta hK hmone hgeom logIndex zbag mbag
          (by simpa [s, scales] using hs)
          (by
            have : 2 * H₀ < scalePrefixProduct scales (s + 1) :=
              lt_of_not_ge hII
            simpa [s, scales] using this)
          (by
            have : m ≤ scales.length - s := le_of_not_gt hj
            simpa [s, scales] using this)
          n
  · exact maskedDynamicPreliminaryComponent_eq_zero_of_allSmall
      hX hdelta hK logIndex zbag mbag hsize
      (by simpa [s, scales] using hs) n

/-- A Type-`d_j` outcome exposes the exact tail count and the two inequalities
used by the published regrouping. -/
theorem typeD_outcome_data
    {X delta H₀ : ℝ} {K k m : ℕ}
    (logIndex : Fin (sourceDyadicCount (hbFactorCutoff X)))
    (zbag : Sym (Option (Fin (sourceDyadicCount (hbFactorCutoff X)))) k)
    (mbag : Sym
      (Option (Fin (sourceDyadicCount ⌊dynamicHBCutoff X K⌋₊))) (k + 1))
    (j : Fin m)
    (houtcome : dynamicComponentOutcome m delta H₀ logIndex zbag mbag =
      .typeD j) :
    let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
    let s := largestSmallPrefix scales (Real.rpow X delta)
    s < scales.length ∧
      2 * H₀ < scalePrefixProduct scales (s + 1) ∧
      (j : ℕ) = scales.length - s ∧ 1 ≤ (j : ℕ) := by
  dsimp only
  let scales := dynamicPreliminaryScaleList (some logIndex) zbag mbag
  let s := largestSmallPrefix scales (Real.rpow X delta)
  by_cases hs : s < scales.length
  · by_cases hII : scalePrefixProduct scales (s + 1) ≤ 2 * H₀
    · have htype : dynamicComponentOutcome m delta H₀
          logIndex zbag mbag = .typeII := by
        exact classifyScaleList_typeII
          (by simpa [s, scales] using hs)
          (by simpa [s, scales] using hII)
      rw [htype] at houtcome
      cases houtcome
    · by_cases hj : scales.length - s < m
      · have htype : dynamicComponentOutcome m delta H₀
            logIndex zbag mbag =
          .typeD ⟨scales.length - s, hj⟩ := by
          exact classifyScaleList_typeD
            (by simpa [s, scales] using hs)
            (by simpa [s, scales] using hII)
            (by simpa [s, scales] using hj)
        have hfin : j = ⟨scales.length - s, hj⟩ := by
          simpa [htype] using houtcome.symm
        have hjval : (j : ℕ) = scales.length - s := by
          exact congrArg Fin.val hfin
        refine ⟨hs, lt_of_not_ge hII, hjval, ?_⟩
        rw [hjval]
        omega
      · have htype : dynamicComponentOutcome m delta H₀
            logIndex zbag mbag = .vanishing := by
          exact classifyScaleList_vanishing_of_largeTail
            (by simpa [s, scales] using hs)
            (by simpa [s, scales] using hII)
            (by simpa [s, scales] using hj)
        rw [htype] at houtcome
        cases houtcome
  · have htype : dynamicComponentOutcome m delta H₀
        logIndex zbag mbag = .vanishing := by
      exact classifyScaleList_vanishing_of_allSmall
        (by simpa [s, scales] using hs)
    rw [htype] at houtcome
    cases houtcome

end
end MRTLemma215DynamicOutcomeWeldV3

#print axioms MRTLemma215DynamicOutcomeWeldV3.maskedDynamicPreliminaryComponent_eq_zero_of_outcome_vanishing
#print axioms MRTLemma215DynamicOutcomeWeldV3.typeD_outcome_data
