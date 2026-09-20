import GuthMaynardLemma92ThreeScaleRegionCover

/-!
# Literal three-scale inputs for the whole-frequency Lemma 9.2 theorem

This module packages the exact first-Poisson cover and low-frequency pair
cardinality in the shapes consumed by the corrected region-I/II assembly.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-- The localized pair set is a filtered subset of the selected first-Poisson
range times the literal three-scale ell cover. -/
theorem card_sourceMediumLocalizedPairs_threeScale_le
    (m1Range : Finset ℤ) {M1 M3 : ℕ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B N1 : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B) (hBT : B ≤ T ^ 6)
    (hcard1 : (m1Range.card : ℝ) ≤ N1) (xi : ℝ) :
    ((sourceMediumLocalizedPairs m1Range
      (sourceLemma92ThreeScaleEllRange M1 M3 T B)
      (M3 : ℝ) B xi).card : ℝ) ≤ N1 * (7 * T ^ 6) := by
  have hfilter := Finset.card_filter_le
    (m1Range ×ˢ sourceLemma92ThreeScaleEllRange M1 M3 T B)
    (fun p : ℤ × ℤ =>
      |xi - (p.1 : ℝ) * (p.2 : ℝ)| <
        (|(p.1 : ℝ)| / (M3 : ℝ)) * B)
  have hpair :
      ((sourceMediumLocalizedPairs m1Range
        (sourceLemma92ThreeScaleEllRange M1 M3 T B)
        (M3 : ℝ) B xi).card : ℝ) ≤
      (m1Range.card : ℝ) *
        ((sourceLemma92ThreeScaleEllRange M1 M3 T B).card : ℝ) := by
    unfold sourceMediumLocalizedPairs
    have hfilterReal :
        (({p ∈ m1Range ×ˢ sourceLemma92ThreeScaleEllRange M1 M3 T B |
          |xi - (p.1 : ℝ) * (p.2 : ℝ)| <
            (|(p.1 : ℝ)| / (M3 : ℝ)) * B}.card : ℕ) : ℝ) ≤
          (((m1Range ×ˢ sourceLemma92ThreeScaleEllRange M1 M3 T B).card : ℕ) : ℝ) := by
      exact_mod_cast hfilter
    simpa only [Finset.card_product, Nat.cast_mul] using hfilterReal
  have hell := card_sourceLemma92ThreeScaleEllRange_cast_le_seven_time_six
    hM1 hM3 hT hB hBT
  have hN1 : 0 ≤ N1 := (Nat.cast_nonneg m1Range.card).trans hcard1
  exact hpair.trans
    (mul_le_mul hcard1 hell (Nat.cast_nonneg _) hN1)

/-- The three first-Poisson inputs which no longer need to be repeated at the
whole-frequency consumer: region-I pair count, region-I cover, and region-II
cover.  The source scales remain independent. -/
theorem sourceLemma92ThreeScale_frequency_inputs
    (m1Range : Finset ℤ) {M1 M3 : ℕ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    (hm1Range : m1Range ⊆ sourceSignedDyadicRange M1)
    {T B N1 a : ℝ} (hT : 1 ≤ T) (hB : 0 ≤ B)
    (hBT : B ≤ T ^ 6) (ha : a ≤ T ^ 6)
    (hcard1 : (m1Range.card : ℝ) ≤ N1) :
    (∀ xi ∈ lowFrequencyRegion a,
      ((sourceMediumLocalizedPairs m1Range
        (sourceLemma92ThreeScaleEllRange M1 M3 T B)
        (M3 : ℝ) B xi).card : ℝ) ≤ N1 * (7 * T ^ 6)) ∧
    (∀ xi ∈ lowFrequencyRegion a,
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B) ∧
    (∀ xi ∈ mediumFrequencyRegion a (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  refine ⟨?_, ?_, ?_⟩
  · intro xi _hxi
    exact card_sourceMediumLocalizedPairs_threeScale_le
      m1Range hM1 hM3 hT hB hBT hcard1 xi
  · exact sourceLemma92ThreeScale_lowFrequency_cover_of_subset
      hM1 hM3 hm1Range hT0 hB ha
  · exact sourceLemma92ThreeScale_mediumFrequency_cover_of_subset
      hM1 hM3 hm1Range hT0 hB

#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_threeScale_le
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScale_frequency_inputs

end GuthMaynardJIteration
