import GuthMaynardLemma92ThreeScaleEllRange

/-!
# Three-scale first-Poisson covers on the low and medium regions

The source split uses the same first-Poisson cover on regions I and II.  This
file proves that fact without identifying the first-Poisson scale `M₁`, the
later detector scale `M₂`, or the affine scale `M₃`.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

/-- Any low-frequency point below the literal `T^6` transition is covered by
the independent-scale first-Poisson ell range. -/
theorem mem_sourceLemma92ThreeScaleEllRange_of_lowFrequency_localized
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B a xi : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (ha : a ≤ T ^ 6) (hxi : xi ∈ lowFrequencyRegion a)
    {m1 ell : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hell : |xi - (m1 : ℝ) * (ell : ℝ)| <
      (|(m1 : ℝ)| / (M3 : ℝ)) * B) :
    ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  apply mem_sourceLemma92ThreeScaleEllRange_of_localized
    hM1 hM3 hT hB hm1 (hxi.trans ha) hell

/-- Region-I cover in the exact functional shape consumed by the first-Poisson
retained-sum identity. -/
theorem sourceLemma92ThreeScale_lowFrequency_cover
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B a : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (ha : a ≤ T ^ 6) :
    ∀ xi ∈ lowFrequencyRegion a,
      ∀ m1 ∈ sourceSignedDyadicRange M1, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  intro xi hxi m1 hm1 ell hell
  exact mem_sourceLemma92ThreeScaleEllRange_of_lowFrequency_localized
    hM1 hM3 hT hB ha hxi hm1 hell

/-- The same region-I cover for any selected source range contained in the
signed dyadic universe. -/
theorem sourceLemma92ThreeScale_lowFrequency_cover_of_subset
    {m1Range : Finset ℤ} {M1 M3 : ℕ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    (hm1Range : m1Range ⊆ sourceSignedDyadicRange M1)
    {T B a : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (ha : a ≤ T ^ 6) :
    ∀ xi ∈ lowFrequencyRegion a,
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  intro xi hxi m1 hm1 ell hell
  exact mem_sourceLemma92ThreeScaleEllRange_of_lowFrequency_localized
    hM1 hM3 hT hB ha hxi (hm1Range hm1) hell

/-- Every point in the literal region-II interval already satisfies the
`T^6` frequency hypothesis required by the three-scale ell cover. -/
theorem mem_sourceLemma92ThreeScaleEllRange_of_mediumFrequency_localized
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B a xi : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hxi : xi ∈ mediumFrequencyRegion a (sourceHighFrequencyCutoff T))
    {m1 ell : ℤ} (hm1 : m1 ∈ sourceSignedDyadicRange M1)
    (hell : |xi - (m1 : ℝ) * (ell : ℝ)| <
      (|(m1 : ℝ)| / (M3 : ℝ)) * B) :
    ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  apply mem_sourceLemma92ThreeScaleEllRange_of_localized
    hM1 hM3 hT hB hm1
  · simpa only [sourceHighFrequencyCutoff] using hxi.2
  · exact hell

/-- Region-II cover in the exact functional shape consumed by the
first-Poisson retained-sum identity. -/
theorem sourceLemma92ThreeScale_mediumFrequency_cover
    {M1 M3 : ℕ} (hM1 : 0 < M1) (hM3 : 0 < M3)
    {T B a : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∀ xi ∈ mediumFrequencyRegion a (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ sourceSignedDyadicRange M1, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  intro xi hxi m1 hm1 ell hell
  exact mem_sourceLemma92ThreeScaleEllRange_of_mediumFrequency_localized
    hM1 hM3 hT hB hxi hm1 hell

/-- The same region-II cover for any selected source range contained in the
signed dyadic universe. -/
theorem sourceLemma92ThreeScale_mediumFrequency_cover_of_subset
    {m1Range : Finset ℤ} {M1 M3 : ℕ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    (hm1Range : m1Range ⊆ sourceSignedDyadicRange M1)
    {T B a : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B) :
    ∀ xi ∈ mediumFrequencyRegion a (sourceHighFrequencyCutoff T),
      ∀ m1 ∈ m1Range, ∀ ell : ℤ,
        |xi - (m1 : ℝ) * (ell : ℝ)| <
            (|(m1 : ℝ)| / (M3 : ℝ)) * B →
          ell ∈ sourceLemma92ThreeScaleEllRange M1 M3 T B := by
  intro xi hxi m1 hm1 ell hell
  exact mem_sourceLemma92ThreeScaleEllRange_of_mediumFrequency_localized
    hM1 hM3 hT hB hxi (hm1Range hm1) hell

#print axioms GuthMaynardJIteration.mem_sourceLemma92ThreeScaleEllRange_of_lowFrequency_localized
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScale_lowFrequency_cover
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScale_lowFrequency_cover_of_subset
#print axioms GuthMaynardJIteration.mem_sourceLemma92ThreeScaleEllRange_of_mediumFrequency_localized
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScale_mediumFrequency_cover
#print axioms GuthMaynardJIteration.sourceLemma92ThreeScale_mediumFrequency_cover_of_subset

end GuthMaynardJIteration
