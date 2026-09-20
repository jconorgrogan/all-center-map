import GuthMaynardLemma92ThreeScaleFrequencyInputs

/-!
# Source-scale localized-pair budget on region I

The first-Poisson cover has size `O(T^6)`, but using that complete cover in
the low-frequency Cauchy step loses the theorem.  On `|xi| ≤ a`, localization
itself forces `|ell| ≤ a/M₁ + B/M₃`.  This file retains that smaller
source window.
-/

open scoped Real

noncomputable section
namespace GuthMaynardJIteration

def sourceLowLocalizedPairBudget
    (N1 a M1 B M3 : ℝ) : ℝ :=
  N1 * (2 * (a / M1 + B / M3) + 3)

theorem card_sourceMediumLocalizedPairs_low_le_sourceBudget
    (m1Range ellRange : Finset ℤ) {M1 M3 : ℕ}
    (hM1 : 0 < M1) (hM3 : 0 < M3)
    (hm1Range : m1Range ⊆ sourceSignedDyadicRange M1)
    {a B N1 xi : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B)
    (hcard1 : (m1Range.card : ℝ) ≤ N1)
    (hxi : xi ∈ lowFrequencyRegion a) :
    ((sourceMediumLocalizedPairs m1Range ellRange (M3 : ℝ) B xi).card : ℝ) ≤
      sourceLowLocalizedPairBudget N1 a (M1 : ℝ) B (M3 : ℝ) := by
  have hM1R : 0 < (M1 : ℝ) := Nat.cast_pos.mpr hM1
  have hM3R : 0 < (M3 : ℝ) := Nat.cast_pos.mpr hM3
  let smallEll : Finset ℤ :=
    sourceIntegerWindow 0 (a / (M1 : ℝ) + B / (M3 : ℝ))
  have hsmall0 : 0 ≤ a / (M1 : ℝ) + B / (M3 : ℝ) := by positivity
  have hsubset : sourceMediumLocalizedPairs m1Range ellRange (M3 : ℝ) B xi ⊆
      m1Range ×ˢ smallEll := by
    intro p hp
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    refine Finset.mem_product.mpr ⟨hpdata.1, ?_⟩
    have hmBounds := sourceSignedDyadicRange_abs_bounds hM1
      (hm1Range hpdata.1)
    have hmpos : 0 < |(p.1 : ℝ)| := hM1R.trans_le hmBounds.1
    have hprod : |(p.1 : ℝ)| * |(p.2 : ℝ)| <
        a + (|(p.1 : ℝ)| / (M3 : ℝ)) * B := by
      calc
        |(p.1 : ℝ)| * |(p.2 : ℝ)| =
            |(p.1 : ℝ) * (p.2 : ℝ)| := (abs_mul _ _).symm
        _ = |xi - (xi - (p.1 : ℝ) * (p.2 : ℝ))| := by ring_nf
        _ ≤ |xi| + |xi - (p.1 : ℝ) * (p.2 : ℝ)| := abs_sub _ _
        _ < a + (|(p.1 : ℝ)| / (M3 : ℝ)) * B :=
          add_lt_add_of_le_of_lt hxi hpdata.2.2
    have hellDiv : |(p.2 : ℝ)| <
        (a + (|(p.1 : ℝ)| / (M3 : ℝ)) * B) / |(p.1 : ℝ)| :=
      (lt_div_iff₀ hmpos).2 (by simpa [mul_comm] using hprod)
    have hsplit :
        (a + (|(p.1 : ℝ)| / (M3 : ℝ)) * B) / |(p.1 : ℝ)| =
          a / |(p.1 : ℝ)| + B / (M3 : ℝ) := by
      field_simp [hM3R.ne', hmpos.ne']
    have hell : |(p.2 : ℝ)| <
        a / |(p.1 : ℝ)| + B / (M3 : ℝ) := by
      rw [← hsplit]
      exact hellDiv
    have hfirst : a / |(p.1 : ℝ)| ≤ a / (M1 : ℝ) :=
      div_le_div_of_nonneg_left ha hM1R hmBounds.1
    dsimp only [smallEll]
    apply mem_sourceIntegerWindow_zero_of_abs_le
    exact hell.le.trans (add_le_add hfirst le_rfl)
  have hcardNat := Finset.card_le_card hsubset
  have hcardProduct :
      ((sourceMediumLocalizedPairs m1Range ellRange (M3 : ℝ) B xi).card : ℝ) ≤
        (m1Range.card : ℝ) * (smallEll.card : ℝ) := by
    have hcardNat' :
        (sourceMediumLocalizedPairs m1Range ellRange (M3 : ℝ) B xi).card ≤
          m1Range.card * smallEll.card := by
      simpa only [Finset.card_product] using hcardNat
    exact_mod_cast hcardNat'
  have hsmallCard : (smallEll.card : ℝ) ≤
      2 * (a / (M1 : ℝ) + B / (M3 : ℝ)) + 3 := by
    dsimp only [smallEll]
    exact card_sourceIntegerWindow_cast_le 0 _ hsmall0
  have hN10 : 0 ≤ N1 := (Nat.cast_nonneg m1Range.card).trans hcard1
  calc
    ((sourceMediumLocalizedPairs m1Range ellRange (M3 : ℝ) B xi).card : ℝ) ≤
        (m1Range.card : ℝ) * (smallEll.card : ℝ) := hcardProduct
    _ ≤ N1 * (2 * (a / (M1 : ℝ) + B / (M3 : ℝ)) + 3) :=
      mul_le_mul hcard1 hsmallCard (Nat.cast_nonneg _) hN10
    _ = sourceLowLocalizedPairBudget N1 a (M1 : ℝ) B (M3 : ℝ) := rfl

#print axioms GuthMaynardJIteration.card_sourceMediumLocalizedPairs_low_le_sourceBudget

end GuthMaynardJIteration
