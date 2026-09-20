import GuthMaynardEnergy118ReducedCardBudget

open scoped BigOperators

namespace GuthMaynardEnergy118GCD

noncomputable section

/-- Exact small-gcd cutoff identity.  The left side keeps the literal dyadic
rectangle and its gcd mask; the right side uses primitive reduced pairs and
the same unscaled ratio-kernel moment. -/
theorem dyadicRatioKernelMomentPow_cutoff_eq_sum_reduced
    (e : ℕ) (W : Finset ℝ) {N D : ℕ} (hN : 1 ≤ N) :
    (∑ p ∈ (dyadicPairs N).filter (fun p => p.1.gcd p.2 ≤ D),
      ratioMomentTermPow e W p) =
      ∑ j ∈ Finset.range D,
        ∑ p ∈ reducedPairs N (j + 1), ratioMomentTermPow e W p := by
  let S : Finset Pair :=
    (dyadicPairs N).filter (fun p => p.1.gcd p.2 ≤ D)
  let f : Pair → ℝ := ratioMomentTermPow e W
  have hmap : ∀ p ∈ S,
      p.1.gcd p.2 ∈ Finset.Icc 1 D := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpDyadic, hpCutoff⟩
    rcases Finset.mem_product.mp hpDyadic with ⟨hm, hn⟩
    have hmPos : 0 < p.1 := by
      rcases Finset.mem_Ioc.mp hm with ⟨hmL, _⟩
      omega
    have hnPos : 0 < p.2 := by
      rcases Finset.mem_Ioc.mp hn with ⟨hnL, _⟩
      omega
    have hgPos : 0 < p.1.gcd p.2 :=
      Nat.gcd_pos_of_pos_left p.2 hmPos
    exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hgPos.ne', hpCutoff⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.Icc 1 D) hmap f
  have hinner (d : ℕ) (hd : d ∈ Finset.Icc 1 D) :
      (∑ p ∈ S with p.1.gcd p.2 = d, f p) =
        ∑ p ∈ gcdClass N d, f p := by
    have hfilter :
        S.filter (fun p => p.1.gcd p.2 = d) = gcdClass N d := by
      ext p
      rcases Finset.mem_Icc.mp hd with ⟨hd1, hdD⟩
      simp only [S, gcdClass, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hpDyadic, hpCutoff⟩, hEq⟩
        exact ⟨hpDyadic, hEq⟩
      · rintro ⟨hpDyadic, hEq⟩
        exact ⟨⟨hpDyadic, by simpa [hEq] using hdD⟩, hEq⟩
    rw [hfilter]
  calc
    (∑ p ∈ (dyadicPairs N).filter
        (fun p => p.1.gcd p.2 ≤ D), ratioMomentTermPow e W p) =
        ∑ p ∈ S, f p := by rfl
    _ = ∑ d ∈ Finset.Icc 1 D,
          ∑ p ∈ S with p.1.gcd p.2 = d, f p := hfiber.symm
    _ = ∑ d ∈ Finset.Icc 1 D, ∑ p ∈ gcdClass N d, f p := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hinner d hd
    _ = ∑ d ∈ Finset.Icc 1 D,
          ∑ p ∈ reducedPairs N d, f p := by
      apply Finset.sum_congr rfl
      intro d hd
      exact ratioKernelMomentPow_gcdClass_eq_reduced e W
        (Finset.mem_Icc.mp hd |>.1)
    _ = ∑ j ∈ Finset.range D,
          ∑ p ∈ reducedPairs N (j + 1), ratioMomentTermPow e W p := by
      symm
      exact sum_range_succ_eq_Icc
        (f := fun d => ∑ p ∈ reducedPairs N d, f p) D

end
end GuthMaynardEnergy118GCD

#print axioms GuthMaynardEnergy118GCD.dyadicRatioKernelMomentPow_cutoff_eq_sum_reduced
