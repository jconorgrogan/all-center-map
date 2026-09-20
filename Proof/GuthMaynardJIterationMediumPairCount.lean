import GuthMaynardJIterationMediumRegionGeometry

open scoped BigOperators Real

noncomputable section
namespace GuthMaynardJIteration

/-! Uniform conversion of the exact integer window and divisor estimates into
the source's localized-pair loss parameter. -/

/-- Source TeX 1585 with every loss exposed.  The exact product window has at
most `Nwindow` integers; signed-factor multiplicity is supplied by the proved
subpower divisor bound. -/
theorem exists_sourceMediumLocalizedPairCard_subpower
    (m1Range ellRange : Finset ℤ)
    {M3 B a b W Nwindow eta : ℝ}
    (heta : 0 < eta) (hb : 0 ≤ b) (hW0 : 0 ≤ W) (hWa : W < a)
    (hradius : ∀ m1 ∈ m1Range, (|(m1 : ℝ)| / M3) * B ≤ W)
    (hwindowCount : ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceIntegerWindow xi W).card : ℝ) ≤ Nwindow) :
    ∃ C : ℝ, 0 < C ∧ ∀ xi ∈ mediumFrequencyRegion a b,
      ((sourceMediumLocalizedPairs m1Range ellRange M3 B xi).card : ℝ) ≤
        Nwindow * C * Real.rpow (b + W) eta := by
  obtain ⟨C, hC, hdiv⟩ := card_signed_divisors_subpolynomial eta heta
  refine ⟨C, hC, ?_⟩
  intro xi hxi
  have hlocalWindow : ∀ p ∈
      sourceMediumLocalizedPairs m1Range ellRange M3 B xi,
      |xi - (((p.1 * p.2 : ℤ) : ℝ))| < W := by
    intro p hp
    have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
    simpa only [Int.cast_mul] using
      hpdata.2.2.trans_le (hradius p.1 hpdata.1)
  have hproducts :
      ((sourceMediumLocalizedProducts m1Range ellRange M3 B xi).card : ℝ) ≤
        Nwindow := by
    have hnat := card_sourceMediumLocalizedProducts_le_integerWindow
      hlocalWindow
    have hreal :
        ((sourceMediumLocalizedProducts m1Range ellRange M3 B xi).card : ℝ) ≤
          ((sourceIntegerWindow xi W).card : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans (hwindowCount xi hxi)
  have hfiber : ∀ s ∈ sourceMediumLocalizedProducts
      m1Range ellRange M3 B xi,
      ((sourceMediumProductFiber m1Range ellRange M3 B xi s).card : ℝ) ≤
        C * Real.rpow (b + W) eta := by
    intro s hs
    unfold sourceMediumLocalizedProducts at hs
    rw [Finset.mem_image] at hs
    obtain ⟨p, hp, rfl⟩ := hs
    have hprod0 := localizedProduct_ne_zero_on_medium
      hradius hWa hxi hp
    let D : Finset ℤ := m1Range.filter fun m1 => m1 ∣ p.1 * p.2
    have hcardFiberNat :
        (sourceMediumProductFiber m1Range ellRange M3 B xi
          (p.1 * p.2)).card ≤ D.card :=
      card_sourceMediumProductFiber_le_signedDivisors hprod0
    have hcardFiber :
        ((sourceMediumProductFiber m1Range ellRange M3 B xi
          (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := by
      exact_mod_cast hcardFiberNat
    have hD : (D.card : ℝ) ≤
        C * Real.rpow (p.1 * p.2).natAbs eta := by
      exact hdiv (p.1 * p.2) D hprod0 (fun d hd =>
        (Finset.mem_filter.mp hd).2)
    have habsProduct : |(((p.1 * p.2 : ℤ) : ℝ))| ≤ b + W := by
      have htriangle : |(((p.1 * p.2 : ℤ) : ℝ))| ≤
          |xi| + |xi - (((p.1 * p.2 : ℤ) : ℝ))| := by
        calc
          |(((p.1 * p.2 : ℤ) : ℝ))| =
              |xi - (xi - (((p.1 * p.2 : ℤ) : ℝ)))| := by ring_nf
          _ ≤ _ := abs_sub _ _
      linarith [hlocalWindow p hp, hxi.2]
    have hrpow : Real.rpow (p.1 * p.2).natAbs eta ≤
        Real.rpow (b + W) eta := by
      apply Real.rpow_le_rpow
      · positivity
      · simpa only [Nat.cast_natAbs, Int.cast_abs] using habsProduct
      · exact heta.le
    calc
      ((sourceMediumProductFiber m1Range ellRange M3 B xi
          (p.1 * p.2)).card : ℝ) ≤ (D.card : ℝ) := hcardFiber
      _ ≤ C * Real.rpow (p.1 * p.2).natAbs eta := hD
      _ ≤ C * Real.rpow (b + W) eta :=
        mul_le_mul_of_nonneg_left hrpow hC.le
  rw [card_sourceMediumLocalizedPairs_eq_sum_fibers]
  push_cast
  calc
    (∑ s ∈ sourceMediumLocalizedProducts m1Range ellRange M3 B xi,
        ((sourceMediumProductFiber m1Range ellRange M3 B xi s).card : ℝ)) ≤
      ∑ _s ∈ sourceMediumLocalizedProducts m1Range ellRange M3 B xi,
        C * Real.rpow (b + W) eta := by
          apply Finset.sum_le_sum
          intro s hs
          exact hfiber s hs
    _ = ((sourceMediumLocalizedProducts m1Range ellRange M3 B xi).card : ℝ) *
        (C * Real.rpow (b + W) eta) := by simp
    _ ≤ Nwindow * (C * Real.rpow (b + W) eta) := by
      exact mul_le_mul_of_nonneg_right hproducts
        (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
    _ = Nwindow * C * Real.rpow (b + W) eta := by ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.exists_sourceMediumLocalizedPairCard_subpower
