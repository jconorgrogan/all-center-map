import GuthMaynardJIterationMediumRegionTailInsertion

open scoped BigOperators Real
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! Exact geometry and factor-count input from source TeX 1585. -/

theorem mediumFrequencyRegion_subset_Icc
    {a b : ℝ} :
    mediumFrequencyRegion a b ⊆ Set.Icc (-b) b := by
  intro xi hxi
  exact (abs_le.mp hxi.2)

theorem volume_mediumFrequencyRegion_ne_top
    {a b : ℝ} :
    volume (mediumFrequencyRegion a b) ≠ (⊤ : ENNReal) := by
  have htop : volume (Set.Icc (-b) b) < (⊤ : ENNReal) := measure_Icc_lt_top
  apply ne_top_of_le_ne_top htop.ne
  exact measure_mono mediumFrequencyRegion_subset_Icc

theorem volumeReal_mediumFrequencyRegion_le
    {a b : ℝ} (hb : 0 ≤ b) :
    volume.real (mediumFrequencyRegion a b) ≤ 2 * b := by
  calc
    volume.real (mediumFrequencyRegion a b) ≤ volume.real (Set.Icc (-b) b) :=
      measureReal_mono mediumFrequencyRegion_subset_Icc
        (show volume (Set.Icc (-b) b) ≠ (⊤ : ENNReal) from
          measure_Icc_lt_top.ne)
    _ = 2 * b := by
      rw [measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ b - (-b))]
      ring

/-- The medium cutoff supplies the uniform normalized phase bound needed by
the certified first-Poisson tail. -/
theorem abs_div_le_of_mem_mediumFrequencyRegion
    {a b M1 : ℝ} (hM1 : 0 < M1) {xi : ℝ}
    (hxi : xi ∈ mediumFrequencyRegion a b) {m1 : ℤ}
    (hm1 : M1 ≤ |(m1 : ℝ)|) :
    |xi / (m1 : ℝ)| ≤ b / M1 := by
  have hm1pos : 0 < |(m1 : ℝ)| := lt_of_lt_of_le hM1 hm1
  rw [abs_div]
  exact div_le_div₀ (le_trans (abs_nonneg _) hxi.2) hxi.2 hM1 hm1

/-- On region II, a localized product `s=m1*ell` cannot vanish once the
lower frequency cutoff exceeds the largest localization radius.  This is the
literal nonzero assertion in source TeX 1585. -/
theorem localizedProduct_ne_zero_on_medium
    {m1Range ellRange : Finset ℤ} {M3 B a b W : ℝ}
    (hW : ∀ m1 ∈ m1Range, (|(m1 : ℝ)| / M3) * B ≤ W)
    (hWa : W < a) {xi : ℝ}
    (hxi : xi ∈ mediumFrequencyRegion a b)
    {p : ℤ × ℤ}
    (hp : p ∈ sourceMediumLocalizedPairs m1Range ellRange M3 B xi) :
    p.1 * p.2 ≠ 0 := by
  intro hzero
  have hpdata := mem_sourceMediumLocalizedPairs_iff.mp hp
  have hlocal := hpdata.2.2
  have hradius := hW p.1 hpdata.1
  have hprodR : (p.1 : ℝ) * (p.2 : ℝ) = 0 := by exact_mod_cast hzero
  rw [hprodR, sub_zero] at hlocal
  linarith [hxi.1]

/-- The first coordinate embeds each nonzero product fiber into the signed
divisors of that product. -/
theorem card_sourceMediumProductFiber_le_signedDivisors
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ} {s : ℤ}
    (hs : s ≠ 0) :
    (sourceMediumProductFiber m1Range ellRange M3 B xi s).card ≤
      (m1Range.filter fun m1 => m1 ∣ s).card := by
  apply Finset.card_le_card_of_injOn (fun p : ℤ × ℤ => p.1)
  · intro p hp
    have hpD : p ∈ sourceMediumProductFiber m1Range ellRange M3 B xi s := hp
    unfold sourceMediumProductFiber at hpD
    have hpdata := Finset.mem_filter.mp hpD
    have hplocal := mem_sourceMediumLocalizedPairs_iff.mp hpdata.1
    change p.1 ∈ m1Range.filter fun m1 => m1 ∣ s
    rw [Finset.mem_filter]
    exact ⟨hplocal.1, ⟨p.2, hpdata.2.symm⟩⟩
  · intro p hp q hq hpq
    have hpD : p ∈ sourceMediumProductFiber m1Range ellRange M3 B xi s := hp
    have hqD : q ∈ sourceMediumProductFiber m1Range ellRange M3 B xi s := hq
    unfold sourceMediumProductFiber at hpD hqD
    have hpdata := Finset.mem_filter.mp hpD
    have hqdata := Finset.mem_filter.mp hqD
    have hpq' : p.1 = q.1 := hpq
    apply Prod.ext hpq'
    have hp10 : p.1 ≠ 0 := by
      intro hp10
      apply hs
      rw [← hpdata.2, hp10]
      simp
    apply mul_left_cancel₀ hp10
    calc
      p.1 * p.2 = s := hpdata.2
      _ = q.1 * q.2 := hqdata.2.symm
      _ = p.1 * q.2 := by rw [hpq']

/-- Uniform product-fiber count with the exact signed-divisor constant `2`.
This consumes the preceding injection and the already-certified divisor
count, rather than postulating a factorization loss. -/
theorem card_sourceMediumProductFiber_le_two_mul_divisors
    {m1Range ellRange : Finset ℤ} {M3 B xi : ℝ} {s : ℤ}
    (hs : s ≠ 0) :
    (sourceMediumProductFiber m1Range ellRange M3 B xi s).card ≤
      2 * s.natAbs.divisors.card := by
  exact (card_sourceMediumProductFiber_le_signedDivisors hs).trans
    (card_signed_divisors_le_two_mul_card_divisors hs
      (m1Range.filter fun m1 => m1 ∣ s) (fun d hd =>
        (Finset.mem_filter.mp hd).2))

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.volumeReal_mediumFrequencyRegion_le
#print axioms GuthMaynardJIteration.abs_div_le_of_mem_mediumFrequencyRegion
#print axioms GuthMaynardJIteration.localizedProduct_ne_zero_on_medium
#print axioms GuthMaynardJIteration.card_sourceMediumProductFiber_le_signedDivisors
#print axioms GuthMaynardJIteration.card_sourceMediumProductFiber_le_two_mul_divisors
