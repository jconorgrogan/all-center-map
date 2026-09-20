import GuthMaynardEnergy118GCDCutoff

open scoped BigOperators
noncomputable section
namespace GuthMaynardEnergy119GCDCutoff
open GuthMaynardEnergy118GCD

/-- Exact complementary high-gcd partition, including cutoffs above 2N. -/
theorem dyadic_high_gcd_eq_sum_reduced
    (e : ℕ) (W : Finset ℝ) (N D : ℕ) :
    (∑ p ∈ (dyadicPairs N).filter (fun p => D < p.1.gcd p.2),
      ratioMomentTermPow e W p) =
      ∑ d ∈ Finset.Icc (D+1) (2*N),
        ∑ p ∈ reducedPairs N d, ratioMomentTermPow e W p := by
  let S := (dyadicPairs N).filter (fun p => D < p.1.gcd p.2)
  let f := ratioMomentTermPow e W
  have hmap : ∀ p ∈ S, p.1.gcd p.2 ∈ Finset.Icc (D+1) (2*N) := by
    intro p hp
    obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
    obtain ⟨hm,hn⟩ := Finset.mem_product.mp hp
    obtain ⟨hmlo,hmhi⟩ := Finset.mem_Ioc.mp hm
    have hg := Nat.gcd_le_left p.2 (by omega : 0 < p.1)
    exact Finset.mem_Icc.mpr ⟨by omega,hg.trans hmhi⟩
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := S) (t := Finset.Icc (D+1) (2*N)) hmap f
  calc
    _ = ∑ d ∈ Finset.Icc (D+1) (2*N),
        ∑ p ∈ S with p.1.gcd p.2 = d, f p := hfiber.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdlo := (Finset.mem_Icc.mp hd).1
      have hfilter : S.filter (fun p => p.1.gcd p.2 = d) = gcdClass N d := by
        ext p
        simp only [S,gcdClass,Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp,hcut⟩,heq⟩
          exact ⟨hp,heq⟩
        · rintro ⟨hp,heq⟩
          exact ⟨⟨hp,by omega⟩,heq⟩
      rw [hfilter]
      exact ratioKernelMomentPow_gcdClass_eq_reduced e W (by omega)

theorem dyadic_cubic_split_small_high (W : Finset ℝ) (N D : ℕ) :
    (∑ p ∈ dyadicPairs N, ratioMomentTermPow 3 W p) =
      (∑ p ∈ (dyadicPairs N).filter (fun p => p.1.gcd p.2 ≤ D),
        ratioMomentTermPow 3 W p)+
      (∑ p ∈ (dyadicPairs N).filter (fun p => D < p.1.gcd p.2),
        ratioMomentTermPow 3 W p) := by
  have hh := Finset.sum_filter_add_sum_filter_not (dyadicPairs N)
    (fun p => p.1.gcd p.2 ≤ D) (ratioMomentTermPow 3 W)
  simpa only [not_le] using hh.symm

/-- Above twice the time length the strict high-gcd carrier is empty. This
allows logarithmic factors to be absorbed in T without assuming N ≤ T. -/
theorem high_gcd_empty_of_two_time_le {N : ℕ} {T : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hNT : 2*T ≤ (N : ℝ)) :
    (dyadicPairs N).filter (fun p => (N : ℝ)^2/T < (p.1.gcd p.2 : ℝ)) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hp,hcut⟩ := Finset.mem_filter.mp hp
  obtain ⟨hm,hn⟩ := Finset.mem_product.mp hp
  obtain ⟨hmlo,hmhi⟩ := Finset.mem_Ioc.mp hm
  have hg : p.1.gcd p.2 ≤ 2*N :=
    (Nat.gcd_le_left p.2 (by omega)).trans hmhi
  have hgR : (p.1.gcd p.2 : ℝ) ≤ 2*(N : ℝ) := by exact_mod_cast hg
  have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hprod := mul_le_mul_of_nonneg_right hNT hN0
  have hquot : 2*(N : ℝ) ≤ (N : ℝ)^2/T := by
    apply (le_div_iff₀ hT).mpr
    nlinarith
  exact (not_lt_of_ge (hgR.trans hquot)) hcut

end GuthMaynardEnergy119GCDCutoff
#print axioms GuthMaynardEnergy119GCDCutoff.dyadic_high_gcd_eq_sum_reduced
#print axioms GuthMaynardEnergy119GCDCutoff.dyadic_cubic_split_small_high
#print axioms GuthMaynardEnergy119GCDCutoff.high_gcd_empty_of_two_time_le
