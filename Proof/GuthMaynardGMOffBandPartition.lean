import GuthMaynardGMPointwiseHighTPartition

namespace GuthMaynardGMOffBandPartition
open GuthMaynardGMPointwiseHighTPartition
noncomputable section

def gmOffBand (N : ℕ) (t δ : ℝ) (ell : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ioc N (2 * N)).filter (fun n =>
    2 * Real.pi * ell + δ < gmIncrement t n ∧
    gmIncrement t n < 2 * Real.pi * (ell + 1) - δ)

theorem offBand_not_resonant {x δ : ℝ} {ell : ℤ} (hδ : 0 < δ)
    (hlo : 2 * Real.pi * ell + δ < x)
    (hhi : x < 2 * Real.pi * (ell + 1) - δ) :
    ¬ ∃ k : ℤ, |x - 2 * Real.pi * k| ≤ δ := by
  rintro ⟨k, hk⟩
  obtain ⟨hklo, hkhi⟩ := abs_le.mp hk
  by_cases hke : k ≤ ell
  · have hkr : (k : ℝ) ≤ ell := by exact_mod_cast hke
    nlinarith [Real.pi_pos]
  · have hkr : (ell : ℝ) + 1 ≤ k := by exact_mod_cast (show ell + 1 ≤ k by omega)
    nlinarith [Real.pi_pos]

theorem exists_offBand_of_not_resonant {x δ : ℝ} (hδ : 0 < δ)
    (h : ¬ ∃ k : ℤ, |x - 2 * Real.pi * k| ≤ δ) :
    ∃ ell : ℤ, 2 * Real.pi * ell + δ < x ∧
      x < 2 * Real.pi * (ell + 1) - δ := by
  let ell : ℤ := Int.floor (x / (2 * Real.pi))
  have hp : 0 < 2 * Real.pi := by positivity
  have hl : 2 * Real.pi * ell ≤ x := by
    have hh := (le_div_iff₀ hp).mp (Int.floor_le (x / (2 * Real.pi)))
    dsimp [ell]; nlinarith
  have hu : x < 2 * Real.pi * (ell + 1) := by
    have hh := (div_lt_iff₀ hp).mp (Int.lt_floor_add_one (x / (2 * Real.pi)))
    dsimp [ell]; nlinarith
  refine ⟨ell, ?_, ?_⟩
  · have hh : δ < |x - 2 * Real.pi * ell| := lt_of_not_ge (fun he => h ⟨ell, he⟩)
    rw [abs_of_nonneg (by linarith)] at hh
    linarith
  · have hh : δ < |x - 2 * Real.pi * ((ell + 1 : ℤ) : ℝ)| :=
      lt_of_not_ge (fun he => h ⟨ell + 1, he⟩)
    push_cast at hh
    rw [abs_of_nonpos (by linarith)] at hh
    linarith

theorem offBand_unique {x δ : ℝ} (hδ : 0 < δ) {a b : ℤ}
    (ha : 2 * Real.pi * a + δ < x ∧ x < 2 * Real.pi * (a + 1) - δ)
    (hb : 2 * Real.pi * b + δ < x ∧ x < 2 * Real.pi * (b + 1) - δ) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · have habR : (a : ℝ) + 1 ≤ b := by exact_mod_cast (show a + 1 ≤ b by omega)
    nlinarith [Real.pi_pos]
  · have hbaR : (b : ℝ) + 1 ≤ a := by exact_mod_cast (show b + 1 ≤ a by omega)
    nlinarith [Real.pi_pos]


theorem offBand_label_mem {N : ℕ} {t δ : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) (hδ : 0 < δ) {ell : ℤ} {n : ℕ}
    (hn : n ∈ gmOffBand N t δ ell) : ell ∈ gmBandLabels N t := by
  classical
  obtain ⟨hnI, hlo, hhi⟩ := Finset.mem_filter.mp hn
  obtain ⟨hNn, hnN⟩ := Finset.mem_Ioc.mp hnI
  have hx0 := gmIncrement_pos ht (by omega : 0 < n)
  have hxhi := gmIncrement_le_t_div_N hN hNn.le ht.le
  have hell0 : 0 ≤ ell := by
    by_contra hh
    have he : (ell : ℝ) + 1 ≤ 0 := by exact_mod_cast (show ell + 1 ≤ 0 by omega)
    nlinarith [Real.pi_pos]
  have hellR : (0 : ℝ) ≤ ell := by exact_mod_cast hell0
  have hbound : (ell : ℝ) ≤ t / N + 1 := by nlinarith [Real.pi_gt_three]
  have hc := Nat.le_ceil (t / (N : ℝ) + 1)
  rw [gmBandLabels, Finset.mem_Icc]
  constructor
  · omega
  · have hh : (ell : ℝ) ≤ (Nat.ceil (t / (N : ℝ) + 1) : ℝ) := hbound.trans hc
    exact_mod_cast hh

theorem gmOffResonant_eq_biUnion {N : ℕ} {t δ : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) (hδ : 0 < δ) :
    gmOffResonant N t δ = (gmBandLabels N t).biUnion (gmOffBand N t δ) := by
  classical
  ext n
  constructor
  · intro hn
    obtain ⟨hnI, hnot⟩ := Finset.mem_filter.mp hn
    obtain ⟨ell, hlo, hhi⟩ := exists_offBand_of_not_resonant hδ hnot
    have hm : n ∈ gmOffBand N t δ ell := Finset.mem_filter.mpr ⟨hnI, hlo, hhi⟩
    exact Finset.mem_biUnion.mpr ⟨ell, offBand_label_mem hN ht hδ hm, hm⟩
  · intro hn
    obtain ⟨ell, hell, hn⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨hnI, hlo, hhi⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnI, offBand_not_resonant hδ hlo hhi⟩

theorem gmOffBand_disjoint {N : ℕ} {t δ : ℝ} (hδ : 0 < δ)
    {a b : ℤ} (hab : a ≠ b) :
    Disjoint (gmOffBand N t δ a) (gmOffBand N t δ b) := by
  classical
  rw [Finset.disjoint_left]
  intro n ha hb
  exact hab (offBand_unique hδ (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2)

end
end GuthMaynardGMOffBandPartition
#print axioms GuthMaynardGMOffBandPartition.exists_offBand_of_not_resonant
#print axioms GuthMaynardGMOffBandPartition.gmOffResonant_eq_biUnion
#print axioms GuthMaynardGMOffBandPartition.gmOffBand_disjoint
