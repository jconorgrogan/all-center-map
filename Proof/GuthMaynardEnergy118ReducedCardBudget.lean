import GuthMaynardEnergy118GCDReindex

open scoped BigOperators

namespace GuthMaynardEnergy118GCD

noncomputable section

/-! Reindexing a finite range of positive gcd parameters as a closed interval. -/
theorem sum_range_succ_eq_Icc
    {M : Type*} [AddCommMonoid M] (f : ℕ → M) (D : ℕ) :
    (∑ k ∈ Finset.range D, f (k + 1)) =
      ∑ d ∈ Finset.Icc 1 D, f d := by
  induction D with
  | zero => simp
  | succ D ih =>
      rw [Finset.sum_range_succ, ih]
      have hIcc : Finset.Icc 1 (D + 1) =
          insert (D + 1) (Finset.Icc 1 D) := by
        ext d
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc]
      have hnot : D + 1 ∉ Finset.Icc 1 D := by
        simp only [Finset.mem_Icc]
        omega
      rw [Finset.sum_insert hnot]
      simpa [add_comm]

private theorem card_reducedPairs_eq_gcdClass
    {N d : ℕ} (hd : 1 ≤ d) :
    (reducedPairs N d).card = (gcdClass N d).card := by
  rcases scalePair_bijective_gcdClass (N := N) (d := d) hd with
    ⟨hmap, hinj, hsurj⟩
  apply Finset.card_bij (fun p _ => scalePair d p)
  · intro p hp
    exact hmap p hp
  · intro p hp q hq heq
    exact hinj heq
  · intro p hp
    rcases hsurj p hp with ⟨q, hq, hscale⟩
    exact ⟨q, hq, hscale⟩

private theorem dyadicPair_gcd_mem_Icc_max
    {N D : ℕ} {p : Pair} (hp : p ∈ dyadicPairs N) :
    p.1.gcd p.2 ∈ Finset.Icc 1 (max D (2 * N)) := by
  rcases Finset.mem_product.mp hp with ⟨hm, hn⟩
  rcases Finset.mem_Ioc.mp hm with ⟨hmL, hmU⟩
  have hp2pos : 0 < p.2 := by
    have := Finset.mem_Ioc.mp hn
    omega
  have hgpos : 0 < p.1.gcd p.2 :=
    Nat.gcd_pos_of_pos_left p.2 (by omega)
  have hgU : p.1.gcd p.2 ≤ 2 * N :=
    (Nat.gcd_le_left p.2 (by omega)).trans hmU
  apply Finset.mem_Icc.mpr
  exact ⟨Nat.one_le_iff_ne_zero.mpr hgpos.ne',
    hgU.trans (Nat.le_max_right D (2 * N))⟩

private theorem gcdClass_card_sum_to_max_eq_dyadicPairs_card
    {N D : ℕ} :
    (∑ d ∈ Finset.Icc 1 (max D (2 * N)), (gcdClass N d).card) =
      (dyadicPairs N).card := by
  have hmap : ∀ p ∈ dyadicPairs N,
      p.1.gcd p.2 ∈ Finset.Icc 1 (max D (2 * N)) := by
    intro p hp
    exact dyadicPair_gcd_mem_Icc_max hp
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := dyadicPairs N)
    (t := Finset.Icc 1 (max D (2 * N)))
    hmap (fun _ : Pair => (1 : ℕ))
  have hcard (d : ℕ) :
      (gcdClass N d).card =
        ∑ p ∈ dyadicPairs N with p.1.gcd p.2 = d, (1 : ℕ) := by
    rw [gcdClass, Finset.card_eq_sum_ones]
  calc
    (∑ d ∈ Finset.Icc 1 (max D (2 * N)), (gcdClass N d).card) =
        ∑ d ∈ Finset.Icc 1 (max D (2 * N)),
          ∑ p ∈ dyadicPairs N with p.1.gcd p.2 = d, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hcard d
    _ = ∑ p ∈ dyadicPairs N, (1 : ℕ) := hfiber
    _ = (dyadicPairs N).card := (Finset.card_eq_sum_ones _).symm

theorem sum_reducedPairs_card_le_sq (N D : ℕ) :
    (∑ k ∈ Finset.range D, (reducedPairs N (k + 1)).card) ≤ N ^ 2 := by
  have hrange := sum_range_succ_eq_Icc
    (f := fun d => (reducedPairs N d).card) D
  rw [hrange]
  calc
    (∑ d ∈ Finset.Icc 1 D, (reducedPairs N d).card) =
        ∑ d ∈ Finset.Icc 1 D, (gcdClass N d).card := by
      apply Finset.sum_congr rfl
      intro d hd
      exact card_reducedPairs_eq_gcdClass (by
        exact Finset.mem_Icc.mp hd |>.1)
    _ ≤ ∑ d ∈ Finset.Icc 1 (max D (2 * N)), (gcdClass N d).card := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1,
          (Finset.mem_Icc.mp hd).2.trans (Nat.le_max_left D (2 * N))⟩
      · intro d hd hnot
        exact Nat.zero_le _
    _ = (dyadicPairs N).card :=
      gcdClass_card_sum_to_max_eq_dyadicPairs_card
    _ = N ^ 2 := by
      simp only [dyadicPairs, Finset.card_product, Nat.card_Ioc]
      have h : 2 * N - N = N := by omega
      simpa [h, pow_two]

end
end GuthMaynardEnergy118GCD

#print axioms GuthMaynardEnergy118GCD.sum_range_succ_eq_Icc
#print axioms GuthMaynardEnergy118GCD.sum_reducedPairs_card_le_sq
