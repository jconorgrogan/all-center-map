import Mathlib

open scoped BigOperators
noncomputable section

namespace FordDiscretePairCount

def positiveRange (Q : ℕ) : Finset ℕ :=
  (Finset.range Q).filter (fun h => 0 < h)

lemma sum_shift_one (Q : ℕ) (c : ℕ → ℝ) :
    (∑ h ∈ Finset.range Q, c (h + 1)) =
      ∑ h ∈ positiveRange (Q + 1), c h := by
  unfold positiveRange
  apply Finset.sum_bij (fun h _ => h + 1)
  · intro h hh
    simp only [Finset.mem_range] at hh
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  · intro a ha b hb hab
    omega
  · intro h hh
    have hh' := Finset.mem_filter.mp hh
    have hhpos : 0 < h := hh'.2
    have hhlt : h < Q + 1 := Finset.mem_range.mp hh'.1
    refine ⟨h - 1, Finset.mem_range.mpr (by omega), ?_⟩
    change (h - 1) + 1 = h
    exact Nat.sub_add_cancel hhpos
  · intro h hh
    rfl

lemma sum_dist_right (Q : ℕ) (c : ℕ → ℝ) :
    (∑ a ∈ Finset.range Q, c (Nat.dist a Q)) =
      ∑ h ∈ Finset.range Q, c (h + 1) := by
  calc
    (∑ a ∈ Finset.range Q, c (Nat.dist a Q)) =
        ∑ a ∈ Finset.range Q, c (Q - a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      rw [Nat.dist_eq_sub_of_le (by omega : a ≤ Q)]
    _ = ∑ a ∈ Finset.range Q, c ((Q - 1 - a) + 1) := by
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      congr 2
      omega
    _ = ∑ h ∈ Finset.range Q, c (h + 1) :=
      Finset.sum_range_reflect (fun h : ℕ => c (h + 1)) Q

lemma sum_dist_left (Q : ℕ) (c : ℕ → ℝ) :
    (∑ b ∈ Finset.range Q, c (Nat.dist Q b)) =
      ∑ h ∈ Finset.range Q, c (h + 1) := by
  calc
    (∑ b ∈ Finset.range Q, c (Nat.dist Q b)) =
        ∑ b ∈ Finset.range Q, c (Q - b) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := Finset.mem_range.mp hb
      rw [Nat.dist_eq_sub_of_le_right (by omega : b ≤ Q)]
    _ = ∑ b ∈ Finset.range Q, c ((Q - 1 - b) + 1) := by
      apply Finset.sum_congr rfl
      intro b hb
      have hb' := Finset.mem_range.mp hb
      congr 2
      omega
    _ = ∑ h ∈ Finset.range Q, c (h + 1) :=
      Finset.sum_range_reflect (fun h : ℕ => c (h + 1)) Q

lemma pair_sum_succ (Q : ℕ) (c : ℕ → ℝ) :
    (∑ a ∈ Finset.range (Q + 1),
      ∑ b ∈ Finset.range (Q + 1), c (Nat.dist a b)) =
      (∑ a ∈ Finset.range Q,
        ∑ b ∈ Finset.range Q, c (Nat.dist a b)) +
        c 0 + 2 * (∑ h ∈ Finset.range Q, c (h + 1)) := by
  rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_range_succ]
  simp_rw [Finset.sum_add_distrib]
  simp only [Nat.dist_self]
  rw [sum_dist_right, sum_dist_left]
  ring

theorem pair_count_le
    (Q : ℕ) (c : ℕ → ℝ) (hc : ∀ h, 0 ≤ c h) :
    (∑ a ∈ Finset.range Q,
      ∑ b ∈ Finset.range Q, c (Nat.dist a b)) ≤
      (Q : ℝ) *
        (c 0 + 2 * (∑ h ∈ positiveRange Q, c h)) := by
  induction Q with
  | zero => simp
  | succ Q ih =>
      rw [pair_sum_succ]
      rw [sum_shift_one]
      have hmono :
          (∑ h ∈ positiveRange Q, c h) ≤
            ∑ h ∈ positiveRange (Q + 1), c h := by
        unfold positiveRange
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro h hh
          simp only [Finset.mem_filter, Finset.mem_range] at hh ⊢
          exact ⟨by omega, hh.2⟩
        · intro h hh hnot
          exact hc h
      have hA :
          (Q : ℝ) * (c 0 + 2 * (∑ h ∈ positiveRange Q, c h)) ≤
            (Q : ℝ) *
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)) := by
        gcongr
      calc
        (∑ a ∈ Finset.range Q,
            ∑ b ∈ Finset.range Q, c (Nat.dist a b)) +
            c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h) ≤
            (Q : ℝ) * (c 0 + 2 * (∑ h ∈ positiveRange Q, c h)) +
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right ih
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)))
        _ ≤ (Q : ℝ) *
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)) +
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)) := by
          simpa [add_comm, add_left_comm, add_assoc] using
            (add_le_add_right hA
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)))
        _ = ((Q + 1 : ℕ) : ℝ) *
              (c 0 + 2 * (∑ h ∈ positiveRange (Q + 1), c h)) := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring

end FordDiscretePairCount

#print axioms FordDiscretePairCount.pair_count_le
