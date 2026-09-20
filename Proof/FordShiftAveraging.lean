import Mathlib
open scoped BigOperators
noncomputable section
namespace FordShiftAveraging
lemma norm_range_sum_le (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (H : ℕ) :
    ‖∑ n ∈ Finset.range H, f n‖ ≤ (H : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Finset.range H, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range H, (1 : ℝ) := Finset.sum_le_sum (fun n _ => hf n)
    _ = _ := by simp

/-- Literal endpoint loss for a translated finite interval, with no disjointness assumption. -/
theorem shift_range_bound (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N H d : ℕ) :
    ‖(∑ n ∈ Finset.range H, f (N+n)) -
      ∑ n ∈ Finset.range H, f (N+n+d)‖ ≤ 2 * (d : ℝ) := by
  have h1 := Finset.sum_range_add (fun n => f (N+n)) H d
  have h2 := Finset.sum_range_add (fun n => f (N+n)) d H
  have hid : (∑ n ∈ Finset.range H, f (N+n)) -
      ∑ n ∈ Finset.range H, f (N+n+d) =
      (∑ n ∈ Finset.range d, f (N+n)) -
      ∑ n ∈ Finset.range d, f (N+H+n) := by
    simp only [Nat.add_assoc, Nat.add_comm d H] at h1 h2
    have he : (∑ n ∈ Finset.range H, f (N+n)) +
        (∑ n ∈ Finset.range d, f (N+H+n)) =
        (∑ n ∈ Finset.range d, f (N+n)) +
        (∑ n ∈ Finset.range H, f (N+n+d)) := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h1.symm.trans h2
    linear_combination he
  rw [hid]
  calc
    _ ≤ ‖∑ n ∈ Finset.range d, f (N+n)‖ +
        ‖∑ n ∈ Finset.range d, f (N+H+n)‖ := norm_sub_le _ _
    _ ≤ (d : ℝ) + d := add_le_add
      (norm_range_sum_le _ (fun n => hf _) _)
      (norm_range_sum_le _ (fun n => hf _) _)
    _ = _ := by ring
/-- Summed shift replacement error; division by the number of shifts is left explicit. -/
theorem summed_shift_bound {ι : Type*} (S : Finset ι) (shift : ι → ℕ)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) (N H D : ℕ)
    (hd : ∀ i ∈ S, shift i ≤ D) :
    ‖(S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n)) -
      ∑ i ∈ S, ∑ n ∈ Finset.range H, f (N+n+shift i)‖ ≤
      (S.card : ℝ) * (2 * (D : ℝ)) := by
  have heq : (S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n)) -
      ∑ i ∈ S, ∑ n ∈ Finset.range H, f (N+n+shift i) =
      ∑ i ∈ S, ((∑ n ∈ Finset.range H, f (N+n)) -
        ∑ n ∈ Finset.range H, f (N+n+shift i)) := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [heq]
  calc
    _ ≤ ∑ i ∈ S, ‖(∑ n ∈ Finset.range H, f (N+n)) -
        ∑ n ∈ Finset.range H, f (N+n+shift i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ S, 2 * (D : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (shift_range_bound f hf N H (shift i)).trans
      have hiR : (shift i : ℝ) ≤ D := by exact_mod_cast hd i hi
      linarith
    _ = _ := by simp [nsmul_eq_mul]

end FordShiftAveraging
#print axioms FordShiftAveraging.shift_range_bound
#print axioms FordShiftAveraging.summed_shift_bound
