import FordShiftAveraging
open scoped BigOperators
noncomputable section
namespace FordShiftApproximation
/-- Finite shift transfer with every approximation error and cardinality retained. -/
theorem transfer {ι : Type*} (S : Finset ι) (shift : ι → ℕ)
    (f : ℕ → ℂ) (g : ℕ → ι → ℂ) (N H D : ℕ) (E : ℝ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hd : ∀ i ∈ S, shift i ≤ D)
    (he : ∀ n ∈ Finset.range H, ∀ i ∈ S, ‖f (N+n+shift i) - g n i‖ ≤ E) :
    (S.card : ℝ) * ‖∑ n ∈ Finset.range H, f (N+n)‖ ≤
      (S.card : ℝ) * (2 * (D : ℝ)) +
      (∑ n ∈ Finset.range H, ‖∑ i ∈ S, g n i‖) +
      (S.card : ℝ) * (H : ℝ) * E := by
  let A : ℂ := ∑ i ∈ S, ∑ n ∈ Finset.range H, f (N+n+shift i)
  let G : ℂ := ∑ i ∈ S, ∑ n ∈ Finset.range H, g n i
  have herr : ‖A-G‖ ≤ (S.card : ℝ) * (H : ℝ) * E := by
    dsimp [A, G]
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i ∈ S, ‖(∑ n ∈ Finset.range H, f (N+n+shift i)) -
          ∑ n ∈ Finset.range H, g n i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ S, (H : ℝ) * E := by
        apply Finset.sum_le_sum
        intro i hi
        rw [← Finset.sum_sub_distrib]
        calc
          _ ≤ ∑ n ∈ Finset.range H, ‖f (N+n+shift i)-g n i‖ := norm_sum_le _ _
          _ ≤ ∑ _n ∈ Finset.range H, E := Finset.sum_le_sum (fun n hn => he n hn i hi)
          _ = _ := by simp [nsmul_eq_mul]
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  have hG : ‖G‖ ≤ ∑ n ∈ Finset.range H, ‖∑ i ∈ S, g n i‖ := by
    dsimp [G]
    rw [Finset.sum_comm]
    exact norm_sum_le _ _
  have hshift := FordShiftAveraging.summed_shift_bound S shift f hf N H D hd
  have hid : (S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n)) =
      ((S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n))-A) + (A-G) + G := by ring
  calc
    _ = ‖(S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n))‖ := by simp [norm_mul]
    _ ≤ ‖(S.card : ℂ) * (∑ n ∈ Finset.range H, f (N+n))-A‖ + ‖A-G‖ + ‖G‖ := by
      conv_lhs => rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (S.card : ℝ) * (2 * (D : ℝ)) + (S.card : ℝ) * (H : ℝ) * E +
        (∑ n ∈ Finset.range H, ‖∑ i ∈ S, g n i‖) :=
      add_le_add (add_le_add hshift herr) hG
    _ = _ := by ring
end FordShiftApproximation
#print axioms FordShiftApproximation.transfer
