import Mathlib

open scoped BigOperators
noncomputable section
namespace FordOffsetDyadicPartition

/-- The block beginning at `2^j`, truncated at the cutoff `M`. -/
def offsetDyadicBlock (z : ℕ → ℂ) (M j : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (min M (2 * (2 ^ j)) - 2 ^ j), z (2 ^ j + i)

theorem offsetDyadicBlock_length_le (z : ℕ → ℂ) (M j : ℕ) :
    min M (2 * (2 ^ j)) - 2 ^ j ≤ 2 ^ j := by
  have hmin : min M (2 * (2 ^ j)) ≤ 2 * (2 ^ j) :=
    min_le_right _ _
  omega

theorem offsetDyadicBlock_eq_full
    (z : ℕ → ℂ) {M j : ℕ} (hfull : 2 * (2 ^ j) ≤ M) :
    offsetDyadicBlock z M j =
      ∑ i ∈ Finset.range (2 ^ j), z (2 ^ j + i) := by
  rw [offsetDyadicBlock, min_eq_right hfull]
  have hsub : 2 * (2 ^ j) - 2 ^ j = 2 ^ j := by omega
  rw [hsub]

theorem offsetDyadicBlock_eq_truncated_last
    (z : ℕ → ℂ) {M j : ℕ}
    (hlower : 2 ^ j ≤ M) (hupper : M ≤ 2 * (2 ^ j)) :
    offsetDyadicBlock z M j =
      ∑ i ∈ Finset.range (M - 2 ^ j), z (2 ^ j + i) := by
  rw [offsetDyadicBlock, min_eq_left hupper]

theorem offsetDyadicBlock_eq_full_range
    (z : ℕ → ℂ) {M j : ℕ} (hfull : 2 * (2 ^ j) ≤ M) :
    offsetDyadicBlock z M j =
      ∑ i ∈ Finset.range (2 ^ j), z (2 ^ j + i) :=
  offsetDyadicBlock_eq_full z hfull

/-- Exact partition of `z(1) + ... + z(M-1)` into dyadic blocks.
The final block is retained in truncated form, and blocks above the cutoff
are empty. -/
theorem sum_range_sub_one_eq_sum_offsetDyadicBlock
    (z : ℕ → ℂ) {M r : ℕ} (hM : 1 ≤ M) (hMr : M ≤ 2 ^ r) :
    ∑ i ∈ Finset.range (M - 1), z (i + 1) =
      ∑ j ∈ Finset.range r, offsetDyadicBlock z M j := by
  induction r generalizing M with
  | zero =>
      have hMr' : M ≤ 1 := by simpa using hMr
      have hMeq : M = 1 := by omega
      subst M
      simp [offsetDyadicBlock]
  | succ r ihr =>
      let N : ℕ := 2 ^ r
      have hpow : 2 ^ (r + 1) = N + N := by
        dsimp [N]
        rw [pow_succ]
        omega
      rw [hpow] at hMr
      by_cases hMN : M ≤ N
      · have hprev := ihr hM hMN
        rw [hprev, Finset.sum_range_succ]
        have hmin : min M (2 * (2 ^ r)) = M := by
          apply min_eq_left
          dsimp [N] at hMN
          omega
        have hempty : min M (2 * (2 ^ r)) - 2 ^ r = 0 := by
          rw [hmin]
          dsimp [N] at hMN
          omega
        simp [offsetDyadicBlock, hempty]
      · have hNM : N ≤ M := Nat.le_of_lt (Nat.lt_of_not_ge hMN)
        have hMsplit : (N - 1) + (M - N) = M - 1 := by omega
        have hNone : 1 ≤ N := by
          apply Nat.one_le_iff_ne_zero.mpr
          dsimp [N]
          positivity
        have hprev := ihr hNone (le_rfl : N ≤ 2 ^ r)
        have hblocksEq :
            ∑ j ∈ Finset.range r, offsetDyadicBlock z N j =
              ∑ j ∈ Finset.range r, offsetDyadicBlock z M j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjr : j < r := Finset.mem_range.mp hj
          have hjone : j + 1 ≤ r := by omega
          have hupperN : 2 * (2 ^ j) ≤ N := by
            dsimp [N]
            rw [show 2 * 2 ^ j = 2 ^ (j + 1) by ring]
            exact Nat.pow_le_pow_right (by norm_num) hjone
          rw [offsetDyadicBlock_eq_full z hupperN,
            offsetDyadicBlock_eq_full z (hupperN.trans hNM)]
        have hsumSplit :
            ∑ i ∈ Finset.range (M - 1), z (i + 1) =
              (∑ i ∈ Finset.range (N - 1), z (i + 1)) +
                ∑ i ∈ Finset.range (M - N), z (N + i) := by
          calc
            ∑ i ∈ Finset.range (M - 1), z (i + 1) =
                ∑ i ∈ Finset.range ((N - 1) + (M - N)), z (i + 1) := by
                  rw [hMsplit]
            _ = (∑ i ∈ Finset.range (N - 1), z (i + 1)) +
                ∑ i ∈ Finset.range (M - N), z ((N - 1) + i + 1) := by
              rw [Finset.sum_range_add]
            _ = (∑ i ∈ Finset.range (N - 1), z (i + 1)) +
                ∑ i ∈ Finset.range (M - N), z (N + i) := by
              congr 2
              funext i
              congr 1
              omega
        rw [hsumSplit, hprev, hblocksEq, Finset.sum_range_succ]
        have hmin : min M (2 * (2 ^ r)) = M := by
          apply min_eq_left
          dsimp [N] at hMr
          omega
        rw [offsetDyadicBlock, hmin]

theorem norm_sum_range_sub_one_le_sum_block_norm
    (z : ℕ → ℂ) {M r : ℕ} (hM : 1 ≤ M) (hMr : M ≤ 2 ^ r) :
    ‖∑ i ∈ Finset.range (M - 1), z (i + 1)‖ ≤
      ∑ j ∈ Finset.range r, ‖offsetDyadicBlock z M j‖ := by
  rw [sum_range_sub_one_eq_sum_offsetDyadicBlock z hM hMr]
  exact norm_sum_le _ _

theorem norm_sum_range_sub_one_le_sum_block_bounds
    (z : ℕ → ℂ) {M r : ℕ} (hM : 1 ≤ M) (hMr : M ≤ 2 ^ r)
    (C : ℕ → ℝ)
    (hC : ∀ j, j < r → ‖offsetDyadicBlock z M j‖ ≤ C j) :
    ‖∑ i ∈ Finset.range (M - 1), z (i + 1)‖ ≤
      ∑ j ∈ Finset.range r, C j := by
  calc
    ‖∑ i ∈ Finset.range (M - 1), z (i + 1)‖ ≤
        ∑ j ∈ Finset.range r, ‖offsetDyadicBlock z M j‖ :=
      norm_sum_range_sub_one_le_sum_block_norm z hM hMr
    _ ≤ ∑ j ∈ Finset.range r, C j := by
      apply Finset.sum_le_sum
      intro j hj
      exact hC j (Finset.mem_range.mp hj)

theorem norm_sum_range_M1_le_sum_block_bounds
    (z : ℕ → ℂ) {M1 r : ℕ} (hM1 : M1 + 1 ≤ 2 ^ r)
    (C : ℕ → ℝ)
    (hC : ∀ j, j < r →
      ‖offsetDyadicBlock z (M1 + 1) j‖ ≤ C j) :
    ‖∑ i ∈ Finset.range M1, z (i + 1)‖ ≤
      ∑ j ∈ Finset.range r, C j := by
  have hM : 1 ≤ M1 + 1 := by omega
  simpa using norm_sum_range_sub_one_le_sum_block_bounds
    z hM hM1 C hC

end FordOffsetDyadicPartition

#print axioms FordOffsetDyadicPartition.offsetDyadicBlock_length_le
#print axioms FordOffsetDyadicPartition.offsetDyadicBlock_eq_full
#print axioms FordOffsetDyadicPartition.offsetDyadicBlock_eq_truncated_last
#print axioms FordOffsetDyadicPartition.offsetDyadicBlock_eq_full_range
#print axioms FordOffsetDyadicPartition.sum_range_sub_one_eq_sum_offsetDyadicBlock
#print axioms FordOffsetDyadicPartition.norm_sum_range_sub_one_le_sum_block_norm
#print axioms FordOffsetDyadicPartition.norm_sum_range_sub_one_le_sum_block_bounds
#print axioms FordOffsetDyadicPartition.norm_sum_range_M1_le_sum_block_bounds
