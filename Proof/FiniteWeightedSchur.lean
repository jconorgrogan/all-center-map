import Mathlib

/-!
# A finite weighted Schur reduction

This is the algebraic heart of the signed pair-energy route.  It converts a
double quadratic form into one weighted square mass using a row-sum bound.
-/

namespace MAPPaperWindowVKBypass

open scoped BigOperators

/-- Finite weighted Schur test for a symmetric nonnegative kernel. -/
theorem finite_weighted_schur
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (m w : ι → ℝ) (K : ι → ι → ℝ) (H : ℝ)
    (hm : ∀ i ∈ S, 0 ≤ m i)
    (hK : ∀ i ∈ S, ∀ j ∈ S, 0 ≤ K i j)
    (hsymm : ∀ i ∈ S, ∀ j ∈ S, K i j = K j i)
    (hrow : ∀ i ∈ S, ∑ j ∈ S, m j * K i j ≤ H) :
    (∑ i ∈ S, ∑ j ∈ S,
        m i * m j * w i * w j * K i j) ≤
      H * ∑ i ∈ S, m i * (w i) ^ 2 := by
  let E : ℝ := ∑ i ∈ S, ∑ j ∈ S,
    m i * m j * w i * w j * K i j
  let M : ℝ := ∑ i ∈ S, m i * (w i) ^ 2
  have hpoint : ∀ i ∈ S, ∀ j ∈ S,
      2 * (m i * m j * w i * w j * K i j) ≤
        (m i * m j * K i j) * ((w i) ^ 2 + (w j) ^ 2) := by
    intro i hi j hj
    have hab : 2 * w i * w j ≤ (w i) ^ 2 + (w j) ^ 2 := by
      nlinarith [sq_nonneg (w i - w j)]
    have hbase : 0 ≤ m i * m j * K i j := by
      exact mul_nonneg (mul_nonneg (hm i hi) (hm j hj)) (hK i hi j hj)
    have hmul := mul_le_mul_of_nonneg_left hab hbase
    nlinarith
  have htwice : 2 * E ≤ 2 * H * M := by
    have hsum :
        2 * E ≤ ∑ i ∈ S, ∑ j ∈ S,
          (m i * m j * K i j) * ((w i) ^ 2 + (w j) ^ 2) := by
      dsimp [E]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      simpa [mul_assoc] using hpoint i hi j hj
    calc
      2 * E ≤ ∑ i ∈ S, ∑ j ∈ S,
          (m i * m j * K i j) * ((w i) ^ 2 + (w j) ^ 2) := hsum
      _ = 2 * ∑ i ∈ S,
          (m i * (w i) ^ 2) * (∑ j ∈ S, m j * K i j) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
        have hfirst :
            (∑ i ∈ S, ∑ j ∈ S,
              m i * m j * K i j * (w i) ^ 2) =
              ∑ i ∈ S, (m i * (w i) ^ 2) *
                (∑ j ∈ S, m j * K i j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        have hsecond :
            (∑ i ∈ S, ∑ j ∈ S,
              m i * m j * K i j * (w j) ^ 2) =
              ∑ i ∈ S, (m i * (w i) ^ 2) *
                (∑ j ∈ S, m j * K i j) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          rw [hsymm j hj i hi]
          ring
        rw [hfirst, hsecond]
        ring
      _ ≤ 2 * ∑ i ∈ S, (m i * (w i) ^ 2) * H := by
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (hrow i hi)
            (mul_nonneg (hm i hi) (sq_nonneg _))
        · norm_num
      _ = 2 * H * M := by
        dsimp [M]
        rw [← Finset.sum_mul]
        ring
  dsimp [E, M] at htwice ⊢
  nlinarith

end MAPPaperWindowVKBypass

#print axioms MAPPaperWindowVKBypass.finite_weighted_schur
