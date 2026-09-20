import FordOffsetLogTransfer

open scoped BigOperators
noncomputable section

namespace FordOffsetMeanTransfer

open FordPolynomialPhase FordSourceWeakBilinear FordOffsetLogTransfer

/-- Cancels the positive bilinear cardinality after inserting a uniform scalar
bound for every offset polynomial source sum. -/
theorem offset_mean_transfer
    (M1 M2 N H k : ℕ) (t u Q : ℝ)
    (hM1 : 1 ≤ M1) (hM2 : 1 ≤ M2) (hN : 1 ≤ N)
    (ht : 0 ≤ t) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (hU : ∀ n ∈ Finset.range H,
      ‖∑ b : Fin M2, ∑ a : Fin M1,
        FordPolynomialPhase.e
          (∑ j : Fin k,
            sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
              (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
              (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖ ≤
        (M1 * M2 : ℝ) * Q) :
    ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
      2 * (M1 * M2 : ℝ) + (H : ℝ) * Q +
        (H : ℝ) *
          (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) := by
  let P : ℝ := (M1 * M2 : ℝ)
  have hP : 0 < P := by
    dsimp [P]
    positivity
  have htr := FordOffsetLogTransfer.offset_bilinear_shift_transfer
    M1 M2 N H k t u hN ht hu hu1
  have hsumU :
      (∑ n ∈ Finset.range H,
        ‖∑ b : Fin M2, ∑ a : Fin M1,
          FordPolynomialPhase.e
            (∑ j : Fin k,
              sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
                (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖) ≤
      ∑ n ∈ Finset.range H, P * Q := by
    apply Finset.sum_le_sum
    intro n hn
    simpa [P] using hU n hn
  have hsumU' :
      (∑ n ∈ Finset.range H,
        ‖∑ b : Fin M2, ∑ a : Fin M1,
          FordPolynomialPhase.e
            (∑ j : Fin k,
              sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
                (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖) ≤
      (H : ℝ) * (P * Q) := by
    calc
      _ ≤ ∑ n ∈ Finset.range H, P * Q := hsumU
      _ = (H : ℝ) * (P * Q) := by simp [nsmul_eq_mul]
  have hadd_actual :
      (M1 * M2 : ℝ) * (2 * ((M1 * M2 : ℕ) : ℝ)) +
          (∑ n ∈ Finset.range H,
            ‖∑ b : Fin M2, ∑ a : Fin M1,
              FordPolynomialPhase.e
                (∑ j : Fin k,
                  sourceGamma t (((N + n : ℕ) : ℝ) + u) j.val *
                    (((b.val + 1 : ℕ) : ℝ) ^ (j.val + 1)) *
                    (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))‖) +
          (M1 * M2 : ℝ) * (H : ℝ) *
            (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) ≤
        (M1 * M2 : ℝ) * (2 * ((M1 * M2 : ℕ) : ℝ)) +
          (H : ℝ) * (P * Q) +
          (M1 * M2 : ℝ) * (H : ℝ) *
            (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) := by
    convert (add_le_add_left
      (add_le_add_right hsumU' (P * (2 * P)))
      (P * (H : ℝ) *
        (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)))) using 1
    all_goals
      dsimp [P]
      norm_num [Nat.cast_mul]
  have htrActual := htr.trans hadd_actual
  have htr' :
      P * ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
        P * (2 * P) + (H : ℝ) * (P * Q) +
          P * (H : ℝ) *
            (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) := by
    convert htrActual using 1
    all_goals
      dsimp [P]
      norm_num [Nat.cast_mul]
  have hfactor :
      P * (2 * P) + (H : ℝ) * (P * Q) +
          P * (H : ℝ) *
            (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1)) =
        P * (2 * P + (H : ℝ) * Q +
          (H : ℝ) *
            (t * (((M1 * M2 : ℕ) : ℝ) / (N : ℝ)) ^ (k + 1) / (k + 1))) := by
    dsimp [P]
    norm_num [Nat.cast_mul]
    ring
  rw [hfactor] at htr'
  have hcancel := (le_of_mul_le_mul_left htr' hP)
  simpa [P] using hcancel

end FordOffsetMeanTransfer

#print axioms FordOffsetMeanTransfer.offset_mean_transfer
