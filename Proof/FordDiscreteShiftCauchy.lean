import FordDiscreteShiftIdentity
import FordDiscreteCauchy

open scoped BigOperators ComplexConjugate
noncomputable section

namespace FordDiscreteShiftCauchy

open FordDiscreteShiftIdentity

/-- The finite differencing identity followed by Cauchy--Schwarz, with the
resulting norm squares expanded as ordered correlations. -/
theorem norm_sum_range_sq_le_shift_correlation
    {N Q : ℕ} (hQ : 1 ≤ Q) (f : ℕ → ℂ) :
    (Q : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, f n‖ ^ 2 ≤
      ((N + Q - 1 : ℕ) : ℝ) *
        ∑ r ∈ Finset.range (N + Q - 1),
          Complex.re (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
            zeroExtend N f ((r : ℤ) - a) *
              star (zeroExtend N f ((r : ℤ) - b))) := by
  let A : ℕ → ℂ := fun r =>
    ∑ h ∈ Finset.range Q, zeroExtend N f ((r : ℤ) - h)
  let S : ℂ := ∑ n ∈ Finset.range N, f n
  let L : ℕ := N + Q - 1
  have hshift : (Q : ℂ) * S = ∑ r ∈ Finset.range L, A r := by
    dsimp [S, A, L]
    exact sum_shift_identity hQ f
  have hnorm : ‖(Q : ℂ) * S‖ ^ 2 =
      ‖∑ r ∈ Finset.range L, A r‖ ^ 2 := by
    rw [hshift]
  have hqnorm : ‖(Q : ℂ) * S‖ ^ 2 = (Q : ℝ) ^ 2 * ‖S‖ ^ 2 := by
    rw [norm_mul]
    norm_num
    ring
  have hc : ‖∑ r ∈ Finset.range L, A r‖ ^ 2 ≤
      (L : ℝ) * ∑ r ∈ Finset.range L, ‖A r‖ ^ 2 :=
    FordDiscreteCauchy.norm_sum_range_sq_le_card_mul_sum_norm_sq L A
  have hexpand : ∑ r ∈ Finset.range L, ‖A r‖ ^ 2 =
      ∑ r ∈ Finset.range L,
        Complex.re (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
          zeroExtend N f ((r : ℤ) - a) *
            star (zeroExtend N f ((r : ℤ) - b))) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact FordDiscreteCauchy.norm_sum_range_sq_eq_real_double_correlation Q
      (fun h => zeroExtend N f ((r : ℤ) - h))
  have hc' : ‖∑ r ∈ Finset.range L, A r‖ ^ 2 ≤
      (L : ℝ) * ∑ r ∈ Finset.range L,
        Complex.re (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
          zeroExtend N f ((r : ℤ) - a) *
            star (zeroExtend N f ((r : ℤ) - b))) := by
    rw [← hexpand]
    exact hc
  calc
    (Q : ℝ) ^ 2 * ‖∑ n ∈ Finset.range N, f n‖ ^ 2 =
        ‖∑ r ∈ Finset.range L, A r‖ ^ 2 := by
      rw [← hqnorm, hnorm]
    _ ≤ (L : ℝ) * ∑ r ∈ Finset.range L,
        Complex.re (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
          zeroExtend N f ((r : ℤ) - a) *
            star (zeroExtend N f ((r : ℤ) - b))) := hc'
    _ = ((N + Q - 1 : ℕ) : ℝ) *
        ∑ r ∈ Finset.range (N + Q - 1),
          Complex.re (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
            zeroExtend N f ((r : ℤ) - a) *
              star (zeroExtend N f ((r : ℤ) - b))) := by
      rfl

end FordDiscreteShiftCauchy

#print axioms FordDiscreteShiftCauchy.norm_sum_range_sq_le_shift_correlation
