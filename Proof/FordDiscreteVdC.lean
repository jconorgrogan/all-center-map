import FordDiscreteShiftCauchy
import FordDiscreteCorrelationNorm
import FordDiscreteCorrelationDiagonal
import FordDiscretePairCount

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordDiscreteVdC
open FordDiscreteShiftIdentity FordDiscreteCorrelationDiagonal FordDiscretePairCount

/-- Literal finite van der Corput inequality before division by the positive
shift count. All off-diagonal correlations and exact support lengths remain. -/
theorem weighted_vdc {N Q : ℕ} (hQ : 1 ≤ Q) (f : ℕ → ℂ)
    (hf : ∀ n ∈ Finset.range N, ‖f n‖ ≤ 1) :
    (Q : ℝ)^2 * ‖∑ n ∈ Finset.range N, f n‖^2 ≤
      ((N+Q-1 : ℕ) : ℝ) * (Q : ℝ) *
        ((N : ℝ) + 2 * ∑ h ∈ positiveRange Q, ‖correlation N h f‖) := by
  let L := N+Q-1
  let F : ℕ → ℕ → ℕ → ℂ := fun r a b =>
    zeroExtend N f ((r : ℤ)-a) * conj (zeroExtend N f ((r : ℤ)-b))
  have hreorder :
      (∑ r ∈ Finset.range L, Complex.re
        (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q, F r a b)) =
      ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
        Complex.re (∑ r ∈ Finset.range L, F r a b) := by
    simp only [Complex.re_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_comm]
  have hpair :
      (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
        Complex.re (∑ r ∈ Finset.range L, F r a b)) ≤
      ∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q,
        ‖correlation N (Nat.dist a b) f‖ := by
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.sum_le_sum
    intro b hb
    have hn := FordDiscreteCorrelationNorm.correlation_norm_eq
      (N := N) hQ (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) f
    have hr := FordDiscreteCorrelationNorm.correlation_real_le_norm
      (N := N) hQ (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) f
    simpa only [L, F, correlation, hn] using hr
  have hcount := pair_count_le Q (fun h => ‖correlation N h f‖) (fun h => norm_nonneg _)
  have hdiag := diagonal_norm_le f hf
  have htot :
      (∑ r ∈ Finset.range L, Complex.re
        (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q, F r a b)) ≤
      (Q : ℝ) * ((N : ℝ) + 2 * ∑ h ∈ positiveRange Q, ‖correlation N h f‖) := by
    rw [hreorder]
    exact hpair.trans (hcount.trans (mul_le_mul_of_nonneg_left
      (add_le_add hdiag le_rfl) (Nat.cast_nonneg Q)))
  have hshift := FordDiscreteShiftCauchy.norm_sum_range_sq_le_shift_correlation (N := N) hQ f
  have hbound := mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg L)
  calc
    _ ≤ (L : ℝ) * ∑ r ∈ Finset.range L, Complex.re
        (∑ a ∈ Finset.range Q, ∑ b ∈ Finset.range Q, F r a b) := hshift
    _ ≤ (L : ℝ) * ((Q : ℝ) * ((N : ℝ) +
        2 * ∑ h ∈ positiveRange Q, ‖correlation N h f‖)) := hbound
    _ = _ := by dsimp [L]; ring

/-- Ambient-length form, valid also when the averaging length exceeds the
actual interval length H. This avoids a hidden long-interval assumption in
iterated differencing. -/
theorem vdc_bound {N H Q : ℕ} (hH : H ≤ N) (hQ : 1 ≤ Q) (hQN : Q ≤ N)
    (f : ℕ → ℂ) (hf : ∀ n ∈ Finset.range H, ‖f n‖ ≤ 1) :
    ‖∑ n ∈ Finset.range H, f n‖^2 ≤
      2 * (N : ℝ)^2 / Q + 4 * (N : ℝ) / Q *
        ∑ h ∈ positiveRange Q, ‖correlation H h f‖ := by
  have hq : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hnr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hhr : (H : ℝ) ≤ N := by exact_mod_cast hH
  have hL : ((H+Q-1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show H+Q-1 ≤ 2*N by omega)
  have hc : 0 ≤ ∑ h ∈ positiveRange Q, ‖correlation H h f‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hw := weighted_vdc hQ f hf
  have hb : (Q : ℝ)^2 * ‖∑ n ∈ Finset.range H, f n‖^2 ≤
      2 * (N : ℝ) * (Q : ℝ) *
        ((N : ℝ) + 2 * ∑ h ∈ positiveRange Q, ‖correlation H h f‖) := by
    apply hw.trans
    gcongr
  have hd := div_le_div_of_nonneg_right hb (sq_nonneg (Q : ℝ))
  have heleft : (Q : ℝ)^2 * ‖∑ n ∈ Finset.range H, f n‖^2 / (Q : ℝ)^2 =
      ‖∑ n ∈ Finset.range H, f n‖^2 := by field_simp
  rw [heleft] at hd
  convert hd using 1 <;> field_simp <;> ring

end FordDiscreteVdC
#print axioms FordDiscreteVdC.weighted_vdc

#print axioms FordDiscreteVdC.vdc_bound
