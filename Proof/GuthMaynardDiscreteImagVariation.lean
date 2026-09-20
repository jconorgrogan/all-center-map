import GuthMaynardDiscreteFirstDerivative

namespace GuthMaynardDiscreteImagVariation

noncomputable section

def imagCoeff (b : ℝ) : ℂ := (-((1 : ℝ) / 2) : ℂ) - (b : ℂ) * Complex.I

theorem norm_imagCoeff_sub
    {x y : ℝ} (hyx : y ≤ x) :
    ‖imagCoeff y - imagCoeff x‖ = x - y := by
  unfold imagCoeff
  have hxy : 0 ≤ x - y := sub_nonneg.mpr hyx
  calc
    ‖((-((1 : ℝ) / 2) : ℂ) - (y : ℂ) * Complex.I) -
        ((-((1 : ℝ) / 2) : ℂ) - (x : ℂ) * Complex.I)‖ =
      ‖((x - y : ℝ) : ℂ) * Complex.I‖ := by
        congr 1
        push_cast
        ring
    _ = x - y := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hxy, Complex.norm_I, mul_one]

theorem sum_norm_imagCoeff_diff_of_antitone
    (k : ℕ) (b : ℕ → ℝ) (hb : Antitone b) :
    ∑ n ∈ Finset.range k, ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ =
      b 0 - b k := by
  calc
    ∑ n ∈ Finset.range k,
        ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ =
      ∑ n ∈ Finset.range k, (b n - b (n + 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact norm_imagCoeff_sub (hb (Nat.le_succ n))
    _ = b 0 - b k := by
      rw [Finset.sum_range_sub']

theorem sum_norm_imagCoeff_diff_le
    (k : ℕ) (b : ℕ → ℝ) (hb : Antitone b) {B : ℝ}
    (hB : b 0 - b k ≤ B) :
    ∑ n ∈ Finset.range k, ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ ≤ B := by
  rw [sum_norm_imagCoeff_diff_of_antitone k b hb]
  exact hB

theorem sum_norm_imagCoeff_diff_of_monotone
    (k : ℕ) (b : ℕ → ℝ) (hb : Monotone b) :
    ∑ n ∈ Finset.range k, ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ =
      b k - b 0 := by
  calc
    ∑ n ∈ Finset.range k,
        ‖imagCoeff (b (n + 1)) - imagCoeff (b n)‖ =
      ∑ n ∈ Finset.range k, (b (n + 1) - b n) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_sub_rev]
        exact norm_imagCoeff_sub (hb (Nat.le_succ n))
    _ = b k - b 0 := by
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Finset.sum_range_succ, ih]
          ring

end
end GuthMaynardDiscreteImagVariation

#print axioms GuthMaynardDiscreteImagVariation.norm_imagCoeff_sub
#print axioms GuthMaynardDiscreteImagVariation.sum_norm_imagCoeff_diff_of_antitone
#print axioms GuthMaynardDiscreteImagVariation.sum_norm_imagCoeff_diff_le
#print axioms GuthMaynardDiscreteImagVariation.sum_norm_imagCoeff_diff_of_monotone
