import MertensAnalyticLeaf

/-!
# An elementary quantitative von Mangoldt p-series bound

This is the far-tail input for the Perron remainder at
`c = 1 + 1 / log x`.  It uses only `Λ(n) ≤ log n`, the elementary
`log n ≤ n^(delta/2)/(delta/2)`, and the integral-test p-series bound.
-/

namespace VonMangoldtPSeriesBound

open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Pointwise comparison with a p-series a half-exponent to the left. -/
theorem vonMangoldt_div_rpow_le
    {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (1 + delta) ≤
      (2 / delta) * (n : ℝ) ^ (-(1 + delta / 2)) := by
  by_cases hn0 : n = 0
  · subst n
    simp only [ArithmeticFunction.vonMangoldt_apply,
      if_neg not_isPrimePow_zero, zero_div]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _)
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn0
  have hlog : Real.log (n : ℝ) ≤
      (n : ℝ) ^ (delta / 2) / (delta / 2) :=
    Real.log_natCast_le_rpow_div n (by positivity)
  have hvm : ArithmeticFunction.vonMangoldt n ≤
      (n : ℝ) ^ (delta / 2) / (delta / 2) :=
    ArithmeticFunction.vonMangoldt_le_log.trans hlog
  have hden : 0 < (n : ℝ) ^ (1 + delta) :=
    Real.rpow_pos_of_pos hnpos _
  calc
    ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (1 + delta) ≤
      ((n : ℝ) ^ (delta / 2) / (delta / 2)) /
        (n : ℝ) ^ (1 + delta) :=
      div_le_div_of_nonneg_right hvm hden.le
    _ = (2 / delta) *
        ((n : ℝ) ^ (delta / 2) / (n : ℝ) ^ (1 + delta)) := by
      field_simp [hdelta.ne']
    _ = (2 / delta) * (n : ℝ) ^ (-(1 + delta / 2)) := by
      rw [← Real.rpow_sub hnpos]
      congr 2
      ring

/-- The von Mangoldt Dirichlet series at `1 + delta` is bounded explicitly
by `O(delta⁻²)`. -/
theorem tsum_vonMangoldt_div_rpow_le
    {delta : ℝ} (hdelta : 0 < delta) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (1 + delta)) ≤
      (2 / delta) * (1 + (delta / 2)⁻¹) := by
  let p : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + delta)
  let a : ℕ → ℝ := fun n =>
    (2 / delta) * (n : ℝ) ^ (-(1 + delta / 2))
  have hs : 1 < 1 + delta / 2 := by linarith
  have hseries : Summable fun n : ℕ =>
      (n : ℝ) ^ (-(1 + delta / 2)) := by
    change Summable (MAPMertensAnalyticLeaf.realRpowSummandHom (1 + delta / 2) (by linarith))
    exact MAPMertensAnalyticLeaf.summable_realRpowSummandHom hs
  have ha : Summable a := hseries.mul_left (2 / delta)
  have hpa : ∀ n, p n ≤ a n := fun n =>
    vonMangoldt_div_rpow_le hdelta n
  have hp0 : ∀ n, 0 ≤ p n := by
    intro n
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hp : Summable p := Summable.of_nonneg_of_le hp0 hpa ha
  calc
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
        (n : ℝ) ^ (1 + delta)) = ∑' n, p n := by rfl
    _ ≤ ∑' n, a n := hp.tsum_le_tsum hpa ha
    _ = (2 / delta) *
        ∑' n : ℕ, (n : ℝ) ^ (-(1 + delta / 2)) := by
      rw [tsum_mul_left]
    _ ≤ (2 / delta) * (1 + (delta / 2)⁻¹) := by
      apply mul_le_mul_of_nonneg_left
      · convert MAPMertensAnalyticLeaf.pSeries_le_one_add_inv_sub_one hs using 1 <;>
          ring
      · positivity

end

end VonMangoldtPSeriesBound
