import JutilaDeterministicCore

/-!
# Weighted Halasz large-value front for Jutila p.53

This packages the already certified finite Halasz inequality in exactly the
form used after the pointwise detector lower bound: the square of
`#selected * detectorSize` is bounded by the coefficient quotient times the
full weighted correlation energy.
-/

namespace MAPJutilaHalaszLargeValueFront

open scoped BigOperators ComplexConjugate
open MAPJutilaDeterministicCore

noncomputable section

/-- The real correlation weight in Jutila (3.3), with the pseudocharacter
sum abstracted as `P`. -/
def jutilaCorrelationWeight
    (M N : ℝ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (P n) ^ 2 *
    (Real.exp (-((n : ℝ) / N)) - Real.exp (-((n : ℝ) / M)))

/-- Positivity of the source weight on the actual coefficient support. -/
theorem jutilaCorrelationWeight_pos
    {M N : ℝ} (hM : 0 < M) (hMN : M < N)
    {P : ℕ → ℝ} {n : ℕ} (hn : 0 < n) (hPn : P n ≠ 0) :
    0 < jutilaCorrelationWeight M N P n := by
  have hN : 0 < N := hM.trans hMN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiv : (n : ℝ) / N < (n : ℝ) / M := by
    exact (div_lt_div_iff_of_pos_left hnR hN hM).2 hMN
  have hexp :
      Real.exp (-((n : ℝ) / M)) < Real.exp (-((n : ℝ) / N)) := by
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold jutilaCorrelationWeight
  exact mul_pos (mul_pos (inv_pos.mpr hnR) (sq_pos_of_ne_zero hPn))
    (sub_pos.mpr hexp)

theorem finite_weighted_halasz_large_value_front
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (b : K → ℝ) (v : I → K → ℂ) (V : ℝ)
    (hb : ∀ k ∈ cols, 0 < b k) (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ((rows.card : ℝ) * V) ^ 2 ≤
        (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b eta v := by
  obtain ⟨eta, heta, hhalasz⟩ :=
    finite_halasz_inequality rows cols a b v hb
  refine ⟨eta, heta, ?_⟩
  have hcard : (rows.card : ℝ) * V ≤
      ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ := by
    calc
      (rows.card : ℝ) * V = ∑ _i ∈ rows, V := by simp
      _ ≤ ∑ i ∈ rows, ‖finitePolynomial cols a v i‖ := by
        apply Finset.sum_le_sum
        intro i hi
        exact hlarge i hi
  have hsquare := pow_le_pow_left₀
    (mul_nonneg (Nat.cast_nonneg _) hV) hcard 2
  exact hsquare.trans hhalasz

theorem finite_weighted_halasz_large_value_front_expanded
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (b : K → ℝ) (v : I → K → ℂ) (V : ℝ)
    (hb : ∀ k ∈ cols, 0 < b k) (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ((rows.card : ℝ) * V) ^ 2 ≤
        (∑ k ∈ cols, ‖a k‖ ^ 2 / b k) *
          correlationEnergy rows cols b eta v ∧
      (correlationEnergy rows cols b eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows,
          conj (eta i) * eta j *
            (∑ k ∈ cols, (b k : ℂ) * conj (v i k) * v j k) := by
  obtain ⟨eta, heta, hbound⟩ :=
    finite_weighted_halasz_large_value_front
      rows cols a b v V hb hV hlarge
  refine ⟨eta, heta, hbound, ?_⟩
  exact correlationEnergy_eq_doubleSum rows cols b eta v

end

end MAPJutilaHalaszLargeValueFront

#print axioms MAPJutilaHalaszLargeValueFront.finite_weighted_halasz_large_value_front_expanded
