import HuxleyFixedModulusSpecialization

/-!
# The finite Halasz front of Huxley's reflection argument

This module proves the finite Hilbert-space step behind Huxley 1973 (2.1)
and the exact cutoff plateau (2.8)--(2.9).  Consequently the next unproved
source step is the analytic estimate for the off-diagonal correlation series,
not a large-value or density statement.
-/

namespace MAPHuxleyHalaszFront

open scoped BigOperators ComplexConjugate
open MAPJutilaDeterministicCore

noncomputable section

/-! ## Huxley's Mellin cutoff on the detector interval -/

/-- The piecewise coefficient `b(m,U)` in Huxley 1973, equation (2.8).
The middle plateau is tested first; at its two boundary points the cosine
formula has the same value. -/
def huxleyCutoffWeight (m U : ℝ) : ℝ :=
  if Real.exp 1 * U ≤ m ∧ m ≤ Real.exp 3 * U then 1
  else if m ≤ U ∨ Real.exp 4 * U ≤ m then 0
  else (1 / 2) * (1 - Real.cos (Real.pi * Real.log (m / U)))

/-- Under Huxley's exact scale condition (2.9), every point of the dyadic
coefficient interval lies on the unit plateau of (2.8).  This is precisely
the positivity input `b(m)>=1` needed in Halasz's inequality. -/
theorem huxleyCutoffWeight_eq_one_of_dyadic
    {m N U : ℝ}
    (hNUlow : Real.exp 1 * U ≤ N)
    (hNUhigh : N ≤ (1 / 2) * Real.exp 3 * U)
    (hmLow : N < m) (hmHigh : m ≤ 2 * N) :
    huxleyCutoffWeight m U = 1 := by
  rw [huxleyCutoffWeight, if_pos]
  constructor
  · exact hNUlow.trans hmLow.le
  · calc
      m ≤ 2 * N := hmHigh
      _ ≤ 2 * ((1 / 2) * Real.exp 3 * U) :=
        mul_le_mul_of_nonneg_left hNUhigh (by norm_num)
      _ = Real.exp 3 * U := by ring

theorem huxleyCutoffWeight_ge_one_of_dyadic
    {m N U : ℝ}
    (hNUlow : Real.exp 1 * U ≤ N)
    (hNUhigh : N ≤ (1 / 2) * Real.exp 3 * U)
    (hmLow : N < m) (hmHigh : m ≤ 2 * N) :
    1 ≤ huxleyCutoffWeight m U := by
  rw [huxleyCutoffWeight_eq_one_of_dyadic hNUlow hNUhigh hmLow hmHigh]

/-! ## Huxley (2.1) before analytic correlation estimation -/

/-- Coefficient energy in the finite dyadic polynomial. -/
def coefficientEnergy
    {K : Type*} [DecidableEq K] (cols : Finset K) (a : K → ℂ) : ℝ :=
  ∑ k ∈ cols, ‖a k‖ ^ 2

/-- Exact large-value corollary of the already certified finite Halasz
inequality.  If every row polynomial has size at least `V`, the square of
`#rows * V` is controlled by coefficient energy times the full correlation
energy.  No spacing or analytic estimate is used here. -/
theorem finite_halasz_large_value_front
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (v : I → K → ℂ) (V : ℝ)
    (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ((rows.card : ℝ) * V) ^ 2 ≤
        coefficientEnergy cols a *
          correlationEnergy rows cols (fun _ => 1) eta v := by
  obtain ⟨eta, heta, hhalasz⟩ :=
    finite_halasz_inequality rows cols a (fun _ => 1) v (by simp)
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
  calc
    ((rows.card : ℝ) * V) ^ 2 ≤
        (∑ i ∈ rows, ‖finitePolynomial cols a v i‖) ^ 2 := hsquare
    _ ≤ (∑ k ∈ cols, ‖a k‖ ^ 2 / (1 : ℝ)) *
        correlationEnergy rows cols (fun _ => 1) eta v := hhalasz
    _ = coefficientEnergy cols a *
        correlationEnergy rows cols (fun _ => 1) eta v := by
      simp [coefficientEnergy]

/-- The correlation energy in the preceding theorem is literally the double
correlation series to which Huxley applies the Mellin kernel and reflection
argument. -/
theorem finite_halasz_large_value_front_expanded
    {I K : Type*} [DecidableEq I] [DecidableEq K]
    (rows : Finset I) (cols : Finset K)
    (a : K → ℂ) (v : I → K → ℂ) (V : ℝ)
    (hV : 0 ≤ V)
    (hlarge : ∀ i ∈ rows, V ≤ ‖finitePolynomial cols a v i‖) :
    ∃ eta : I → ℂ,
      (∀ i ∈ rows, ‖eta i‖ = 1) ∧
      ((rows.card : ℝ) * V) ^ 2 ≤
        coefficientEnergy cols a *
          correlationEnergy rows cols (fun _ => 1) eta v ∧
      (correlationEnergy rows cols (fun _ => 1) eta v : ℂ) =
        ∑ i ∈ rows, ∑ j ∈ rows,
          conj (eta i) * eta j *
            (∑ k ∈ cols, conj (v i k) * v j k) := by
  obtain ⟨eta, heta, hbound⟩ :=
    finite_halasz_large_value_front rows cols a v V hV hlarge
  refine ⟨eta, heta, hbound, ?_⟩
  simpa using correlationEnergy_eq_doubleSum
    rows cols (fun _ => 1) eta v

end


end MAPHuxleyHalaszFront

#print axioms MAPHuxleyHalaszFront.huxleyCutoffWeight_eq_one_of_dyadic
#print axioms MAPHuxleyHalaszFront.finite_halasz_large_value_front
#print axioms MAPHuxleyHalaszFront.finite_halasz_large_value_front_expanded
