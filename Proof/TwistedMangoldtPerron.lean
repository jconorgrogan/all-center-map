import PerronKernel
import PrimitiveExplicitFormulaSpine

/-!
# Finite Perron kernels for twisted Mangoldt coefficients

This is an exact specialization of `PerronKernel` to the coefficient sequence
already certified in `PrimitiveExplicitFormulaSpine`.  It remains a finite
Dirichlet polynomial: no convergence, contour shift, or explicit formula is
smuggled into a hypothesis.
-/

namespace TwistedMangoldtPerron

open Set MeasureTheory PerronKernel
open scoped BigOperators Interval ArithmeticFunction

noncomputable section

def ratio (x : ℝ) (n : ℕ) : ℝ := x / n

def polynomial {q : ℕ} (chi : DirichletCharacter ℂ q) (x : ℝ)
    (N : ℕ) (c t : ℝ) : ℂ :=
  finitePerronPolynomial (Finset.Icc 1 N)
    (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi) (ratio x) c t

theorem ratio_pos {x : ℝ} {n N : ℕ} (hx : 0 < x)
    (hn : n ∈ Finset.Icc 1 N) :
    0 < ratio x n := by
  rw [ratio]
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  exact div_pos hx (Nat.cast_pos.mpr (by omega))

/-- Exact finite-height vertical-segment identity for the twisted Mangoldt
Dirichlet polynomial. -/
theorem exact_finite_vertical_segment {q N : ℕ}
    (chi : DirichletCharacter ℂ q) (x : ℝ) {c T : ℝ} (hc : 0 < c) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, polynomial chi x N c t)) =
      ∑ n ∈ Finset.Icc 1 N,
        PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi n *
          kernel (ratio x n) c T := by
  exact kernel_finset_sum (Finset.Icc 1 N)
    (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi) (ratio x) hc

/-- Character-uniform absolute bound for the literal finite vertical segment.
The right side contains only the ordinary von Mangoldt function. -/
theorem norm_finite_vertical_segment_le {q N : ℕ}
    (chi : DirichletCharacter ℂ q) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 ≤ T) :
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, polynomial chi x N c t)) ≤
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          ((ratio x n) ^ c * T / (Real.pi * c)) := by
  calc
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, polynomial chi x N c t)) ≤
      ∑ n ∈ Finset.Icc 1 N,
        ‖PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi n‖ *
          ((ratio x n) ^ c * T / (Real.pi * c)) := by
      exact norm_integral_finitePerronPolynomial_le (Finset.Icc 1 N)
        (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi) (ratio x)
        (fun n hn => ratio_pos hx hn) hc hT
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          ((ratio x n) ^ c * T / (Real.pi * c)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (PrimitiveExplicitFormulaSpine.norm_twistedMangoldtCoeff_le chi n)
        (div_nonneg
          (mul_nonneg (Real.rpow_nonneg (ratio_pos hx hn).le c) hT)
          (mul_nonneg Real.pi_pos.le hc.le))

/-- Transition-band estimate with the exact endpoint weight.  This is the
near-integer-safe finite Perron statement for twisted Mangoldt coefficients.
It is uniform in the character and modulus. -/
theorem norm_finite_vertical_sub_arctan_weight_le {q N : ℕ}
    (chi : DirichletCharacter ℂ q) {x c T : ℝ}
    (hx : 0 < x) (hc : 0 < c) (hT : 0 ≤ T)
    (hnear : ∀ n ∈ Finset.Icc 1 N,
      |Real.log (ratio x n)| * (c + T) ≤ 1) :
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ t in (-T)..T, polynomial chi x N c t) -
        ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.Icc 1 N,
            PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi n) ≤
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          (2 * T * |Real.log (ratio x n)| / Real.pi) := by
  calc
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ t in (-T)..T, polynomial chi x N c t) -
        ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.Icc 1 N,
            PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi n) ≤
      ∑ n ∈ Finset.Icc 1 N,
        ‖PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi n‖ *
          (2 * T * |Real.log (ratio x n)| / Real.pi) := by
      exact norm_finitePerron_sub_arctan_weight_le (Finset.Icc 1 N)
        (PrimitiveExplicitFormulaSpine.twistedMangoldtCoeff chi) (ratio x)
        (fun n hn => ratio_pos hx hn) hc hT hnear
    _ ≤ ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          (2 * T * |Real.log (ratio x n)| / Real.pi) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_right
        (PrimitiveExplicitFormulaSpine.norm_twistedMangoldtCoeff_le chi n)
        (by positivity)

end

end TwistedMangoldtPerron
