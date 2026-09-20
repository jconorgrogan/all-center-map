import PrimitiveRectangleSpecialization
import SharpFinitePerronStep

/-!
# Sharp arithmetic Perron remainder bridge

This applies the compiled `1/pi` kernel estimate coefficientwise to the exact
inside-prefix discrepancy used by the primitive explicit formula.
-/

namespace SharpPerronRemainderBridge

open scoped BigOperators ArithmeticFunction
open PrimitiveTruncatedExplicitFormulaBridge
open SharpFinitePerronStep

noncomputable section

/-- Every coefficient in the half-integer prefix lies strictly inside the
Perron step, so the transition singularity `y=1` never occurs. -/
theorem one_lt_halfIntegerPoint_div_nat
    {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    1 < halfIntegerPoint N / (n : ℝ) := by
  simp only [Finset.mem_Icc] at hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hnle : (n : ℝ) ≤ N := by exact_mod_cast hn.2
  rw [one_lt_div hnpos]
  unfold halfIntegerPoint
  linarith

/-- Sharp coefficientwise bound for the literal inside-kernel error.  This is
uniform in the character and keeps the exact logarithmic distance to the
half-integer endpoint. -/
theorem norm_insideKernelError_le_sharp
    {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖insideKernelError χ N c T‖ ≤
      ∑ n ∈ Finset.Icc 1 N,
        ArithmeticFunction.vonMangoldt n *
          ((halfIntegerPoint N / n) ^ c /
            (Real.pi * T * |Real.log (halfIntegerPoint N / n)|)) := by
  refine (norm_insideKernelError_le χ N c T).trans ?_
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _
    (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  have hy1 := one_lt_halfIntegerPoint_div_nat hn
  have hkernel := norm_kernel_sub_one_le hy1 hc hT
  calc
    ‖1 - PerronKernel.kernel (halfIntegerPoint N / n) c T‖ =
        ‖PerronKernel.kernel (halfIntegerPoint N / n) c T - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    _ ≤ _ := hkernel

end

end SharpPerronRemainderBridge
