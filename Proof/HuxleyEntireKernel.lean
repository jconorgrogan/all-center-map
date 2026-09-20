import HuxleyReflectionKernelAlgebra
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# Huxley's reflection kernel is entire

Huxley 1973 calls the kernel in (2.6) an "integral function" before moving
the contour in Section 3.  The displayed rational formula has apparent poles
at `0` and `+- pi i`.  This file removes all three poles constructively.

The key point is the exact factorization

`exp(4w)+exp(3w)-exp(w)-1 = (exp(w)-1)(exp(w)+1)(exp(2w)+exp(w)+1)`.

The first linear factor is divided by `w` using a divided difference of
`exp`.  The second has zeros at both `pi i` and `-pi i`, so two successive
divided differences remove the other two poles.  Thus no removable-
singularity premise is introduced.
-/

namespace MAPHuxleyEntireKernel

open Complex Set

noncomputable section

private def p : ℂ := (Real.pi : ℂ) * I
private def n : ℂ := -((Real.pi : ℂ) * I)

/-- The numerator factorization implicit in Huxley (2.6). -/
theorem huxleyKernelNumerator_factor (w : ℂ) :
    MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator w =
      (exp w - 1) * (exp w + 1) * (exp (2 * w) + exp w + 1) := by
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator
  rw [show (4 : ℂ) * w = (4 : ℕ) * w by norm_num,
    exp_nat_mul,
    show (3 : ℂ) * w = (3 : ℕ) * w by norm_num,
    exp_nat_mul,
    show (2 : ℂ) * w = (2 : ℕ) * w by norm_num,
    exp_nat_mul]
  ring

/-- Entire extension of Huxley's kernel `K` from (2.6).  `dslope` supplies
the derivative value at each removed point and the ordinary quotient away
from it. -/
def huxleyKEntire (w : ℂ) : ℂ :=
  ((Real.pi : ℂ) ^ 2 / 2) *
    dslope exp 0 w *
    dslope (dslope exp p) n w *
    (exp (2 * w) + exp w + 1)

/-- The constructive extension is holomorphic on the whole plane. -/
theorem differentiable_huxleyKEntire :
    Differentiable ℂ huxleyKEntire := by
  have hexp : DifferentiableOn ℂ exp (univ : Set ℂ) :=
    Complex.differentiable_exp.differentiableOn
  have hslopeP : DifferentiableOn ℂ (dslope exp p) univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2 hexp
  have hslopePN : DifferentiableOn ℂ (dslope (dslope exp p) n) univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2 hslopeP
  have hslope0 : DifferentiableOn ℂ (dslope exp 0) univ :=
    (Complex.differentiableOn_dslope Filter.univ_mem).2 hexp
  have hslopePN' : Differentiable ℂ (dslope (dslope exp p) n) := by
    intro w
    simpa only [differentiableWithinAt_univ] using hslopePN w (mem_univ w)
  have hslope0' : Differentiable ℂ (dslope exp 0) := by
    intro w
    simpa only [differentiableWithinAt_univ] using hslope0 w (mem_univ w)
  unfold huxleyKEntire
  exact (((differentiable_const (c := ((Real.pi : ℂ) ^ 2 / 2))).mul
      hslope0').mul hslopePN').mul
    ((((differentiable_id.const_mul (2 : ℂ)).cexp).add
      Complex.differentiable_exp).add (differentiable_const (c := (1 : ℂ))))

theorem analytic_huxleyKEntire :
    AnalyticOnNhd ℂ huxleyKEntire univ :=
  differentiable_huxleyKEntire.differentiableOn.analyticOnNhd isOpen_univ

private theorem exp_p : exp p = -1 := by
  exact Complex.exp_pi_mul_I

private theorem exp_n : exp n = -1 := by
  unfold n
  rw [exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- Away from the three removable points, the entire extension equals
Huxley's literal rational kernel from (2.6). -/
theorem huxleyKEntire_eq_huxleyK
    {w : ℂ} (hw0 : w ≠ 0) (hwp : w ≠ p) (hwn : w ≠ n) :
    huxleyKEntire w = MAPHuxleyReflectionKernelAlgebra.huxleyK w := by
  rw [huxleyKEntire, dslope_of_ne exp hw0]
  rw [dslope_of_ne (dslope exp p) hwn]
  unfold slope
  have hnp : n ≠ p := by
    unfold n p
    intro h
    have hpi : (Real.pi : ℂ) = 0 := by
      apply mul_right_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num)
      calc
        (Real.pi : ℂ) * 2 =
            (((Real.pi : ℂ) * I) - (-((Real.pi : ℂ) * I))) * (-I) := by
              ring_nf
              simp [Complex.I_sq]
        _ = 0 := by rw [h]; ring
        _ = 0 * 2 := by ring
    exact (ofReal_ne_zero.mpr Real.pi_ne_zero) hpi
  rw [dslope_of_ne exp hwp, dslope_of_ne exp hnp]
  unfold slope MAPHuxleyReflectionKernelAlgebra.huxleyK
    MAPHuxleyReflectionKernelAlgebra.huxleyJ
  rw [huxleyKernelNumerator_factor, exp_zero, exp_p, exp_n]
  change
    ((Real.pi : ℂ) ^ 2 / 2) *
        ((w - 0)⁻¹ * (exp w - 1)) *
        ((w - n)⁻¹ * ((w - p)⁻¹ * (exp w - (-1)) -
          (n - p)⁻¹ * ((-1) - (-1)))) *
        (exp (2 * w) + exp w + 1) =
      ((exp w - 1) * (exp w + 1) * (exp (2 * w) + exp w + 1)) *
        ((Real.pi : ℂ) ^ 2 /
          (2 * w * (w - (Real.pi : ℂ) * I) *
            (w + (Real.pi : ℂ) * I)))
  have hwm0 : w - 0 ≠ 0 := sub_ne_zero.mpr hw0
  have hwpm : w - p ≠ 0 := sub_ne_zero.mpr hwp
  have hwnm : w - n ≠ 0 := sub_ne_zero.mpr hwn
  dsimp only [p, n] at hwpm hwnm ⊢
  have hplus : w + (Real.pi : ℂ) * I ≠ 0 := by
    simpa only [sub_neg_eq_add] using hwnm
  field_simp [hwm0, hwpm, hwnm, hplus, Complex.I_sq]
  ring

end

end MAPHuxleyEntireKernel

#print axioms MAPHuxleyEntireKernel.huxleyKernelNumerator_factor
#print axioms MAPHuxleyEntireKernel.differentiable_huxleyKEntire
#print axioms MAPHuxleyEntireKernel.analytic_huxleyKEntire
#print axioms MAPHuxleyEntireKernel.huxleyKEntire_eq_huxleyK
