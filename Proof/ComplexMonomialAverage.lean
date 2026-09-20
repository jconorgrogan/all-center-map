import APExplicitFormulaMajorantAdapter

/-!
# Oscillatory right averages of zero monomials

This is a staging module for the paper-window zero-field route.  Unlike the
existing `rightAverage`, it retains the complex phase before taking a norm.
The main identity below is premise-free complex calculus: the average of
`t^(rho-1)` is the endpoint difference divided by `y*rho`.
-/

namespace MAPPaperWindowVKBypass

open Complex MeasureTheory Set
open scoped BigOperators

noncomputable section

/-- The signed/complex right average.  The normalization is written in `ℂ`
so it can be applied directly to the literal zero field. -/
def complexRightAverage (f : ℝ → ℂ) (y x : ℝ) : ℂ :=
  (y : ℂ)⁻¹ * ∫ t : ℝ in x..x + y, f t

/-- Exact endpoint formula for one zero monomial. -/
theorem complexRightAverage_cpow_sub_one_eq
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    complexRightAverage (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) y x =
      (((x + y : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ((y : ℂ) * ρ) := by
  have hr : -1 < (ρ - 1).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have hρ0 : ρ ≠ 0 := by
    intro h
    subst ρ
    simp at hρ
  have hy0 : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  unfold complexRightAverage
  rw [integral_cpow (Or.inl hr)]
  simp only [sub_add_cancel]
  field_simp

/-- The ordinate is bounded by the norm of the zero. -/
theorem abs_im_le_norm_self (ρ : ℂ) : |ρ.im| ≤ ‖ρ‖ :=
  Complex.abs_im_le_norm ρ

/-- Trivial short-interval estimate.  It is paired with the oscillatory
endpoint estimate below, so the resulting envelope is their minimum. -/
theorem norm_complexRightAverage_cpow_sub_one_le_trivial
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    {ρ : ℂ} (hβ : ρ.re ≤ 1) :
    ‖complexRightAverage (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) y x‖ ≤
      Real.rpow x (ρ.re - 1) := by
  have hint :
      ‖∫ t : ℝ in x..x + y, (t : ℂ) ^ (ρ - 1)‖ ≤
        Real.rpow x (ρ.re - 1) * |(x + y) - x| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Set.Ioc x (x + y) := by
      rw [Set.uIoc_of_le (by linarith)] at ht
      exact ht
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hx.trans ht'.1)]
    simp only [Complex.sub_re, Complex.one_re]
    exact Real.rpow_le_rpow_of_nonpos hx (le_of_lt ht'.1) (by linarith)
  unfold complexRightAverage
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy]
  have habs : |(x + y) - x| = y := by simp [abs_of_pos hy]
  rw [habs] at hint
  calc
    y⁻¹ * ‖∫ t : ℝ in x..x + y, (t : ℂ) ^ (ρ - 1)‖ ≤
        y⁻¹ * (Real.rpow x (ρ.re - 1) * y) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hy.le)
    _ = Real.rpow x (ρ.re - 1) := by field_simp

/-- Oscillatory endpoint estimate.  This is the actual source of the
`1/|gamma|` multiplier; no signs have been discarded before this point. -/
theorem norm_complexRightAverage_cpow_sub_one_le
    {x y U : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y ≤ U) (hU : 0 ≤ U)
    {ρ : ℂ} (hρ : 0 < ρ.re) :
    ‖complexRightAverage (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) y x‖ ≤
      2 * Real.rpow U ρ.re / (y * ‖ρ‖) := by
  rw [complexRightAverage_cpow_sub_one_eq hx hy hρ]
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hy]
  have hxU : x ≤ U := by linarith
  have hxypos : 0 < x + y := by linarith
  have hpowxy :
      ‖(((x + y : ℝ) : ℂ) ^ ρ)‖ ≤ Real.rpow U ρ.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxypos]
    exact Real.rpow_le_rpow hxypos.le hxy hρ.le
  have hpowx : ‖(x : ℂ) ^ ρ‖ ≤ Real.rpow U ρ.re := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    exact Real.rpow_le_rpow hx.le hxU hρ.le
  have hnum :
      ‖(((x + y : ℝ) : ℂ) ^ ρ) - (x : ℂ) ^ ρ‖ ≤
        2 * Real.rpow U ρ.re := by
    calc
      ‖(((x + y : ℝ) : ℂ) ^ ρ) - (x : ℂ) ^ ρ‖ ≤
          ‖(((x + y : ℝ) : ℂ) ^ ρ)‖ + ‖(x : ℂ) ^ ρ‖ := norm_sub_le _ _
      _ ≤ Real.rpow U ρ.re + Real.rpow U ρ.re := add_le_add hpowxy hpowx
      _ = 2 * Real.rpow U ρ.re := by ring
  exact div_le_div_of_nonneg_right hnum (mul_nonneg hy.le (norm_nonneg ρ))

/-- A denominator-free version in terms of the ordinate, valid away from the
real axis. -/
theorem norm_complexRightAverage_cpow_sub_one_le_im
    {x y U : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y ≤ U) (hU : 0 ≤ U)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hγ : 0 < |ρ.im|) :
    ‖complexRightAverage (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) y x‖ ≤
      2 * Real.rpow U ρ.re / (y * |ρ.im|) := by
  refine (norm_complexRightAverage_cpow_sub_one_le hx hy hxy hU hρ).trans ?_
  apply div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (Real.rpow_nonneg hU _))
  · exact mul_pos hy hγ
  · exact mul_le_mul_of_nonneg_left (abs_im_le_norm_self ρ) hy.le

/-- Phase-sensitive minimum envelope.  This is the clean implementation-level
form of the paper-window multiplier, before specializing `x,U` to constant
multiples of the paper scale `X`. -/
theorem norm_complexRightAverage_cpow_sub_one_le_min
    {x y U : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hxy : x + y ≤ U) (hU : 0 ≤ U)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hβ : ρ.re ≤ 1)
    (hγ : 0 < |ρ.im|) :
    ‖complexRightAverage (fun t : ℝ => (t : ℂ) ^ (ρ - 1)) y x‖ ≤
      min (Real.rpow x (ρ.re - 1))
        (2 * Real.rpow U ρ.re / (y * |ρ.im|)) := by
  exact le_min
    (norm_complexRightAverage_cpow_sub_one_le_trivial hx hy hβ)
    (norm_complexRightAverage_cpow_sub_one_le_im hx hy hxy hU hρ hγ)

end
end MAPPaperWindowVKBypass

#print axioms MAPPaperWindowVKBypass.complexRightAverage_cpow_sub_one_eq
#print axioms MAPPaperWindowVKBypass.norm_complexRightAverage_cpow_sub_one_le_trivial
#print axioms MAPPaperWindowVKBypass.norm_complexRightAverage_cpow_sub_one_le
#print axioms MAPPaperWindowVKBypass.norm_complexRightAverage_cpow_sub_one_le_im
#print axioms MAPPaperWindowVKBypass.norm_complexRightAverage_cpow_sub_one_le_min
