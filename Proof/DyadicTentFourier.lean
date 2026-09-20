import Mathlib

namespace MAPDyadicTentFourier

open MeasureTheory Set
open scoped FourierTransform

noncomputable section

/-- The continuous triangular autocorrelation of an interval of length `X`. -/
def tent (X t : ℝ) : ℂ := ((max 0 (X - |t|) : ℝ) : ℂ)

@[fun_prop] theorem continuous_tent (X : ℝ) : Continuous (tent X) := by
  unfold tent
  fun_prop

theorem tent_eq_zero_of_abs_ge {X t : ℝ} (h : X ≤ |t|) : tent X t = 0 := by
  simp [tent, max_eq_left (sub_nonpos.mpr h)]

theorem tent_eq_on_Icc {X t : ℝ} (ht : t ∈ Icc (-X) X) :
    tent X t = ((X - |t| : ℝ) : ℂ) := by
  rw [tent, max_eq_right]
  rw [mem_Icc] at ht
  exact sub_nonneg.mpr (abs_le.mpr ⟨by linarith, ht.2⟩)

theorem tent_eq_indicator (X : ℝ) (hX : 0 ≤ X) :
    tent X = (Icc (-X) X).indicator (fun t => ((X - |t| : ℝ) : ℂ)) := by
  funext t
  by_cases ht : t ∈ Icc (-X) X
  · rw [indicator_of_mem ht, tent_eq_on_Icc ht]
  · rw [indicator_of_notMem ht]
    have hab : X ≤ |t| := by
      simp only [mem_Icc, not_and_or, not_le] at ht
      rcases ht with ht | ht
      · linarith [neg_le_abs t]
      · linarith [le_abs_self t]
    exact tent_eq_zero_of_abs_ge hab

theorem integrable_tent (X : ℝ) (hX : 0 ≤ X) : Integrable (tent X) := by
  rw [tent_eq_indicator X hX]
  have hc : Continuous (fun t : ℝ => ((X - |t| : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub continuous_abs)
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

/-- Primitive for `(X-x) exp(c x)` on the positive half of the tent. -/
def tentPrimitivePos (X : ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (c * x) * ((((X - x : ℝ) : ℂ) / c) + 1 / c ^ 2)

/-- Primitive for `(X+x) exp(c x)` on the negative half of the tent. -/
def tentPrimitiveNeg (X : ℝ) (c : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (c * x) * ((((X + x : ℝ) : ℂ) / c) - 1 / c ^ 2)

theorem hasDerivAt_tentPrimitivePos
    {X : ℝ} {c : ℂ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (tentPrimitivePos X c)
      (((X - x : ℝ) : ℂ) * Complex.exp (c * x)) x := by
  unfold tentPrimitivePos
  have he0 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    convert (hasDerivAt_id x).ofReal_comp.const_mul c using 1 <;> simp
  have he : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
      (Complex.exp (c * x) * c) x := he0.cexp
  have hb0 : HasDerivAt (fun y : ℝ => ((X - y : ℝ) : ℂ)) (-1 : ℂ) x := by
    convert ((hasDerivAt_const x X).sub (hasDerivAt_id x)).ofReal_comp using 1 <;> simp
  have hb : HasDerivAt
      (fun y : ℝ => (((X - y : ℝ) : ℂ) / c + 1 / c ^ 2)) (-1 / c) x := by
    convert (hb0.div_const c).add_const (1 / c ^ 2) using 1 <;> ring
  convert he.mul hb using 1 <;> field_simp <;> ring

theorem hasDerivAt_tentPrimitiveNeg
    {X : ℝ} {c : ℂ} (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (tentPrimitiveNeg X c)
      (((X + x : ℝ) : ℂ) * Complex.exp (c * x)) x := by
  unfold tentPrimitiveNeg
  have he0 : HasDerivAt (fun y : ℝ => c * (y : ℂ)) c x := by
    convert (hasDerivAt_id x).ofReal_comp.const_mul c using 1 <;> simp
  have he : HasDerivAt (fun y : ℝ => Complex.exp (c * y))
      (Complex.exp (c * x) * c) x := he0.cexp
  have hb0 : HasDerivAt (fun y : ℝ => ((X + y : ℝ) : ℂ)) (1 : ℂ) x := by
    convert ((hasDerivAt_const x X).add (hasDerivAt_id x)).ofReal_comp using 1 <;> simp
  have hb : HasDerivAt
      (fun y : ℝ => (((X + y : ℝ) : ℂ) / c - 1 / c ^ 2)) (1 / c) x := by
    convert (hb0.div_const c).sub_const (1 / c ^ 2) using 1 <;> ring
  convert he.mul hb using 1 <;> field_simp <;> ring

theorem integral_tent_pos_half
    {X : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ x in 0..X, ((X - x : ℝ) : ℂ) * Complex.exp (c * x)) =
      tentPrimitivePos X c X - tentPrimitivePos X c 0 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := tentPrimitivePos X c)
    (f' := fun x : ℝ => ((X - x : ℝ) : ℂ) * Complex.exp (c * x))
  · intro x hx
    exact hasDerivAt_tentPrimitivePos hc x
  · exact (by fun_prop : Continuous
      (fun x : ℝ => ((X - x : ℝ) : ℂ) * Complex.exp (c * x))).intervalIntegrable _ _

theorem integral_tent_neg_half
    {X : ℝ} {c : ℂ} (hc : c ≠ 0) :
    (∫ x in -X..0, ((X + x : ℝ) : ℂ) * Complex.exp (c * x)) =
      tentPrimitiveNeg X c 0 - tentPrimitiveNeg X c (-X) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := tentPrimitiveNeg X c)
    (f' := fun x : ℝ => ((X + x : ℝ) : ℂ) * Complex.exp (c * x))
  · intro x hx
    exact hasDerivAt_tentPrimitiveNeg hc x
  · exact (by fun_prop : Continuous
      (fun x : ℝ => ((X + x : ℝ) : ℂ) * Complex.exp (c * x))).intervalIntegrable _ _

theorem integral_tent_exp_eq
    {X : ℝ} (hX : 0 ≤ X) {c : ℂ} (hc : c ≠ 0) :
    (∫ x : ℝ, tent X x * Complex.exp (c * x)) =
      (Complex.exp (c * X) + Complex.exp (c * (-X)) - 2) / c ^ 2 := by
  have hcont : Continuous (fun x : ℝ =>
      (((X - |x| : ℝ) : ℂ) * Complex.exp (c * x))) := by
    fun_prop
  have hwhole :
      (∫ x : ℝ, tent X x * Complex.exp (c * x)) =
        ∫ x in -X..X, ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x) := by
    rw [tent_eq_indicator X hX]
    calc
      (∫ x : ℝ,
          (Icc (-X) X).indicator (fun t => ((X - |t| : ℝ) : ℂ)) x *
            Complex.exp (c * x)) =
          ∫ x : ℝ, (Icc (-X) X).indicator
            (fun t => ((X - |t| : ℝ) : ℂ) * Complex.exp (c * t)) x := by
              apply integral_congr_ae
              filter_upwards with x
              by_cases hx : x ∈ Icc (-X) X <;> simp [hx]
      _ = ∫ x in Icc (-X) X,
          ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x) := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
      _ = ∫ x in Ioc (-X) X,
          ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x) :=
            integral_Icc_eq_integral_Ioc
      _ = ∫ x in -X..X,
          ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x) := by
            rw [intervalIntegral.integral_of_le (by linarith)]
  rw [hwhole]
  have hnegInt : IntervalIntegrable
      (fun x : ℝ => ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x)) volume (-X) 0 :=
    hcont.intervalIntegrable _ _
  have hposInt : IntervalIntegrable
      (fun x : ℝ => ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x)) volume 0 X :=
    hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hnegInt hposInt]
  have hnegEq :
      (∫ x in -X..0, ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x)) =
        ∫ x in -X..0, ((X + x : ℝ) : ℂ) * Complex.exp (c * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hx0 : x ≤ 0 := hx.2
    simp only [abs_of_nonpos hx0]
    push_cast
    ring
  have hposEq :
      (∫ x in 0..X, ((X - |x| : ℝ) : ℂ) * Complex.exp (c * x)) =
        ∫ x in 0..X, ((X - x : ℝ) : ℂ) * Complex.exp (c * x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hX] at hx
    have hx0 : 0 ≤ x := hx.1
    simp only [abs_of_nonneg hx0]
  rw [hnegEq, hposEq, integral_tent_neg_half hc, integral_tent_pos_half hc]
  unfold tentPrimitiveNeg tentPrimitivePos
  have hnegArg : c * ((-X : ℝ) : ℂ) = -(c * (X : ℂ)) := by
    push_cast
    ring
  rw [hnegArg]
  norm_num
  field_simp
  ring

/-- Mathlib's negative-sign Fourier transform of the tent, at every nonzero
frequency. -/
theorem fourier_tent_eq_formula
    {X β : ℝ} (hX : 0 ≤ X) (hβ : β ≠ 0) :
    FourierTransform.fourier (tent X) β =
      (Complex.exp ((-2 * Real.pi * Complex.I * β) * X) +
        Complex.exp ((-2 * Real.pi * Complex.I * β) * (-X)) - 2) /
          (-2 * Real.pi * Complex.I * β) ^ 2 := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hc : (-2 * Real.pi * Complex.I * (β : ℂ)) ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hβ)
  have hint :
      (∫ x : ℝ,
          Complex.exp ((-2 * Real.pi * Complex.I * β) * x) * tent X x) =
        ∫ x : ℝ, tent X x *
          Complex.exp ((-2 * Real.pi * Complex.I * β) * x) := by
    apply integral_congr_ae
    filter_upwards with x
    ring
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * β) * Complex.I) • tent X x) =
        ∫ x : ℝ,
          Complex.exp ((-2 * Real.pi * Complex.I * β) * x) * tent X x := by
            apply integral_congr_ae
            filter_upwards with x
            rw [smul_eq_mul]
            congr 2
            push_cast
            ring
    _ = ∫ x : ℝ, tent X x *
          Complex.exp ((-2 * Real.pi * Complex.I * β) * x) := hint
    _ = _ := integral_tent_exp_eq hX hc

end

end MAPDyadicTentFourier
