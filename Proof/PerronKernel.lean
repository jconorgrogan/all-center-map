import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.RealDeriv

/-!
# A literal finite-height Perron kernel

This file does not assume Perron inversion.  It defines the actual vertical
segment integral, proves its elementary uniform bounds, and commutes it through
a finite Dirichlet polynomial.  The normalization is the number-theoretic one:
after parametrizing `s = c + it`, `ds = i dt`, the factor `1 / (2*pi*i)` is
`1 / (2*pi)`.
-/

namespace PerronKernel

open Set MeasureTheory
open scoped BigOperators Interval

noncomputable section

/-- The positive-base complex power on the vertical line `Re s = c`.  This
explicit formula avoids all branch conventions for `Complex.cpow`. -/
def verticalPower (y c t : ℝ) : ℂ :=
  (y ^ c : ℝ) * Complex.exp (Complex.I * (t * Real.log y))

theorem verticalPower_eq_exp {y : ℝ} (hy : 0 < y) (c t : ℝ) :
    verticalPower y c t =
      Complex.exp (((c : ℂ) + Complex.I * t) * Real.log y) := by
  rw [verticalPower, Real.rpow_def_of_pos hy, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The literal integrand obtained after parametrizing the Perron segment by
`s = c + it`. -/
def verticalIntegrand (y c t : ℝ) : ℂ :=
  verticalPower y c t / ((c : ℂ) + Complex.I * t)

/-- The finite-height Perron kernel
`(2*pi*i)^(-1) ∫_{c-iT}^{c+iT} y^s/s ds`. -/
def kernel (y c T : ℝ) : ℂ :=
  ((2 * Real.pi : ℝ) : ℂ)⁻¹ *
    ∫ t in (-T)..T, verticalIntegrand y c t

theorem norm_verticalPower (hy : 0 < y) (c t : ℝ) :
    ‖verticalPower y c t‖ = y ^ c := by
  rw [verticalPower, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hy c), Complex.norm_exp]
  simp

theorem denominator_ne_zero {c t : ℝ} (hc : 0 < c) :
    (c : ℂ) + Complex.I * t ≠ 0 := by
  intro h
  have := congr_arg Complex.re h
  simp at this
  linarith

theorem c_le_norm_denominator {c t : ℝ} (hc : 0 ≤ c) :
    c ≤ ‖(c : ℂ) + Complex.I * t‖ := by
  calc
    c = |(((c : ℂ) + Complex.I * t).re)| := by simp [abs_of_nonneg hc]
    _ ≤ ‖(c : ℂ) + Complex.I * t‖ := Complex.abs_re_le_norm _

theorem norm_denominator_le {c t T : ℝ} (hc : 0 ≤ c) (ht : |t| ≤ T) :
    ‖(c : ℂ) + Complex.I * t‖ ≤ c + T := by
  calc
    ‖(c : ℂ) + Complex.I * t‖
        ≤ ‖(c : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := norm_add_le _ _
    _ = c + |t| := by simp [Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c + T := by linarith

theorem norm_verticalIntegrand_le {y c t : ℝ} (hy : 0 < y) (hc : 0 < c) :
    ‖verticalIntegrand y c t‖ ≤ y ^ c / c := by
  rw [verticalIntegrand, norm_div, norm_verticalPower hy]
  exact div_le_div_of_nonneg_left (Real.rpow_nonneg (le_of_lt hy) c) hc
    (c_le_norm_denominator hc.le)

theorem continuous_verticalIntegrand {y c : ℝ} (hc : 0 < c) :
    Continuous (verticalIntegrand y c) := by
  unfold verticalIntegrand verticalPower
  apply Continuous.div
  · fun_prop
  · fun_prop
  · exact fun t => denominator_ne_zero hc

theorem intervalIntegrable_verticalIntegrand {y c a b : ℝ} (hc : 0 < c) :
    IntervalIntegrable (verticalIntegrand y c) volume a b :=
  (continuous_verticalIntegrand hc).intervalIntegrable _ _

/-- Inside the transition band `|log y| (c+T) ≤ 1`, the finite kernel is
Lipschitz around its endpoint value `y = 1`.  This is the literal
near-integer behavior: the kernel cannot be replaced by a sharp step when
`|log y|` is of order `1/T` or smaller. -/
theorem norm_verticalIntegrand_sub_one_le {y c t T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (ht : |t| ≤ T)
    (hnear : |Real.log y| * (c + T) ≤ 1) :
    ‖verticalIntegrand y c t - verticalIntegrand 1 c t‖ ≤
      2 * |Real.log y| := by
  let d : ℂ := (c : ℂ) + Complex.I * t
  have hd : d ≠ 0 := denominator_ne_zero hc
  have hdnorm : ‖d‖ ≤ c + T := norm_denominator_le hc.le ht
  have hlognorm : ‖(Real.log y : ℂ)‖ = |Real.log y| := by
    simp [Real.norm_eq_abs]
  have hz : ‖d * (Real.log y : ℂ)‖ ≤ 1 := by
    rw [norm_mul, hlognorm]
    exact (mul_le_mul_of_nonneg_right hdnorm (abs_nonneg _)).trans (by
      simpa [mul_comm] using hnear)
  have hexp := Complex.norm_exp_sub_one_le hz
  rw [verticalIntegrand, verticalIntegrand, verticalPower_eq_exp hy]
  have hone : verticalPower 1 c t = 1 := by simp [verticalPower]
  rw [hone, div_sub_div_same, norm_div]
  calc
    ‖Complex.exp (d * (Real.log y : ℂ)) - 1‖ / ‖d‖
        ≤ (2 * ‖d * (Real.log y : ℂ)‖) / ‖d‖ :=
          div_le_div_of_nonneg_right hexp (norm_nonneg _)
    _ = 2 * |Real.log y| := by
      rw [norm_mul, hlognorm]
      field_simp [norm_ne_zero_iff.mpr hd]

/-- Quantitative near-endpoint bound for the actual vertical segment. -/
theorem norm_kernel_sub_one_le {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hT : 0 ≤ T)
    (hnear : |Real.log y| * (c + T) ≤ 1) :
    ‖kernel y c T - kernel 1 c T‖ ≤
      2 * T * |Real.log y| / Real.pi := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hab : -T ≤ T := neg_le_self hT
  have hiY := intervalIntegrable_verticalIntegrand (y := y) (a := -T) (b := T) hc
  have hi1 := intervalIntegrable_verticalIntegrand (y := 1) (a := -T) (b := T) hc
  rw [kernel, kernel, ← mul_sub, ← intervalIntegral.integral_sub hiY hi1, norm_mul]
  have hconst : norm (((2 * Real.pi : ℝ) : ℂ)⁻¹) = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  have hint :
      ‖∫ t in (-T)..T, verticalIntegrand y c t - verticalIntegrand 1 c t‖ ≤
        (2 * |Real.log y|) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun t htmem => by
      have htIoc : t ∈ Set.Ioc (-T) T := by
        simpa [Set.uIoc_of_le hab] using htmem
      have ht : |t| ≤ T := abs_le.mpr ⟨by linarith [htIoc.1], htIoc.2⟩
      exact norm_verticalIntegrand_sub_one_le hy hc ht hnear)
  calc
    (2 * Real.pi)⁻¹ *
        ‖∫ t in (-T)..T, verticalIntegrand y c t - verticalIntegrand 1 c t‖
        ≤ (2 * Real.pi)⁻¹ * ((2 * |Real.log y|) * |T - (-T)|) :=
          mul_le_mul_of_nonneg_left hint
            (inv_nonneg.mpr (mul_nonneg (by norm_num) hpi.le))
    _ = 2 * T * |Real.log y| / Real.pi := by
      have habs : |T - (-T)| = 2 * T := by
        rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (mul_nonneg (by norm_num) hT)]
      rw [habs]
      field_simp [ne_of_gt hpi]

/-! ### Exact endpoint value -/

def endpointPrimitive (c t : ℝ) : ℂ :=
  (Real.arctan (t / c) : ℂ) -
    Complex.I * (((2 : ℂ)⁻¹) * (Real.log (c ^ 2 + t ^ 2) : ℂ))

theorem hasDerivAt_endpointPrimitive {c t : ℝ} (hc : 0 < c) :
    HasDerivAt (endpointPrimitive c) (verticalIntegrand 1 c t) t := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have hden : c ^ 2 + t ^ 2 ≠ 0 := by positivity
  have hatanR : HasDerivAt (fun u : ℝ => Real.arctan (u / c))
      (c / (c ^ 2 + t ^ 2)) t := by
    convert (Real.hasDerivAt_arctan (t / c)).comp t
      ((hasDerivAt_id t).div_const c) using 1
    field_simp [hc0]
  have hquad : HasDerivAt (fun u : ℝ => c ^ 2 + u ^ 2) (2 * t) t := by
    convert (hasDerivAt_const t (c ^ 2)).add ((hasDerivAt_id t).pow 2) using 1
    simp [two_mul]
  have hlogR : HasDerivAt (fun u : ℝ => (2 : ℝ)⁻¹ * Real.log (c ^ 2 + u ^ 2))
      (t / (c ^ 2 + t ^ 2)) t := by
    convert ((Real.hasDerivAt_log hden).comp t hquad).const_mul (2 : ℝ)⁻¹ using 1
    field_simp [hden]
  have hatanC := hatanR.ofReal_comp
  have hlogC := hlogR.ofReal_comp
  have hprim0 : HasDerivAt (endpointPrimitive c)
      (((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) -
        Complex.I * ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) t := by
    simpa [endpointPrimitive, Complex.ofReal_mul] using
      hatanC.sub ((hasDerivAt_const t Complex.I).mul hlogC)
  have heq : (((c / (c ^ 2 + t ^ 2) : ℝ) : ℂ) -
        Complex.I * ((t / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      Complex.mk (c / (c ^ 2 + t ^ 2)) (-t / (c ^ 2 + t ^ 2)) := by
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero]
    · simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, zero_sub, neg_div]
  rw [heq] at hprim0
  convert hprim0 using 1
  have hone : verticalPower 1 c t = 1 := by simp [verticalPower]
  rw [verticalIntegrand, hone]
  apply Complex.ext <;> simp [Complex.normSq_apply]
  · field_simp [hden]
  · field_simp [hden]

theorem integral_verticalIntegrand_one {c T : ℝ} (hc : 0 < c) :
    (∫ t in (-T)..T, verticalIntegrand 1 c t) =
      endpointPrimitive c T - endpointPrimitive c (-T) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_endpointPrimitive hc
  · exact intervalIntegrable_verticalIntegrand hc

/-- At the integer endpoint the vertical segment is exactly
`atan(T/c)/pi`; it is neither the strict weight zero nor the inclusive weight
one. -/
theorem kernel_one_eq_arctan {c T : ℝ} (hc : 0 < c) :
    kernel 1 c T = (Real.arctan (T / c) / Real.pi : ℝ) := by
  rw [kernel, integral_verticalIntegrand_one hc]
  simp only [endpointPrimitive, neg_sq]
  push_cast
  rw [show -T / c = -(T / c) by ring, Real.arctan_neg]
  have hcastneg : ((-Real.arctan (T / c) : ℝ) : ℂ) =
      -(Real.arctan (T / c) : ℂ) := by norm_num
  rw [hcastneg]
  field_simp [ne_of_gt Real.pi_pos]
  ring

/-! ### Arithmetic distance from the logarithmic singularity -/

/-- The exact elementary bridge from the Perron logarithmic denominator to
arithmetic distance. -/
theorem abs_log_div_ge_abs_sub_div_max {x n : ℝ} (hx : 0 < x) (hn : 0 < n) :
    |Real.log (x / n)| ≥ |x - n| / max x n := by
  rcases le_total x n with hxn | hnx
  · rw [max_eq_right hxn]
    have hratio_pos : 0 < x / n := div_pos hx hn
    have hratio_le : x / n ≤ 1 := (div_le_one hn).2 hxn
    rw [abs_of_nonpos (Real.log_nonpos hratio_pos.le hratio_le)]
    have hlogswap : -Real.log (x / n) = Real.log (n / x) := by
      rw [Real.log_div hx.ne' hn.ne', Real.log_div hn.ne' hx.ne']
      ring
    rw [hlogswap, abs_of_nonpos (sub_nonpos.mpr hxn)]
    have hbase := Real.one_sub_inv_le_log_of_pos (div_pos hn hx)
    rw [inv_div, one_sub_div hn.ne'] at hbase
    simpa only [neg_div, neg_sub] using hbase
  · rw [max_eq_left hnx]
    have hratio_ge : 1 ≤ x / n := (le_div_iff₀ hn).2 (by simpa using hnx)
    rw [abs_of_nonneg (Real.log_nonneg hratio_ge),
      abs_of_nonneg (sub_nonneg.mpr hnx)]
    have hbase := Real.one_sub_inv_le_log_of_pos (div_pos hx hn)
    rw [inv_div, one_sub_div hx.ne'] at hbase
    exact hbase

/-- A half-integer Perron boundary stays at least `1/2` from every natural
index.  This removes the endpoint singularity without a genericity
assumption. -/
theorem halfInteger_nat_distance (N n : ℕ) :
    (1 / 2 : ℝ) ≤ |((N : ℝ) + 1 / 2) - (n : ℝ)| := by
  by_cases h : n ≤ N
  · have hc : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have h' : N + 1 ≤ n := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge h)
    have hc : ((N + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h'
    rw [abs_of_nonpos (by norm_num at hc ⊢; linarith)]
    norm_num at hc ⊢
    linarith

/-- A uniform bound which remains valid at `y = 1`.  It deliberately exposes
the `T/c` growth of the crude absolute-value estimate; oscillatory improvement
away from `y = 1` is a separate theorem. -/
theorem norm_kernel_le {y c T : ℝ} (hy : 0 < y) (hc : 0 < c) (hT : 0 ≤ T) :
    ‖kernel y c T‖ ≤ y ^ c * T / (Real.pi * c) := by
  rw [kernel, norm_mul]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hconst : norm (((2 * Real.pi : ℝ) : ℂ)⁻¹) = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  have hint : ‖∫ t in (-T)..T, verticalIntegrand y c t‖ ≤
      (y ^ c / c) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => norm_verticalIntegrand_le hy hc)
  calc
    (2 * Real.pi)⁻¹ * ‖∫ t in (-T)..T, verticalIntegrand y c t‖
        ≤ (2 * Real.pi)⁻¹ * ((y ^ c / c) * |T - (-T)|) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (mul_nonneg (by norm_num) hpi.le))
    _ = y ^ c * T / (Real.pi * c) := by
      have habs : |T - (-T)| = 2 * T := by
        rw [sub_neg_eq_add, ← two_mul, abs_of_nonneg (mul_nonneg (by norm_num) hT)]
      rw [habs]
      field_simp [ne_of_gt hpi, ne_of_gt hc]

/-- A finite Dirichlet polynomial on the Perron line.  The ratio is kept as a
positive real base, so no logarithm branch or integer coercion is hidden. -/
def finitePerronPolynomial {N : Type*} (S : Finset N) (a : N → ℂ)
    (ratio : N → ℝ) (c t : ℝ) : ℂ :=
  ∑ n ∈ S, a n * verticalIntegrand (ratio n) c t

/-- Exact finite-sum/vertical-integral interchange.  This is the algebraic
kernel of truncated Perron for a finite Dirichlet polynomial, with no error
term and no appeal to an infinite Dirichlet series. -/
theorem kernel_finset_sum {N : Type*} (S : Finset N) (a : N → ℂ)
    (ratio : N → ℝ) {c T : ℝ} (hc : 0 < c) :
    (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        ∫ t in (-T)..T, finitePerronPolynomial S a ratio c t) =
      ∑ n ∈ S, a n * kernel (ratio n) c T := by
  classical
  simp only [finitePerronPolynomial]
  have hi : ∀ n ∈ S, IntervalIntegrable
      (fun t => a n * verticalIntegrand (ratio n) c t) volume (-T) T := by
    intro n hn
    exact (intervalIntegrable_verticalIntegrand hc).const_mul _
  rw [intervalIntegral.integral_finsetSum (s := S) hi]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul, kernel]
  ring

/-- Quantitative coefficient bound for the exact finite Perron polynomial.
It is uniform in the index type and therefore applies directly to twisted
Mangoldt coefficients once `ratio n = x/n` and positivity are supplied. -/
theorem norm_integral_finitePerronPolynomial_le {N : Type*} (S : Finset N)
    (a : N → ℂ) (ratio : N → ℝ) {c T : ℝ}
    (hratio : ∀ n ∈ S, 0 < ratio n) (hc : 0 < c) (hT : 0 ≤ T) :
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
        (∫ t in (-T)..T, finitePerronPolynomial S a ratio c t)) ≤
      ∑ n ∈ S, ‖a n‖ * ((ratio n) ^ c * T / (Real.pi * c)) := by
  rw [kernel_finset_sum S a ratio hc]
  calc
    ‖∑ n ∈ S, a n * kernel (ratio n) c T‖
        ≤ ∑ n ∈ S, ‖a n * kernel (ratio n) c T‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖a n‖ * ((ratio n) ^ c * T / (Real.pi * c)) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_kernel_le (hratio n hn) hc hT) (norm_nonneg _)

/-- Finite-polynomial near-integer estimate.  Every parameter remains
visible: if a ratio lies in the `1/T` transition band, its contribution is
controlled relative to the exact endpoint weight `atan(T/c)/pi`, rather than
being incorrectly rounded to zero or one. -/
theorem norm_finitePerron_sub_endpoint_le {N : Type*} (S : Finset N)
    (a : N → ℂ) (ratio : N → ℝ) {c T : ℝ}
    (hratio : ∀ n ∈ S, 0 < ratio n) (hc : 0 < c) (hT : 0 ≤ T)
    (hnear : ∀ n ∈ S, |Real.log (ratio n)| * (c + T) ≤ 1) :
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ t in (-T)..T, finitePerronPolynomial S a ratio c t) -
        kernel 1 c T * ∑ n ∈ S, a n) ≤
      ∑ n ∈ S, ‖a n‖ *
        (2 * T * |Real.log (ratio n)| / Real.pi) := by
  rw [kernel_finset_sum S a ratio hc, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    norm (∑ n ∈ S, (a n * kernel (ratio n) c T - kernel 1 c T * a n))
        ≤ ∑ n ∈ S,
          norm (a n * kernel (ratio n) c T - kernel 1 c T * a n) := norm_sum_le _ _
    _ ≤ ∑ n ∈ S, ‖a n‖ *
        (2 * T * |Real.log (ratio n)| / Real.pi) := by
      apply Finset.sum_le_sum
      intro n hn
      rw [mul_comm (kernel 1 c T) (a n), ← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (norm_kernel_sub_one_le (hratio n hn) hc hT (hnear n hn)) (norm_nonneg _)

/-- The preceding endpoint-centered theorem with the endpoint evaluated
exactly. -/
theorem norm_finitePerron_sub_arctan_weight_le {N : Type*} (S : Finset N)
    (a : N → ℂ) (ratio : N → ℝ) {c T : ℝ}
    (hratio : ∀ n ∈ S, 0 < ratio n) (hc : 0 < c) (hT : 0 ≤ T)
    (hnear : ∀ n ∈ S, |Real.log (ratio n)| * (c + T) ≤ 1) :
    norm (((2 * Real.pi : ℝ) : ℂ)⁻¹ *
          (∫ t in (-T)..T, finitePerronPolynomial S a ratio c t) -
        ((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) * ∑ n ∈ S, a n) ≤
      ∑ n ∈ S, ‖a n‖ *
        (2 * T * |Real.log (ratio n)| / Real.pi) := by
  rw [← kernel_one_eq_arctan hc]
  exact norm_finitePerron_sub_endpoint_le S a ratio hratio hc hT hnear

end

end PerronKernel
