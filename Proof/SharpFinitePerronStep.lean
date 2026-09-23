import PerronKernel
import FinitePoleRectangle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Sharp finite Perron step estimate

This file formalizes, with the literal normalization of `PerronKernel.kernel`,
the full sharp finite Perron estimate obtained by closing the Perron segment to
the left or to the right.  The finite-pole rectangle theorem supplies the
residue-one identity in the left closure; the right closure is pole-free.  The
remote vertical sides vanish, and after multiplication by `(2 * pi)⁻¹` the two
horizontal rays contribute exactly the target constant `1 / pi`.  No contour
identity or quantitative estimate is assumed as a proposition.
-/

namespace SharpFinitePerronStep

set_option maxHeartbeats 800000

open Set MeasureTheory Filter
open scoped Interval

noncomputable section

/-- The meromorphic contour integrand after writing `a = log y` and
`y^s = exp (a s)`. -/
def contourIntegrand (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((a : ℂ) * z) / z

/-- The literal kernel is the normalized vertical contour integral of
`exp ((log y) * z) / z`. -/
theorem kernel_eq_contour_vertical {y c T : ℝ} (hy : 0 < y) :
    PerronKernel.kernel y c T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in (-T)..T,
          contourIntegrand (Real.log y) ((c : ℂ) + Complex.I * t) := by
  rw [PerronKernel.kernel]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [PerronKernel.verticalIntegrand, PerronKernel.verticalPower_eq_exp hy]
  simp only [contourIntegrand]
  congr 2
  ring

/-! ### The pole is literally isolated

`removablePart a` is `(exp (a*z) - 1) / z`, with its removable value filled at
zero by `dslope`.  Thus the only rectangle residue is the explicit `1/z`
term, rather than an assumed residue proposition.
-/

def removablePart (a : ℝ) : ℂ → ℂ :=
  dslope (fun z : ℂ => Complex.exp ((a : ℂ) * z)) 0

theorem differentiable_removablePart (a : ℝ) :
    Differentiable ℂ (removablePart a) := by
  have h : DifferentiableOn ℂ (removablePart a) Set.univ := by
    apply (Complex.differentiableOn_dslope
      (s := Set.univ) (c := 0) Filter.univ_mem).2
    fun_prop
  exact fun _ => h.differentiableAt Filter.univ_mem

theorem removablePart_add_inv {a : ℝ} {z : ℂ} (hz : z ≠ 0) :
    removablePart a z + z⁻¹ = contourIntegrand a z := by
  rw [removablePart, dslope_of_ne _ hz]
  simp [slope, contourIntegrand, div_eq_inv_mul]
  ring

/-- The exact oriented rectangle boundary of the removable part is zero.
This is the Cauchy-Goursat component of the Perron closure. -/
theorem removablePart_rectangle_boundary (a : ℝ) (z w : ℂ) :
    ((∫ x : ℝ in z.re..w.re,
          removablePart a (x + z.im * Complex.I)) -
        (∫ x : ℝ in z.re..w.re,
          removablePart a (x + w.im * Complex.I)) +
      Complex.I • (∫ t : ℝ in z.im..w.im,
        removablePart a (w.re + t * Complex.I)) -
      Complex.I • (∫ t : ℝ in z.im..w.im,
        removablePart a (z.re + t * Complex.I))) = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    (removablePart a) z w (differentiable_removablePart a).differentiableOn

theorem norm_contourIntegrand_horizontal_le {a sigma tau T : ℝ}
    (hT : 0 < T) (htau : T ≤ |tau|) :
    ‖contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖ ≤
      Real.exp (a * sigma) / T := by
  have hden : T ≤ ‖(sigma : ℂ) + Complex.I * tau‖ := by
    calc
      T ≤ |tau| := htau
      _ = |(((sigma : ℂ) + Complex.I * tau).im)| := by simp
      _ ≤ ‖(sigma : ℂ) + Complex.I * tau‖ := Complex.abs_im_le_norm _
  rw [contourIntegrand, norm_div, Complex.norm_exp]
  have hre : (((a : ℂ) * ((sigma : ℂ) + Complex.I * tau)).re) = a * sigma := by
    simp
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hT hden

theorem norm_contourIntegrand_left_vertical_le {a R t : ℝ}
    (hR : 0 < R) :
    ‖contourIntegrand a ((-R : ℝ) + Complex.I * t)‖ ≤
      Real.exp (-a * R) / R := by
  have hden : R ≤ ‖((-R : ℝ) : ℂ) + Complex.I * t‖ := by
    calc
      R = |(((-R : ℝ) : ℂ) + Complex.I * t).re| := by
        simp [abs_of_pos hR]
      _ ≤ ‖((-R : ℝ) : ℂ) + Complex.I * t‖ := Complex.abs_re_le_norm _
  rw [contourIntegrand, norm_div, Complex.norm_exp]
  have hre : (((a : ℂ) * (((-R : ℝ) : ℂ) + Complex.I * t)).re) = -a * R := by
    simp
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hR hden

theorem norm_contourIntegrand_right_vertical_le {a R t : ℝ}
    (hR : 0 < R) :
    ‖contourIntegrand a ((R : ℂ) + Complex.I * t)‖ ≤
      Real.exp (a * R) / R := by
  have hden : R ≤ ‖(R : ℂ) + Complex.I * t‖ := by
    calc
      R = |(((R : ℂ) + Complex.I * t).re)| := by simp [abs_of_pos hR]
      _ ≤ ‖(R : ℂ) + Complex.I * t‖ := Complex.abs_re_le_norm _
  rw [contourIntegrand, norm_div, Complex.norm_exp]
  have hre : (((a : ℂ) * ((R : ℂ) + Complex.I * t)).re) = a * R := by simp
  rw [hre]
  exact div_le_div_of_nonneg_left (Real.exp_pos _).le hR hden

def leftRemoteVertical (a R T : ℝ) : ℂ :=
  ∫ t in (-T)..T, contourIntegrand a (((-R : ℝ) : ℂ) + Complex.I * t)

def rightRemoteVertical (a R T : ℝ) : ℂ :=
  ∫ t in (-T)..T, contourIntegrand a ((R : ℂ) + Complex.I * t)

/-- Quantitative death bound for the remote vertical side of a left closure. -/
theorem norm_leftRemoteVertical_le {a R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) :
    ‖leftRemoteVertical a R T‖ ≤
      2 * T * (Real.exp (-a * R) / R) := by
  rw [leftRemoteVertical]
  have h :
      ‖∫ t in (-T)..T,
          contourIntegrand a (((-R : ℝ) : ℂ) + Complex.I * t)‖ ≤
        (Real.exp (-a * R) / R) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => norm_contourIntegrand_left_vertical_le (a := a) hR)
  have habs : |T - (-T)| = 2 * T := by
    rw [sub_neg_eq_add, ← two_mul,
      abs_of_nonneg (mul_nonneg (by norm_num) hT)]
  calc
    ‖∫ t in (-T)..T,
        contourIntegrand a (((-R : ℝ) : ℂ) + Complex.I * t)‖
        ≤ (Real.exp (-a * R) / R) * |T - (-T)| := h
    _ = 2 * T * (Real.exp (-a * R) / R) := by
      rw [habs]
      ring

/-- Quantitative death bound for the remote vertical side of a right closure. -/
theorem norm_rightRemoteVertical_le {a R T : ℝ} (hR : 0 < R) (hT : 0 ≤ T) :
    ‖rightRemoteVertical a R T‖ ≤
      2 * T * (Real.exp (a * R) / R) := by
  rw [rightRemoteVertical]
  have h :
      ‖∫ t in (-T)..T,
          contourIntegrand a ((R : ℂ) + Complex.I * t)‖ ≤
        (Real.exp (a * R) / R) * |T - (-T)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t _ => norm_contourIntegrand_right_vertical_le (a := a) hR)
  have habs : |T - (-T)| = 2 * T := by
    rw [sub_neg_eq_add, ← two_mul,
      abs_of_nonneg (mul_nonneg (by norm_num) hT)]
  calc
    ‖∫ t in (-T)..T,
        contourIntegrand a ((R : ℂ) + Complex.I * t)‖
        ≤ (Real.exp (a * R) / R) * |T - (-T)| := h
    _ = 2 * T * (Real.exp (a * R) / R) := by
      rw [habs]
      ring

/-- The remote side of a left closure vanishes; this is proved from the
literal finite-side bound, not postulated as a contour limit. -/
theorem tendsto_leftRemoteVertical_atTop_zero {a T : ℝ}
    (ha : 0 < a) (hT : 0 ≤ T) :
    Filter.Tendsto (fun R : ℝ => leftRemoteVertical a R T)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have harg : Filter.Tendsto (fun R : ℝ => (-a) * R)
      Filter.atTop Filter.atBot :=
    tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos ha)
  have hexp : Filter.Tendsto (fun R : ℝ => Real.exp ((-a) * R))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp harg
  have hinv : Filter.Tendsto (fun R : ℝ => R⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hmajor : Filter.Tendsto
      (fun R : ℝ => 2 * T * (Real.exp (-a * R) / R))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (hexp.mul hinv)) using 1
    all_goals first | rfl | simp
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_leftRemoteVertical_le hR hT
  · exact hmajor

/-- The remote side of a right closure vanishes for a negative logarithm. -/
theorem tendsto_rightRemoteVertical_atTop_zero {a T : ℝ}
    (ha : a < 0) (hT : 0 ≤ T) :
    Filter.Tendsto (fun R : ℝ => rightRemoteVertical a R T)
      Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have harg : Filter.Tendsto (fun R : ℝ => a * R)
      Filter.atTop Filter.atBot :=
    tendsto_id.const_mul_atTop_of_neg ha
  have hexp : Filter.Tendsto (fun R : ℝ => Real.exp (a * R))
      Filter.atTop (nhds 0) := Real.tendsto_exp_atBot.comp harg
  have hinv : Filter.Tendsto (fun R : ℝ => R⁻¹)
      Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hmajor : Filter.Tendsto
      (fun R : ℝ => 2 * T * (Real.exp (a * R) / R))
      Filter.atTop (nhds 0) := by
    convert (tendsto_const_nhds.mul (hexp.mul hinv)) using 1
    all_goals first | rfl | simp
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun R => norm_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact norm_rightRemoteVertical_le hR hT
  · exact hmajor

/-! ### Exact finite rectangles and their improper limits -/

/-- Both improper horizontal rays in the left closure, with exact rectangle
orientation. -/
def leftHorizontalPair (a c T : ℝ) : ℂ :=
  (∫ sigma : ℝ in Iic c,
      contourIntegrand a ((sigma : ℂ) - Complex.I * T)) -
    ∫ sigma : ℝ in Iic c,
      contourIntegrand a ((sigma : ℂ) + Complex.I * T)

/-- Both improper horizontal rays in the right closure, with exact rectangle
orientation. -/
def rightHorizontalPair (a c T : ℝ) : ℂ :=
  (∫ sigma : ℝ in Ioi c,
      contourIntegrand a ((sigma : ℂ) + Complex.I * T)) -
    ∫ sigma : ℝ in Ioi c,
      contourIntegrand a ((sigma : ℂ) - Complex.I * T)

def leftHorizontalFinite (a c T R : ℝ) : ℂ :=
  (∫ sigma in (-R)..c,
      contourIntegrand a ((sigma : ℂ) - Complex.I * T)) -
    ∫ sigma in (-R)..c,
      contourIntegrand a ((sigma : ℂ) + Complex.I * T)

def rightHorizontalFinite (a c T R : ℝ) : ℂ :=
  (∫ sigma in c..R,
      contourIntegrand a ((sigma : ℂ) + Complex.I * T)) -
    ∫ sigma in c..R,
      contourIntegrand a ((sigma : ℂ) - Complex.I * T)

theorem left_boundary_expansion (a c T R : ℝ) :
    FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) (-R) c (-T) T =
      leftHorizontalFinite a c T R +
        Complex.I * (∫ t in (-T)..T,
          contourIntegrand a ((c : ℂ) + Complex.I * t)) -
        Complex.I * leftRemoteVertical a R T := by
  have hbot :
      (∫ x in (-R)..c,
        contourIntegrand a ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) =
      ∫ x in (-R)..c,
        contourIntegrand a ((x : ℂ) - Complex.I * T) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (contourIntegrand a) (by push_cast; ring)
  have hvis : ∀ d : ℝ,
      (∫ x in (-T)..T,
        contourIntegrand a ((d : ℂ) + (x : ℂ) * Complex.I)) =
      ∫ x in (-T)..T,
        contourIntegrand a ((d : ℂ) + Complex.I * x) := by
    intro d
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (contourIntegrand a) (mul_comm (x : ℂ) Complex.I ▸ rfl)
  unfold FinitePoleRectangle.rectangleBoundaryIntegral
    leftHorizontalFinite leftRemoteVertical
  rw [hbot, hvis c, hvis (-R)]
  simp [sub_eq_add_neg, add_comm, mul_comm]

theorem right_boundary_expansion (a c T R : ℝ) :
    FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) c R (-T) T =
      -rightHorizontalFinite a c T R +
        Complex.I * rightRemoteVertical a R T -
        Complex.I * (∫ t in (-T)..T,
          contourIntegrand a ((c : ℂ) + Complex.I * t)) := by
  have hbot :
      (∫ x in c..R,
        contourIntegrand a ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) =
      ∫ x in c..R,
        contourIntegrand a ((x : ℂ) - Complex.I * T) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (contourIntegrand a) (by push_cast; ring)
  have hvis : ∀ d : ℝ,
      (∫ x in (-T)..T,
        contourIntegrand a ((d : ℂ) + (x : ℂ) * Complex.I)) =
      ∫ x in (-T)..T,
        contourIntegrand a ((d : ℂ) + Complex.I * x) := by
    intro d
    apply intervalIntegral.integral_congr
    intro x hx
    exact congrArg (contourIntegrand a) (mul_comm (x : ℂ) Complex.I ▸ rfl)
  unfold FinitePoleRectangle.rectangleBoundaryIntegral
    rightHorizontalFinite rightRemoteVertical
  rw [hbot, hvis R, hvis c]
  simp [sub_eq_add_neg, add_comm, mul_comm]

theorem integrableOn_horizontal_Iic
    {a c T tau : ℝ} (ha : 0 < a) (hT : 0 < T)
    (htau : T ≤ |tau|) :
    IntegrableOn (fun sigma : ℝ =>
      contourIntegrand a ((sigma : ℂ) + Complex.I * tau)) (Iic c) := by
  have hmajor : IntegrableOn (fun sigma : ℝ => Real.exp (a * sigma) / T) (Iic c) :=
    (integrableOn_exp_mul_Iic ha c).div_const T
  have hcont : Continuous (fun sigma : ℝ =>
      contourIntegrand a ((sigma : ℂ) + Complex.I * tau)) := by
    unfold contourIntegrand
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro sigma hz
    have him := congrArg Complex.im hz
    have htau0 : tau ≠ 0 := abs_pos.mp (lt_of_lt_of_le hT htau)
    exact htau0 (by simpa using him)
  apply Integrable.mono' hmajor hcont.aestronglyMeasurable.restrict
  exact Filter.Eventually.of_forall fun sigma =>
    norm_contourIntegrand_horizontal_le hT htau

theorem integrableOn_horizontal_Ioi
    {a c T tau : ℝ} (ha : a < 0) (hT : 0 < T)
    (htau : T ≤ |tau|) :
    IntegrableOn (fun sigma : ℝ =>
      contourIntegrand a ((sigma : ℂ) + Complex.I * tau)) (Ioi c) := by
  have hmajor : IntegrableOn (fun sigma : ℝ => Real.exp (a * sigma) / T) (Ioi c) :=
    (integrableOn_exp_mul_Ioi ha c).div_const T
  have hcont : Continuous (fun sigma : ℝ =>
      contourIntegrand a ((sigma : ℂ) + Complex.I * tau)) := by
    unfold contourIntegrand
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro sigma hz
    have him := congrArg Complex.im hz
    have htau0 : tau ≠ 0 := abs_pos.mp (lt_of_lt_of_le hT htau)
    exact htau0 (by simpa using him)
  apply Integrable.mono' hmajor hcont.aestronglyMeasurable.restrict
  exact Filter.Eventually.of_forall fun sigma =>
    norm_contourIntegrand_horizontal_le hT htau

theorem tendsto_leftHorizontalFinite
    {a c T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    Tendsto (fun R : ℝ => leftHorizontalFinite a c T R) atTop
      (nhds (leftHorizontalPair a c T)) := by
  have hminus : T ≤ |-T| := by simpa using le_abs_self T
  have hplus : T ≤ |T| := le_abs_self T
  have hlo := MeasureTheory.intervalIntegral_tendsto_integral_Iic c
    (integrableOn_horizontal_Iic ha hT hminus)
    tendsto_neg_atTop_atBot
  have hhi := MeasureTheory.intervalIntegral_tendsto_integral_Iic c
    (integrableOn_horizontal_Iic ha hT hplus)
    tendsto_neg_atTop_atBot
  simpa [leftHorizontalFinite, leftHorizontalPair, sub_eq_add_neg] using hlo.sub hhi

theorem tendsto_rightHorizontalFinite
    {a c T : ℝ} (ha : a < 0) (hT : 0 < T) :
    Tendsto (fun R : ℝ => rightHorizontalFinite a c T R) atTop
      (nhds (rightHorizontalPair a c T)) := by
  have hplus : T ≤ |T| := le_abs_self T
  have hminus : T ≤ |-T| := by simpa using le_abs_self T
  have hhi := MeasureTheory.intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_horizontal_Ioi ha hT hplus) tendsto_id
  have hlo := MeasureTheory.intervalIntegral_tendsto_integral_Ioi c
    (integrableOn_horizontal_Ioi ha hT hminus) tendsto_id
  simpa [rightHorizontalFinite, rightHorizontalPair, sub_eq_add_neg] using hhi.sub hlo

private theorem horizontal_ne_zero {x T : ℝ} (hT : 0 < T) (sgn : ℝ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    (x : ℂ) + (sgn * T : ℝ) * Complex.I ≠ 0 := by
  intro hz
  have hi := congrArg Complex.im hz
  rcases hsgn with rfl | rfl <;> simp at hi <;> linarith

private theorem vertical_ne_zero {x t : ℝ} (hx : x ≠ 0) :
    (x : ℂ) + (t : ℂ) * Complex.I ≠ 0 := by
  intro hz
  have hr := congrArg Complex.re hz
  simpa using hx (by simpa using hr)

/-- The literal contour integrand has residue one at zero, so every positive
left rectangle has boundary integral `2*pi*I`. -/
theorem left_contour_boundary_eq_two_pi_I {a R c T : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hT : 0 < T) :
    FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) (-R) c (-T) T =
      2 * Real.pi * Complex.I := by
  let r : ℝ := min R (min c T) / 2
  have hm : 0 < min R (min c T) := lt_min hR (lt_min hc hT)
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by
    have hle : min R (min c T) ≤ R := min_le_left _ _
    dsimp [r]
    linarith
  have hrc : r < c := by
    have hle : min R (min c T) ≤ c :=
      (min_le_right R (min c T)).trans (min_le_left c T)
    dsimp [r]
    linarith
  have hrT : r < T := by
    have hle : min R (min c T) ≤ T :=
      (min_le_right R (min c T)).trans (min_le_right c T)
    dsimp [r]
    linarith
  let S : Finset Unit := {()}
  let pole : Unit → ℂ := fun _ => 0
  let residue : Unit → ℂ := fun _ => 1
  let radius : Unit → ℝ := fun _ => r
  have hgdiff : DifferentiableOn ℂ (removablePart a)
      (uIcc (-R) c ×ℂ uIcc (-T) T) :=
    (differentiable_removablePart a).differentiableOn
  have hres :=
    FinitePoleRectangle.rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
      S pole residue radius (contourIntegrand a) (removablePart a)
        (-R) c (-T) T
        (by intro i hi; simp [radius, hr])
        (by intro i hi; simp [pole, radius]; linarith)
        (by intro i hi; simp [pole, radius]; linarith)
        (by intro i hi; simp [pole, radius]; linarith)
        (by intro i hi; simp [pole, radius]; linarith)
        (FinitePoleRectangle.boundaryIntervalIntegrable_of_differentiableOn hgdiff)
        hgdiff
        (by
          intro x
          have hz : (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I ≠ 0 := by
            simpa using (horizontal_ne_zero (x := x) hT (-1) (Or.inr rfl))
          simpa [S, pole, residue] using
            (removablePart_add_inv (a := a) hz).symm)
        (by
          intro x
          have hz : (x : ℂ) + (T : ℂ) * Complex.I ≠ 0 := by
            simpa using (horizontal_ne_zero (x := x) hT 1 (Or.inl rfl))
          simpa [S, pole, residue] using
            (removablePart_add_inv (a := a) hz).symm)
        (by
          intro y
          have hz : (c : ℂ) + (y : ℂ) * Complex.I ≠ 0 :=
            vertical_ne_zero hc.ne'
          simpa [S, pole, residue] using
            (removablePart_add_inv (a := a) hz).symm)
        (by
          intro y
          have hz : ((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I ≠ 0 :=
            vertical_ne_zero (neg_ne_zero.mpr hR.ne')
          simpa [S, pole, residue] using
            (removablePart_add_inv (a := a) hz).symm)
  simpa [S, residue] using hres

/-- A positive right rectangle excludes zero, so the literal contour boundary
integral vanishes. -/
theorem right_contour_boundary_eq_zero {a c R T : ℝ}
    (hc : 0 < c) (hcR : c ≤ R) :
    FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) c R (-T) T = 0 := by
  apply FinitePoleRectangle.rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  have hzmem := Complex.mem_reProdIm.mp hz
  rw [Set.uIcc_of_le hcR] at hzmem
  have hz0 : z ≠ 0 := by
    intro hzero
    have : c ≤ 0 := by simpa [hzero] using hzmem.1.1
    linarith
  apply DifferentiableAt.differentiableWithinAt
  unfold contourIntegrand
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact hz0

private theorem solve_left_boundary {L V VR : ℂ}
    (h : L + Complex.I * V - Complex.I * VR =
      2 * Real.pi * Complex.I) :
    V = ((2 * Real.pi : ℝ) : ℂ) + Complex.I * L + VR := by
  have hIV : Complex.I * V =
      2 * Real.pi * Complex.I - L + Complex.I * VR := by
    linear_combination h
  calc
    V = -Complex.I * (Complex.I * V) := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]
      ring
    _ = -Complex.I *
        (2 * Real.pi * Complex.I - L + Complex.I * VR) := by rw [hIV]
    _ = ((2 * Real.pi : ℝ) : ℂ) + Complex.I * L + VR := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring

private theorem solve_right_boundary {H V VR : ℂ}
    (h : -H + Complex.I * VR - Complex.I * V = 0) :
    V = Complex.I * H + VR := by
  have hIV : Complex.I * V = -H + Complex.I * VR := by
    linear_combination -h
  calc
    V = -Complex.I * (Complex.I * V) := by
      rw [← mul_assoc, neg_mul, Complex.I_mul_I]
      ring
    _ = -Complex.I * (-H + Complex.I * VR) := by rw [hIV]
    _ = Complex.I * H + VR := by
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Closing to the left gives the exact step residue before taking norms. -/
theorem contour_vertical_eq_two_pi_add_I_mul_leftHorizontalPair
    {a c T : ℝ} (ha : 0 < a) (hc : 0 < c) (hT : 0 < T) :
    (∫ t in (-T)..T,
        contourIntegrand a ((c : ℂ) + Complex.I * t)) =
      ((2 * Real.pi : ℝ) : ℂ) +
        Complex.I * leftHorizontalPair a c T := by
  let V : ℂ := ∫ t in (-T)..T,
    contourIntegrand a ((c : ℂ) + Complex.I * t)
  have hfinite : ∀ᶠ R : ℝ in atTop,
      V = ((2 * Real.pi : ℝ) : ℂ) +
        Complex.I * leftHorizontalFinite a c T R +
        leftRemoteVertical a R T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    apply solve_left_boundary
    have hexpand := left_boundary_expansion a c T R
    have hres := left_contour_boundary_eq_two_pi_I (a := a) hR hc hT
    change FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) (-R) c (-T) T =
      leftHorizontalFinite a c T R + Complex.I * V -
        Complex.I * leftRemoteVertical a R T at hexpand
    exact hexpand.symm.trans hres
  have hconst : Tendsto (fun _ : ℝ => V) atTop (nhds V) := tendsto_const_nhds
  have heq : Tendsto
      (fun R : ℝ => ((2 * Real.pi : ℝ) : ℂ) +
        Complex.I * leftHorizontalFinite a c T R +
        leftRemoteVertical a R T) atTop (nhds V) :=
    Filter.Tendsto.congr' hfinite hconst
  have hlimit : Tendsto
      (fun R : ℝ => ((2 * Real.pi : ℝ) : ℂ) +
        Complex.I * leftHorizontalFinite a c T R +
        leftRemoteVertical a R T) atTop
      (nhds (((2 * Real.pi : ℝ) : ℂ) +
        Complex.I * leftHorizontalPair a c T + 0)) :=
    (tendsto_const_nhds.add
      (tendsto_const_nhds.mul (tendsto_leftHorizontalFinite ha hT))).add
        (tendsto_leftRemoteVertical_atTop_zero ha hT.le)
  have hvalue := tendsto_nhds_unique heq hlimit
  simpa [V] using hvalue

/-- Closing to the right gives the exact zero-step identity before norms. -/
theorem contour_vertical_eq_I_mul_rightHorizontalPair
    {a c T : ℝ} (ha : a < 0) (hc : 0 < c) (hT : 0 < T) :
    (∫ t in (-T)..T,
        contourIntegrand a ((c : ℂ) + Complex.I * t)) =
      Complex.I * rightHorizontalPair a c T := by
  let V : ℂ := ∫ t in (-T)..T,
    contourIntegrand a ((c : ℂ) + Complex.I * t)
  have hfinite : ∀ᶠ R : ℝ in atTop,
      V = Complex.I * rightHorizontalFinite a c T R +
        rightRemoteVertical a R T := by
    filter_upwards [eventually_ge_atTop c] with R hcR
    apply solve_right_boundary
    have hexpand := right_boundary_expansion a c T R
    have hzero := right_contour_boundary_eq_zero (a := a) (T := T) hc hcR
    change FinitePoleRectangle.rectangleBoundaryIntegral
        (contourIntegrand a) c R (-T) T =
      -rightHorizontalFinite a c T R +
        Complex.I * rightRemoteVertical a R T - Complex.I * V at hexpand
    exact hexpand.symm.trans hzero
  have hconst : Tendsto (fun _ : ℝ => V) atTop (nhds V) := tendsto_const_nhds
  have heq : Tendsto
      (fun R : ℝ => Complex.I * rightHorizontalFinite a c T R +
        rightRemoteVertical a R T) atTop (nhds V) :=
    Filter.Tendsto.congr' hfinite hconst
  have hlimit : Tendsto
      (fun R : ℝ => Complex.I * rightHorizontalFinite a c T R +
        rightRemoteVertical a R T) atTop
      (nhds (Complex.I * rightHorizontalPair a c T + 0)) :=
    (tendsto_const_nhds.mul (tendsto_rightHorizontalFinite ha hT)).add
      (tendsto_rightRemoteVertical_atTop_zero ha hT.le)
  have hvalue := tendsto_nhds_unique heq hlimit
  simpa [V] using hvalue

/-- A single horizontal ray in the left closure (`a > 0`) has sharp norm
`exp (a*c) / (a*T)`. -/
theorem norm_left_horizontal_ray_le {a c tau T : ℝ}
    (ha : 0 < a) (hT : 0 < T) (htau : T ≤ |tau|) :
    ‖∫ sigma : ℝ in Iic c,
        contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖ ≤
      Real.exp (a * c) / (a * T) := by
  have hmajor : IntegrableOn (fun sigma : ℝ => Real.exp (a * sigma) / T) (Iic c) :=
    (integrableOn_exp_mul_Iic ha c).div_const T
  have hbound : ∀ᵐ sigma : ℝ ∂((volume : Measure ℝ).restrict (Iic c)),
      ‖contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖ ≤
        Real.exp (a * sigma) / T :=
    Filter.Eventually.of_forall fun sigma =>
      norm_contourIntegrand_horizontal_le hT htau
  calc
    ‖∫ sigma : ℝ in Iic c,
        contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖
        ≤ ∫ sigma : ℝ in Iic c, Real.exp (a * sigma) / T :=
          norm_integral_le_of_norm_le hmajor hbound
    _ = Real.exp (a * c) / (a * T) := by
      rw [MeasureTheory.integral_div, integral_exp_mul_Iic ha c]
      field_simp [ne_of_gt ha, ne_of_gt hT]

/-- After the Perron normalization, the left horizontal pair has exactly the
source-faithful constant `1/pi`. -/
theorem norm_normalized_leftHorizontalPair_le {a c T : ℝ}
    (ha : 0 < a) (hT : 0 < T) :
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) * leftHorizontalPair a c T‖ ≤
      Real.exp (a * c) / (Real.pi * T * a) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hminus : T ≤ |-T| := by simpa using le_abs_self T
  have hplus : T ≤ |T| := le_abs_self T
  have hlo := norm_left_horizontal_ray_le (c := c) ha hT hminus
  have hhi := norm_left_horizontal_ray_le (c := c) ha hT hplus
  rw [norm_mul]
  have hconst : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  calc
    (2 * Real.pi)⁻¹ * ‖leftHorizontalPair a c T‖
        ≤ (2 * Real.pi)⁻¹ *
            (‖∫ sigma : ℝ in Iic c,
                contourIntegrand a ((sigma : ℂ) - Complex.I * T)‖ +
              ‖∫ sigma : ℝ in Iic c,
                contourIntegrand a ((sigma : ℂ) + Complex.I * T)‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact norm_sub_le _ _
          · positivity
    _ ≤ (2 * Real.pi)⁻¹ *
          (Real.exp (a * c) / (a * T) + Real.exp (a * c) / (a * T)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add (by simpa [sub_eq_add_neg, mul_neg] using hlo) hhi
    _ = Real.exp (a * c) / (Real.pi * T * a) := by
      field_simp [ne_of_gt ha, ne_of_gt hT, ne_of_gt hpi]
      ring

/-- The left-ray estimate in the literal source variables. -/
theorem norm_normalized_leftHorizontalPair_log_le {y c T : ℝ}
    (hy : 1 < y) (hT : 0 < T) :
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        leftHorizontalPair (Real.log y) c T‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  have hy0 : 0 < y := lt_trans zero_lt_one hy
  have hlog : 0 < Real.log y := Real.log_pos hy
  simpa [Real.rpow_def_of_pos hy0, abs_of_pos hlog, mul_comm] using
    (norm_normalized_leftHorizontalPair_le (c := c) hlog hT)

/-- A single horizontal ray in the right closure (`a < 0`) has sharp norm
`exp (a*c) / ((-a)*T)`. -/
theorem norm_right_horizontal_ray_le {a c tau T : ℝ}
    (ha : a < 0) (hT : 0 < T) (htau : T ≤ |tau|) :
    ‖∫ sigma : ℝ in Ioi c,
        contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖ ≤
      Real.exp (a * c) / ((-a) * T) := by
  have hmajor : IntegrableOn (fun sigma : ℝ => Real.exp (a * sigma) / T) (Ioi c) :=
    (integrableOn_exp_mul_Ioi ha c).div_const T
  have hbound : ∀ᵐ sigma : ℝ ∂((volume : Measure ℝ).restrict (Ioi c)),
      ‖contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖ ≤
        Real.exp (a * sigma) / T :=
    Filter.Eventually.of_forall fun sigma =>
      norm_contourIntegrand_horizontal_le hT htau
  calc
    ‖∫ sigma : ℝ in Ioi c,
        contourIntegrand a ((sigma : ℂ) + Complex.I * tau)‖
        ≤ ∫ sigma : ℝ in Ioi c, Real.exp (a * sigma) / T :=
          norm_integral_le_of_norm_le hmajor hbound
    _ = Real.exp (a * c) / ((-a) * T) := by
      rw [MeasureTheory.integral_div, integral_exp_mul_Ioi ha c]
      field_simp [ne_of_lt ha, ne_of_gt hT]

/-- After Perron normalization, the right horizontal pair also has the exact
constant `1/pi`. -/
theorem norm_normalized_rightHorizontalPair_le {a c T : ℝ}
    (ha : a < 0) (hT : 0 < T) :
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) * rightHorizontalPair a c T‖ ≤
      Real.exp (a * c) / (Real.pi * T * |a|) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hminus : T ≤ |-T| := by simpa using le_abs_self T
  have hplus : T ≤ |T| := le_abs_self T
  have hhi := norm_right_horizontal_ray_le (c := c) ha hT hplus
  have hlo := norm_right_horizontal_ray_le (c := c) ha hT hminus
  rw [norm_mul]
  have hconst : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) hpi)]
  rw [hconst]
  calc
    (2 * Real.pi)⁻¹ * ‖rightHorizontalPair a c T‖
        ≤ (2 * Real.pi)⁻¹ *
            (‖∫ sigma : ℝ in Ioi c,
                contourIntegrand a ((sigma : ℂ) + Complex.I * T)‖ +
              ‖∫ sigma : ℝ in Ioi c,
                contourIntegrand a ((sigma : ℂ) - Complex.I * T)‖) := by
          apply mul_le_mul_of_nonneg_left
          · exact norm_sub_le _ _
          · positivity
    _ ≤ (2 * Real.pi)⁻¹ *
          (Real.exp (a * c) / ((-a) * T) +
            Real.exp (a * c) / ((-a) * T)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact add_le_add hhi (by simpa [sub_eq_add_neg, mul_neg] using hlo)
    _ = Real.exp (a * c) / (Real.pi * T * |a|) := by
      rw [abs_of_neg ha]
      field_simp [ne_of_lt ha, ne_of_gt hT, ne_of_gt hpi]
      ring

/-- The right-ray estimate in the literal source variables. -/
theorem norm_normalized_rightHorizontalPair_log_le {y c T : ℝ}
    (hy0 : 0 < y) (hy1 : y < 1) (hT : 0 < T) :
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        rightHorizontalPair (Real.log y) c T‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  have hlog : Real.log y < 0 := Real.log_neg hy0 hy1
  simpa [Real.rpow_def_of_pos hy0, mul_comm] using
    (norm_normalized_rightHorizontalPair_le (c := c) hlog hT)

/-! ### The sharp finite Perron step theorem -/

theorem kernel_sub_one_eq_I_mul_leftHorizontalPair
    {y c T : ℝ} (hy : 0 < y) (hy1 : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    PerronKernel.kernel y c T - 1 =
      Complex.I * ((((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        leftHorizontalPair (Real.log y) c T) := by
  rw [kernel_eq_contour_vertical hy]
  rw [contour_vertical_eq_two_pi_add_I_mul_leftHorizontalPair
    (Real.log_pos hy1) hc hT]
  have hpi : (((2 * Real.pi : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  field_simp [hpi]
  ring

theorem kernel_eq_I_mul_rightHorizontalPair
    {y c T : ℝ} (hy : 0 < y) (hy1 : y < 1)
    (hc : 0 < c) (hT : 0 < T) :
    PerronKernel.kernel y c T =
      Complex.I * ((((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        rightHorizontalPair (Real.log y) c T) := by
  rw [kernel_eq_contour_vertical hy]
  rw [contour_vertical_eq_I_mul_rightHorizontalPair
    (Real.log_neg hy hy1) hc hT]
  ring

theorem norm_kernel_sub_one_le {y c T : ℝ} (hy1 : 1 < y)
    (hc : 0 < c) (hT : 0 < T) :
    ‖PerronKernel.kernel y c T - 1‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  have hy : 0 < y := lt_trans zero_lt_one hy1
  rw [kernel_sub_one_eq_I_mul_leftHorizontalPair hy hy1 hc hT,
    norm_mul, Complex.norm_I, one_mul]
  exact norm_normalized_leftHorizontalPair_log_le hy1 hT

theorem norm_kernel_le_of_lt_one {y c T : ℝ}
    (hy : 0 < y) (hy1 : y < 1) (hc : 0 < c) (hT : 0 < T) :
    ‖PerronKernel.kernel y c T‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  rw [kernel_eq_I_mul_rightHorizontalPair hy hy1 hc hT,
    norm_mul, Complex.norm_I, one_mul]
  exact norm_normalized_rightHorizontalPair_log_le hy hy1 hT

/-- The sharp finite-height Perron step estimate, with the literal source
kernel and the exact source-faithful constant `1/pi`. -/
theorem norm_kernel_sub_step_le {y c T : ℝ}
    (hy : 0 < y) (hc : 0 < c) (hT : 0 < T) (hy_ne : y ≠ 1) :
    ‖PerronKernel.kernel y c T -
        (if 1 < y then (1 : ℂ) else 0)‖ ≤
      y ^ c / (Real.pi * T * |Real.log y|) := by
  by_cases h : 1 < y
  · simpa [h] using norm_kernel_sub_one_le h hc hT
  · have hylt : y < 1 := lt_of_le_of_ne (le_of_not_gt h) hy_ne
    simpa [h] using norm_kernel_le_of_lt_one hy hylt hc hT

end

end SharpFinitePerronStep
