import PerronKernel
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Rectangle boundary integrals with one excised pole

This module supplies the geometric residue primitive absent from Mathlib's
rectangle Cauchy API.  The proof excises an axis-parallel square, applies
Cauchy--Goursat to the four remaining rectangles, and evaluates the inner
square from the already certified endpoint Perron integral.
-/

namespace FinitePoleRectangle

open Set MeasureTheory Complex
open scoped Interval

noncomputable section

/-- The unnormalized positively oriented boundary integral of the rectangle
`[a,b] × [u,v]`. -/
def rectangleBoundaryIntegral (f : ℂ → ℂ)
    (a b u v : ℝ) : ℂ :=
  (∫ x in a..b, f ((x : ℂ) + (u : ℂ) * Complex.I)) -
    (∫ x in a..b, f ((x : ℂ) + (v : ℂ) * Complex.I)) +
    Complex.I * (∫ y in u..v, f ((b : ℂ) + (y : ℂ) * Complex.I)) -
    Complex.I * (∫ y in u..v, f ((a : ℂ) + (y : ℂ) * Complex.I))

/-- Splitting a rectangle by a vertical line adds the two positively oriented
boundary integrals; the internal vertical edges cancel. -/
theorem rectangleBoundaryIntegral_split_vertical
    (f : ℂ → ℂ) (a m b u v : ℝ)
    (hbot₁ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (u : ℂ) * Complex.I)) volume a m)
    (hbot₂ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (u : ℂ) * Complex.I)) volume m b)
    (htop₁ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) volume a m)
    (htop₂ : IntervalIntegrable
      (fun x : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) volume m b) :
    rectangleBoundaryIntegral f a b u v =
      rectangleBoundaryIntegral f a m u v +
        rectangleBoundaryIntegral f m b u v := by
  have hbot := intervalIntegral.integral_add_adjacent_intervals hbot₁ hbot₂
  have htop := intervalIntegral.integral_add_adjacent_intervals htop₁ htop₂
  unfold rectangleBoundaryIntegral
  rw [← hbot, ← htop]
  ring

/-- Splitting a rectangle by a horizontal line adds the two positively
oriented boundary integrals; the internal horizontal edges cancel. -/
theorem rectangleBoundaryIntegral_split_horizontal
    (f : ℂ → ℂ) (a b u m v : ℝ)
    (hleft₁ : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume u m)
    (hleft₂ : IntervalIntegrable
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume m v)
    (hright₁ : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume u m)
    (hright₂ : IntervalIntegrable
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume m v) :
    rectangleBoundaryIntegral f a b u v =
      rectangleBoundaryIntegral f a b u m +
        rectangleBoundaryIntegral f a b m v := by
  have hleft := intervalIntegral.integral_add_adjacent_intervals hleft₁ hleft₂
  have hright := intervalIntegral.integral_add_adjacent_intervals hright₁ hright₂
  unfold rectangleBoundaryIntegral
  rw [← hleft, ← hright]
  ring

/-- Cauchy--Goursat in the named boundary convention. -/
theorem rectangleBoundaryIntegral_eq_zero_of_differentiableOn
    (f : ℂ → ℂ) (a b u v : ℝ)
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc u v)) :
    rectangleBoundaryIntegral f a b u v = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f ((a : ℂ) + (u : ℂ) * Complex.I)
      ((b : ℂ) + (v : ℂ) * Complex.I) (by simpa using hf)
  simpa only [rectangleBoundaryIntegral, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
    one_mul, mul_one, zero_add, smul_eq_mul] using h

/-- The reciprocal of `z-ρ` is differentiable on any rectangle not containing
`ρ`. -/
theorem rectangleBoundaryIntegral_sub_inv_eq_zero_of_not_mem
    (ρ : ℂ) (a b u v : ℝ)
    (hρ : ρ ∉ uIcc a b ×ℂ uIcc u v) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - ρ)⁻¹) a b u v = 0 := by
  apply rectangleBoundaryIntegral_eq_zero_of_differentiableOn
  intro z hz
  exact (differentiableAt_id.sub_const ρ).inv
    (sub_ne_zero.mpr fun h => hρ (h ▸ hz)) |>.differentiableWithinAt

private theorem continuous_vertical_sub_inv
    (ρ : ℂ) {a : ℝ} (ha : a ≠ ρ.re) :
    Continuous (fun y : ℝ => (((a : ℂ) + (y : ℂ) * Complex.I) - ρ)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro y h
    apply ha
    have hre := congrArg Complex.re h
    exact sub_eq_zero.mp (by simpa using hre)

private theorem continuous_horizontal_sub_inv
    (ρ : ℂ) {u : ℝ} (hu : u ≠ ρ.im) :
    Continuous (fun x : ℝ => (((x : ℂ) + (u : ℂ) * Complex.I) - ρ)⁻¹) := by
  apply Continuous.inv₀
  · fun_prop
  · intro x h
    apply hu
    have him := congrArg Complex.im h
    exact sub_eq_zero.mp (by simpa using him)

/-- The centered square integral of `1/(z-ρ)` is exactly `2πi`. -/
theorem rectangleBoundaryIntegral_sub_inv_centered_square
    (ρ : ℂ) {r : ℝ} (hr : 0 < r) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - ρ)⁻¹)
        (ρ.re - r) (ρ.re + r) (ρ.im - r) (ρ.im + r) =
      2 * Real.pi * Complex.I := by
  let J : ℂ := ∫ t in (-r)..r,
    (((r : ℂ) + Complex.I * (t : ℂ))⁻¹)
  have hJ : ((2 * Real.pi : ℝ) : ℂ)⁻¹ * J = (1 / 4 : ℝ) := by
    have hk := PerronKernel.kernel_one_eq_arctan (c := r) (T := r) hr
    rw [PerronKernel.kernel] at hk
    have hv : (fun t : ℝ => PerronKernel.verticalIntegrand 1 r t) =
        fun t : ℝ => (((r : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
      funext t
      simp [PerronKernel.verticalIntegrand, PerronKernel.verticalPower]
    rw [hv] at hk
    change ((2 * Real.pi : ℝ) : ℂ)⁻¹ * J = _ at hk
    rw [div_self hr.ne', Real.arctan_one] at hk
    have hreal : Real.pi / 4 / Real.pi = (1 / 4 : ℝ) := by
      field_simp [Real.pi_ne_zero]
    rw [hreal] at hk
    simpa using hk
  have hJval : J = ((Real.pi / 2 : ℝ) : ℂ) := by
    have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
    calc
      J = ((2 * Real.pi : ℝ) : ℂ) * ((1 / 4 : ℝ) : ℂ) :=
        (inv_mul_eq_iff_eq_mul₀ hpi).mp hJ
      _ = ((Real.pi / 2 : ℝ) : ℂ) := by
        push_cast
        ring
  have hright :
      (∫ y in (ρ.im - r)..(ρ.im + r),
        ((((ρ.re + r : ℝ) : ℂ) + (y : ℂ) * Complex.I) - ρ)⁻¹) = J := by
    rw [show ρ.im - r = -r + ρ.im by ring]
    rw [show ρ.im + r = r + ρ.im by ring]
    rw [← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ((((ρ.re + r : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ρ)⁻¹)
      ρ.im]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [J]
    congr 1
    apply Complex.ext <;> simp <;> ring
  have hleft :
      (∫ y in (ρ.im - r)..(ρ.im + r),
        ((((ρ.re - r : ℝ) : ℂ) + (y : ℂ) * Complex.I) - ρ)⁻¹) = -J := by
    rw [show ρ.im - r = -r + ρ.im by ring]
    rw [show ρ.im + r = r + ρ.im by ring]
    rw [← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ((((ρ.re - r : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ρ)⁻¹)
      ρ.im]
    have hcomp := intervalIntegral.integral_comp_neg
      (a := -r) (b := r)
      (fun t : ℝ =>
        ((((ρ.re - r : ℝ) : ℂ) + ((t + ρ.im : ℝ) : ℂ) * Complex.I) - ρ)⁻¹)
    simp only [neg_neg] at hcomp
    rw [← hcomp]
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [J]
    have hcenter :
        ((ρ.re - r : ℝ) : ℂ) + ((-t + ρ.im : ℝ) : ℂ) * Complex.I - ρ =
          -((r : ℂ) + Complex.I * (t : ℂ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [hcenter, inv_neg]
  have hbottom :
      (∫ x in (ρ.re - r)..(ρ.re + r),
        ((((x : ℝ) : ℂ) + ((ρ.im - r : ℝ) : ℂ) * Complex.I) - ρ)⁻¹) =
        Complex.I * J := by
    rw [show ρ.re - r = -r + ρ.re by ring]
    rw [show ρ.re + r = r + ρ.re by ring]
    rw [← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ((((t : ℝ) : ℂ) + ((ρ.im - r : ℝ) : ℂ) * Complex.I) - ρ)⁻¹)
      ρ.re]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [J]
    have hden : (r : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
      exact PerronKernel.denominator_ne_zero hr
    have hcenter :
        ((t + ρ.re : ℝ) : ℂ) + ((ρ.im - r : ℝ) : ℂ) * Complex.I - ρ =
          -Complex.I * ((r : ℂ) + Complex.I * (t : ℂ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [hcenter]
    field_simp
    simp [Complex.I_sq]
  have htop :
      (∫ x in (ρ.re - r)..(ρ.re + r),
        ((((x : ℝ) : ℂ) + ((ρ.im + r : ℝ) : ℂ) * Complex.I) - ρ)⁻¹) =
        -Complex.I * J := by
    rw [show ρ.re - r = -r + ρ.re by ring]
    rw [show ρ.re + r = r + ρ.re by ring]
    rw [← intervalIntegral.integral_comp_add_right
      (fun t : ℝ => ((((t : ℝ) : ℂ) + ((ρ.im + r : ℝ) : ℂ) * Complex.I) - ρ)⁻¹)
      ρ.re]
    have hcomp := intervalIntegral.integral_comp_neg
      (a := -r) (b := r)
      (fun t : ℝ =>
        ((((t + ρ.re : ℝ) : ℂ) + ((ρ.im + r : ℝ) : ℂ) * Complex.I) - ρ)⁻¹)
    simp only [neg_neg] at hcomp
    rw [← hcomp]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [J]
    have hden : (r : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
      exact PerronKernel.denominator_ne_zero hr
    have hcenter :
        ((-t + ρ.re : ℝ) : ℂ) + ((ρ.im + r : ℝ) : ℂ) * Complex.I - ρ =
          Complex.I * ((r : ℂ) + Complex.I * (t : ℂ)) := by
      apply Complex.ext <;> simp <;> ring
    rw [hcenter]
    field_simp
    simp [Complex.I_sq]
  unfold rectangleBoundaryIntegral
  rw [hright, hleft, hbottom, htop, hJval]
  push_cast
  ring

/-- If `ρ` lies strictly inside the rectangle, the rectangle boundary integral
of `1 / (z - ρ)` is `2πi`.  The proof is the literal square-excision proof:
the outer rectangle is split into four pole-free rectangles and the centered
square; all artificial edges cancel by the two splitting identities above. -/
theorem rectangleBoundaryIntegral_sub_inv_eq_two_pi_I
    (ρ : ℂ) {a b u v r : ℝ}
    (hr : 0 < r)
    (ha : a < ρ.re - r) (hb : ρ.re + r < b)
    (hu : u < ρ.im - r) (hv : ρ.im + r < v) :
    rectangleBoundaryIntegral (fun z : ℂ => (z - ρ)⁻¹) a b u v =
      2 * Real.pi * Complex.I := by
  let f : ℂ → ℂ := fun z => (z - ρ)⁻¹
  have har : a ≠ ρ.re := by linarith
  have hbr : b ≠ ρ.re := by linarith
  have hdq : ρ.im - r ≠ ρ.im := by linarith
  have hUq : ρ.im + r ≠ ρ.im := by linarith
  have hVa := continuous_vertical_sub_inv ρ har
  have hVb := continuous_vertical_sub_inv ρ hbr
  have hHd := continuous_horizontal_sub_inv ρ hdq
  have hHU := continuous_horizontal_sub_inv ρ hUq
  have hsplitOuter := rectangleBoundaryIntegral_split_horizontal f a b u
    (ρ.im - r) v
    (hVa.intervalIntegrable _ _) (hVa.intervalIntegrable _ _)
    (hVb.intervalIntegrable _ _) (hVb.intervalIntegrable _ _)
  have hsplitUpper := rectangleBoundaryIntegral_split_horizontal f a b
    (ρ.im - r) (ρ.im + r) v
    (hVa.intervalIntegrable _ _) (hVa.intervalIntegrable _ _)
    (hVb.intervalIntegrable _ _) (hVb.intervalIntegrable _ _)
  have hsplitMiddle := rectangleBoundaryIntegral_split_vertical f a
    (ρ.re - r) b (ρ.im - r) (ρ.im + r)
    (hHd.intervalIntegrable _ _) (hHd.intervalIntegrable _ _)
    (hHU.intervalIntegrable _ _) (hHU.intervalIntegrable _ _)
  have hsplitMiddleRight := rectangleBoundaryIntegral_split_vertical f
    (ρ.re - r) (ρ.re + r) b (ρ.im - r) (ρ.im + r)
    (hHd.intervalIntegrable _ _) (hHd.intervalIntegrable _ _)
    (hHU.intervalIntegrable _ _) (hHU.intervalIntegrable _ _)
  have hbottom : rectangleBoundaryIntegral f a b u (ρ.im - r) = 0 := by
    apply rectangleBoundaryIntegral_sub_inv_eq_zero_of_not_mem
    intro hz
    have hz' := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le (le_of_lt hu)] at hz'
    linarith [hz'.2.2]
  have htop : rectangleBoundaryIntegral f a b (ρ.im + r) v = 0 := by
    apply rectangleBoundaryIntegral_sub_inv_eq_zero_of_not_mem
    intro hz
    have hz' := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le (le_of_lt hv)] at hz'
    linarith [hz'.2.1]
  have hleft : rectangleBoundaryIntegral f a (ρ.re - r)
      (ρ.im - r) (ρ.im + r) = 0 := by
    apply rectangleBoundaryIntegral_sub_inv_eq_zero_of_not_mem
    intro hz
    have hz' := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le (le_of_lt ha)] at hz'
    linarith [hz'.1.2]
  have hright : rectangleBoundaryIntegral f (ρ.re + r) b
      (ρ.im - r) (ρ.im + r) = 0 := by
    apply rectangleBoundaryIntegral_sub_inv_eq_zero_of_not_mem
    intro hz
    have hz' := Complex.mem_reProdIm.mp hz
    rw [Set.uIcc_of_le (le_of_lt hb)] at hz'
    linarith [hz'.1.1]
  have hsquare : rectangleBoundaryIntegral f (ρ.re - r) (ρ.re + r)
      (ρ.im - r) (ρ.im + r) = 2 * Real.pi * Complex.I := by
    exact rectangleBoundaryIntegral_sub_inv_centered_square ρ hr
  rw [hsplitOuter, hsplitUpper, hsplitMiddle, hsplitMiddleRight,
    hbottom, htop, hleft, hright, hsquare]
  ring

/-- Integrability on each of the four real parametrizations of a rectangle. -/
def BoundaryIntervalIntegrable (f : ℂ → ℂ) (a b u v : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (u : ℂ) * Complex.I)) volume a b ∧
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) volume a b ∧
  IntervalIntegrable (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) volume u v ∧
  IntervalIntegrable (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) volume u v

/-- Holomorphy on the closed rectangle supplies all four edge integrability
conditions used by the geometric residue theorem. -/
theorem boundaryIntervalIntegrable_of_differentiableOn
    {f : ℂ → ℂ} {a b u v : ℝ}
    (hf : DifferentiableOn ℂ f (uIcc a b ×ℂ uIcc u v)) :
    BoundaryIntervalIntegrable f a b u v := by
  have hc := hf.continuousOn
  have hbot : ContinuousOn
      (fun x : ℝ => f ((x : ℂ) + (u : ℂ) * Complex.I)) (uIcc a b) := by
    change ContinuousOn (f ∘ fun x : ℝ => (x : ℂ) + (u : ℂ) * Complex.I) (uIcc a b)
    apply hc.comp (by fun_prop)
    intro x hx
    exact Complex.mem_reProdIm.mpr ⟨by simpa using hx,
      by simpa using (Set.left_mem_uIcc : u ∈ uIcc u v)⟩
  have htop : ContinuousOn
      (fun x : ℝ => f ((x : ℂ) + (v : ℂ) * Complex.I)) (uIcc a b) := by
    change ContinuousOn (f ∘ fun x : ℝ => (x : ℂ) + (v : ℂ) * Complex.I) (uIcc a b)
    apply hc.comp (by fun_prop)
    intro x hx
    exact Complex.mem_reProdIm.mpr ⟨by simpa using hx,
      by simpa using (Set.right_mem_uIcc : v ∈ uIcc u v)⟩
  have hright : ContinuousOn
      (fun y : ℝ => f ((b : ℂ) + (y : ℂ) * Complex.I)) (uIcc u v) := by
    change ContinuousOn (f ∘ fun y : ℝ => (b : ℂ) + (y : ℂ) * Complex.I) (uIcc u v)
    apply hc.comp (by fun_prop)
    intro y hy
    exact Complex.mem_reProdIm.mpr ⟨
      by simpa using (Set.right_mem_uIcc : b ∈ uIcc a b), by simpa using hy⟩
  have hleft : ContinuousOn
      (fun y : ℝ => f ((a : ℂ) + (y : ℂ) * Complex.I)) (uIcc u v) := by
    change ContinuousOn (f ∘ fun y : ℝ => (a : ℂ) + (y : ℂ) * Complex.I) (uIcc u v)
    apply hc.comp (by fun_prop)
    intro y hy
    exact Complex.mem_reProdIm.mpr ⟨
      by simpa using (Set.left_mem_uIcc : a ∈ uIcc a b), by simpa using hy⟩
  exact ⟨hbot.intervalIntegrable, htop.intervalIntegrable,
    hright.intervalIntegrable, hleft.intervalIntegrable⟩

private theorem boundaryIntervalIntegrable_add
    {f g : ℂ → ℂ} {a b u v : ℝ}
    (hf : BoundaryIntervalIntegrable f a b u v)
    (hg : BoundaryIntervalIntegrable g a b u v) :
    BoundaryIntervalIntegrable (fun z => f z + g z) a b u v := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

private theorem boundaryIntervalIntegrable_const_mul
    {f : ℂ → ℂ} {a b u v : ℝ} (c : ℂ)
    (hf : BoundaryIntervalIntegrable f a b u v) :
    BoundaryIntervalIntegrable (fun z => c * f z) a b u v := by
  exact ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

private theorem rectangleBoundaryIntegral_add
    {f g : ℂ → ℂ} {a b u v : ℝ}
    (hf : BoundaryIntervalIntegrable f a b u v)
    (hg : BoundaryIntervalIntegrable g a b u v) :
    rectangleBoundaryIntegral (fun z => f z + g z) a b u v =
      rectangleBoundaryIntegral f a b u v + rectangleBoundaryIntegral g a b u v := by
  unfold rectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

private theorem rectangleBoundaryIntegral_const_mul
    (c : ℂ) (f : ℂ → ℂ) (a b u v : ℝ) :
    rectangleBoundaryIntegral (fun z => c * f z) a b u v =
      c * rectangleBoundaryIntegral f a b u v := by
  unfold rectangleBoundaryIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  ring

private theorem boundaryIntervalIntegrable_finset_sum
    {I : Type*} {S : Finset I} {f : I → ℂ → ℂ} {a b u v : ℝ}
    (hf : ∀ i ∈ S, BoundaryIntervalIntegrable (f i) a b u v) :
    BoundaryIntervalIntegrable (fun z => ∑ i ∈ S, f i z) a b u v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [BoundaryIntervalIntegrable]
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      apply boundaryIntervalIntegrable_add
      · exact hf i (Finset.mem_insert_self i S)
      · exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))

private theorem rectangleBoundaryIntegral_finset_sum
    {I : Type*} {S : Finset I} {f : I → ℂ → ℂ} {a b u v : ℝ}
    (hf : ∀ i ∈ S, BoundaryIntervalIntegrable (f i) a b u v) :
    rectangleBoundaryIntegral (fun z => ∑ i ∈ S, f i z) a b u v =
      ∑ i ∈ S, rectangleBoundaryIntegral (f i) a b u v := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [rectangleBoundaryIntegral]
  | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      rw [rectangleBoundaryIntegral_add
        (hf i (Finset.mem_insert_self i S))
        (boundaryIntervalIntegrable_finset_sum
          (fun j hj => hf j (Finset.mem_insert_of_mem hj)))]
      rw [ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

private theorem rectangleBoundaryIntegral_congr_edges
    {f g : ℂ → ℂ} {a b u v : ℝ}
    (hbot : ∀ x : ℝ, f ((x : ℂ) + (u : ℂ) * Complex.I) =
      g ((x : ℂ) + (u : ℂ) * Complex.I))
    (htop : ∀ x : ℝ, f ((x : ℂ) + (v : ℂ) * Complex.I) =
      g ((x : ℂ) + (v : ℂ) * Complex.I))
    (hright : ∀ y : ℝ, f ((b : ℂ) + (y : ℂ) * Complex.I) =
      g ((b : ℂ) + (y : ℂ) * Complex.I))
    (hleft : ∀ y : ℝ, f ((a : ℂ) + (y : ℂ) * Complex.I) =
      g ((a : ℂ) + (y : ℂ) * Complex.I)) :
    rectangleBoundaryIntegral f a b u v =
      rectangleBoundaryIntegral g a b u v := by
  have hbot' : (∫ x in a..b, f ((x : ℂ) + (u : ℂ) * Complex.I)) =
      ∫ x in a..b, g ((x : ℂ) + (u : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact hbot x
  have htop' : (∫ x in a..b, f ((x : ℂ) + (v : ℂ) * Complex.I)) =
      ∫ x in a..b, g ((x : ℂ) + (v : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    exact htop x
  have hright' : (∫ y in u..v, f ((b : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in u..v, g ((b : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hright y
  have hleft' : (∫ y in u..v, f ((a : ℂ) + (y : ℂ) * Complex.I)) =
      ∫ y in u..v, g ((a : ℂ) + (y : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact hleft y
  unfold rectangleBoundaryIntegral
  rw [hbot', htop', hright', hleft']

/-- Finite-pole rectangle residue theorem in a form suitable for explicit
formulae.  The radii give pairwise independent square excisions contained in
the outer rectangle.  The function `g` is the patched holomorphic remainder;
the four edge equalities say that subtracting the displayed principal parts
from `f` really gives that remainder on the contour.

Unlike a contract which assumes the desired boundary integral, this theorem
derives it from Cauchy--Goursat, finite-sum linearity, and the excised-square
calculation above. -/
theorem rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    {I : Type*} [DecidableEq I]
    (S : Finset I) (pole : I → ℂ) (residue : I → ℂ)
    (radius : I → ℝ) (f g : ℂ → ℂ) (a b u v : ℝ)
    (hradius : ∀ i ∈ S, 0 < radius i)
    (ha : ∀ i ∈ S, a < (pole i).re - radius i)
    (hb : ∀ i ∈ S, (pole i).re + radius i < b)
    (hu : ∀ i ∈ S, u < (pole i).im - radius i)
    (hv : ∀ i ∈ S, (pole i).im + radius i < v)
    (hgIntegrable : BoundaryIntervalIntegrable g a b u v)
    (hgDifferentiable : DifferentiableOn ℂ g (uIcc a b ×ℂ uIcc u v))
    (hbot : ∀ x : ℝ,
      f ((x : ℂ) + (u : ℂ) * Complex.I) =
        g ((x : ℂ) + (u : ℂ) * Complex.I) +
          ∑ i ∈ S, residue i *
            (((x : ℂ) + (u : ℂ) * Complex.I) - pole i)⁻¹)
    (htop : ∀ x : ℝ,
      f ((x : ℂ) + (v : ℂ) * Complex.I) =
        g ((x : ℂ) + (v : ℂ) * Complex.I) +
          ∑ i ∈ S, residue i *
            (((x : ℂ) + (v : ℂ) * Complex.I) - pole i)⁻¹)
    (hright : ∀ y : ℝ,
      f ((b : ℂ) + (y : ℂ) * Complex.I) =
        g ((b : ℂ) + (y : ℂ) * Complex.I) +
          ∑ i ∈ S, residue i *
            (((b : ℂ) + (y : ℂ) * Complex.I) - pole i)⁻¹)
    (hleft : ∀ y : ℝ,
      f ((a : ℂ) + (y : ℂ) * Complex.I) =
        g ((a : ℂ) + (y : ℂ) * Complex.I) +
          ∑ i ∈ S, residue i *
            (((a : ℂ) + (y : ℂ) * Complex.I) - pole i)⁻¹) :
    rectangleBoundaryIntegral f a b u v =
      (2 * Real.pi * Complex.I) * ∑ i ∈ S, residue i := by
  let principalPart : I → ℂ → ℂ := fun i z =>
    residue i * (z - pole i)⁻¹
  have hprincipalIntegrable : ∀ i ∈ S,
      BoundaryIntervalIntegrable (principalPart i) a b u v := by
    intro i hi
    have hri := hradius i hi
    have hau : u ≠ (pole i).im := by linarith [hu i hi]
    have hav : v ≠ (pole i).im := by linarith [hv i hi]
    have haa : a ≠ (pole i).re := by linarith [ha i hi]
    have hab : b ≠ (pole i).re := by linarith [hb i hi]
    apply boundaryIntervalIntegrable_const_mul (residue i)
    exact ⟨(continuous_horizontal_sub_inv (pole i) hau).intervalIntegrable _ _,
      (continuous_horizontal_sub_inv (pole i) hav).intervalIntegrable _ _,
      (continuous_vertical_sub_inv (pole i) hab).intervalIntegrable _ _,
      (continuous_vertical_sub_inv (pole i) haa).intervalIntegrable _ _⟩
  have hprincipalValue :
      rectangleBoundaryIntegral (fun z => ∑ i ∈ S, principalPart i z) a b u v =
        (2 * Real.pi * Complex.I) * ∑ i ∈ S, residue i := by
    rw [rectangleBoundaryIntegral_finset_sum hprincipalIntegrable]
    calc
      ∑ i ∈ S, rectangleBoundaryIntegral (principalPart i) a b u v =
          ∑ i ∈ S, residue i * (2 * Real.pi * Complex.I) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [show principalPart i = fun z => residue i * (z - pole i)⁻¹ by rfl]
        rw [rectangleBoundaryIntegral_const_mul]
        rw [rectangleBoundaryIntegral_sub_inv_eq_two_pi_I (pole i)
          (hradius i hi) (ha i hi) (hb i hi) (hu i hi) (hv i hi)]
      _ = (2 * Real.pi * Complex.I) * ∑ i ∈ S, residue i := by
        rw [← Finset.sum_mul]
        ring
  have hboundary : rectangleBoundaryIntegral f a b u v =
      rectangleBoundaryIntegral
        (fun z => g z + ∑ i ∈ S, principalPart i z) a b u v := by
    apply rectangleBoundaryIntegral_congr_edges
    · simpa [principalPart] using hbot
    · simpa [principalPart] using htop
    · simpa [principalPart] using hright
    · simpa [principalPart] using hleft
  rw [hboundary]
  rw [rectangleBoundaryIntegral_add hgIntegrable
    (boundaryIntervalIntegrable_finset_sum hprincipalIntegrable)]
  rw [rectangleBoundaryIntegral_eq_zero_of_differentiableOn g a b u v
    hgDifferentiable, hprincipalValue]
  ring

end

end FinitePoleRectangle
