import RamachandraFunctionalFactorQuarterLine
import BHPRademacherGaussianThreeLines

/-!
# Real-part sharp Gamma bound on the positive unit strip

A centered Gaussian and a one-sided exponential twist make Hadamard's
three-lines theorem retain the interpolation exponent in the height.  This is
the uniform strip input needed by the near Ramachandra contour.
-/

namespace GammaSharpPositiveStripInterpolation

open Complex Set
open Complex.HadamardThreeLines
open MAPBHPRademacherGaussianEnvelope

noncomputable section

private def orientation (t : ℝ) : ℝ := if 0 ≤ t then -1 else 1

private theorem orientation_abs (t : ℝ) : |orientation t| = 1 := by
  unfold orientation
  split_ifs <;> norm_num

private theorem neg_orientation_mul_le_abs (t v : ℝ) :
    -(orientation t) * v ≤ |v| := by
  by_cases ht : 0 ≤ t
  · rw [orientation, if_pos ht]
    norm_num
    exact le_abs_self v
  · rw [orientation, if_neg ht]
    norm_num
    exact neg_le_abs v

private theorem neg_orientation_mul_self_eq_abs (t : ℝ) :
    -(orientation t) * t = |t| := by
  by_cases ht : 0 ≤ t
  · rw [orientation, if_pos ht, abs_of_nonneg ht]
    ring
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [orientation, if_neg ht, abs_of_neg ht']
    ring

/-- Gamma with both its vertical exponential and a Gaussian centered at the
target ordinate removed. -/
def gammaInterpolationTwist (t : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma z *
    Complex.exp (((orientation t * (Real.pi / 2) : ℝ) : ℂ) * I * z) *
    Complex.exp ((z - (t : ℂ) * I) ^ 2)

private theorem norm_linearTwist (t : ℝ) (z : ℂ) :
    ‖Complex.exp (((orientation t * (Real.pi / 2) : ℝ) : ℂ) * I * z)‖ =
      Real.exp (-(orientation t) * (Real.pi / 2) * z.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, zero_mul, mul_zero,
    sub_zero, add_zero, mul_im]
  ring

private theorem norm_centeredGaussian (t : ℝ) (z : ℂ) :
    ‖Complex.exp ((z - (t : ℂ) * I) ^ 2)‖ =
      Real.exp (z.re ^ 2 - (z.im - t) ^ 2) :=
  MAPBHPRademacherGaussianThreeLines.norm_centeredGaussian t z

private theorem gammaInterpolationTwist_diffContOnCl (t : ℝ) :
    DiffContOnCl ℂ (gammaInterpolationTwist t)
      (verticalStrip (1 / 2) (3 / 2)) := by
  apply DifferentiableOn.diffContOnCl
  intro z hz
  have hzre : (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 3 / 2 := by
    have heq : closure (verticalStrip (1 / 2) (3 / 2)) =
        verticalClosedStrip (1 / 2) (3 / 2) := by
      rw [verticalStrip, verticalClosedStrip, Complex.closure_preimage_re,
        closure_Ioo (by norm_num : (1 / 2 : ℝ) ≠ 3 / 2)]
    rw [heq] at hz
    exact hz
  have hGamma : DifferentiableAt ℂ Complex.Gamma z := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp at hre
    linarith
  have hlin : DifferentiableAt ℂ (fun w : ℂ =>
      Complex.exp (((orientation t * (Real.pi / 2) : ℝ) : ℂ) * I * w)) z :=
    Complex.differentiableAt_exp.comp z
      (differentiableAt_const _ |>.mul differentiableAt_id)
  have hgauss : DifferentiableAt ℂ (fun w : ℂ =>
      Complex.exp ((w - (t : ℂ) * I) ^ 2)) z :=
    Complex.differentiableAt_exp.comp z
      ((differentiableAt_id.sub_const ((t : ℂ) * I)).pow 2)
  exact ((hGamma.mul hlin).mul hgauss).differentiableWithinAt

private theorem one_add_abs_le_center (t v : ℝ) :
    1 + |v| ≤ (1 + |t|) * (1 + |v - t|) := by
  have htri : |v| ≤ |t| + |v - t| := by
    have h := abs_add_le t (v - t)
    rw [show t + (v - t) = v by ring] at h
    exact h
  nlinarith [abs_nonneg t, abs_nonneg (v - t)]

private theorem polynomial_gaussian_le_four (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) * Real.exp (-(r ^ 2)) ≤ 4 := by
  calc
    (1 + r) * Real.exp (-(r ^ 2)) ≤
        (1 + r) ^ 2 * Real.exp (-(r ^ 2)) := by
      gcongr
      nlinarith
    _ ≤ 4 := one_add_sq_mul_exp_neg_sq_le_four r hr

private theorem normalized_exp_product_le_one (t v : ℝ) :
    Real.exp (-(Real.pi / 2) * |v|) *
        Real.exp (-(orientation t) * (Real.pi / 2) * v) ≤ 1 := by
  rw [← Real.exp_add, ← Real.exp_zero]
  apply Real.exp_le_exp.mpr
  have h := neg_orientation_mul_le_abs t v
  have hp : 0 ≤ Real.pi / 2 := by positivity
  nlinarith

private theorem gammaInterpolationTwist_bound
    {t : ℝ} {z : ℂ}
    (hzlo : (1 / 2 : ℝ) ≤ z.re) (hzhi : z.re ≤ 3 / 2) :
    ‖gammaInterpolationTwist t z‖ ≤ 2000 * (1 + |t|) := by
  have hGamma := MAPGammaCompactStripSharp.norm_Gamma_positive_strip_le_exp_pi_half
    (a := z.re) (t := z.im) hzlo hzhi
  have hgeom : GammaCompactStripScratch.stripPoint z.re z.im = z := by
    apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]
  rw [hgeom] at hGamma
  have hnormBasic : ‖gammaInterpolationTwist t z‖ =
      ‖Complex.Gamma z‖ *
        Real.exp (-(orientation t) * (Real.pi / 2) * z.im) *
        Real.exp (z.re ^ 2 - (z.im - t) ^ 2) := by
    unfold gammaInterpolationTwist
    rw [norm_mul, norm_mul, norm_linearTwist, norm_centeredGaussian]
  rw [hnormBasic]
  let r : ℝ := |z.im - t|
  have hr : 0 ≤ r := abs_nonneg _
  have hcenter := one_add_abs_le_center t z.im
  have hpoly := polynomial_gaussian_le_four r hr
  have hnormprod := normalized_exp_product_le_one t z.im
  have hreSq : z.re ^ 2 ≤ 9 / 4 := by nlinarith
  have hexpre : Real.exp (z.re ^ 2) ≤ Real.exp (9 / 4) :=
    Real.exp_le_exp.mpr hreSq
  have hexpBound : Real.exp (9 / 4 : ℝ) ≤ 27 := by
    calc
      Real.exp (9 / 4 : ℝ) ≤ Real.exp 3 := Real.exp_le_exp.mpr (by norm_num)
      _ = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ 3 ^ 3 := by gcongr; exact Real.exp_one_lt_three.le
      _ ≤ 27 := by norm_num
  have hexpFinal : Real.exp (z.re ^ 2) ≤ 27 := hexpre.trans hexpBound
  have hcenterExp :
      (1 + |z.im|) * Real.exp (-(r ^ 2)) ≤ 4 * (1 + |t|) := by
    calc
      (1 + |z.im|) * Real.exp (-(r ^ 2)) ≤
          ((1 + |t|) * (1 + r)) * Real.exp (-(r ^ 2)) :=
        mul_le_mul_of_nonneg_right (by simpa [r] using hcenter) (Real.exp_pos _).le
      _ = (1 + |t|) * ((1 + r) * Real.exp (-(r ^ 2))) := by ring
      _ ≤ (1 + |t|) * 4 :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = 4 * (1 + |t|) := by ring
  let P : ℝ := Real.exp (-(Real.pi / 2) * |z.im|) *
    Real.exp (-(orientation t) * (Real.pi / 2) * z.im)
  have hP : P ≤ 1 := by simpa [P] using hnormprod
  have hP0 : 0 ≤ P := by dsimp [P]; positivity
  have hEP0 : 0 ≤ Real.exp (-(r ^ 2)) := (Real.exp_pos _).le
  have hFirst :
      (1 + |z.im|) * P * Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2)) ≤
        27 * ((1 + |z.im|) * Real.exp (-(r ^ 2))) := by
    calc
      (1 + |z.im|) * P * Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2)) ≤
          (1 + |z.im|) * 1 * Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hP (by positivity))
            (Real.exp_pos _).le) hEP0
      _ ≤ (1 + |z.im|) * 1 * 27 * Real.exp (-(r ^ 2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpFinal (by positivity)) hEP0
      _ = 27 * ((1 + |z.im|) * Real.exp (-(r ^ 2))) := by ring
  calc
    ‖Complex.Gamma z‖ *
        Real.exp (-(orientation t) * (Real.pi / 2) * z.im) *
        Real.exp (z.re ^ 2 - (z.im - t) ^ 2) ≤
      (12 * (1 + |z.im|) * Real.exp (-(Real.pi / 2) * |z.im|)) *
        Real.exp (-(orientation t) * (Real.pi / 2) * z.im) *
        Real.exp (z.re ^ 2 - (z.im - t) ^ 2) := by gcongr
    _ = 12 * (1 + |z.im|) * P *
        (Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2))) := by
      rw [show z.re ^ 2 - (z.im - t) ^ 2 =
        z.re ^ 2 + (-(r ^ 2)) by simp [r, sq_abs]; ring, Real.exp_add]
      ring
    _ ≤ 12 * (27 * ((1 + |z.im|) * Real.exp (-(r ^ 2)))) := by
      rw [show 12 * (1 + |z.im|) * P *
          (Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2))) =
          12 * ((1 + |z.im|) * P * Real.exp (z.re ^ 2) *
            Real.exp (-(r ^ 2))) by ring]
      exact mul_le_mul_of_nonneg_left hFirst (by norm_num)
    _ ≤ 12 * (27 * (4 * (1 + |t|))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hcenterExp (by norm_num)) (by norm_num)
    _ ≤ 2000 * (1 + |t|) := by nlinarith [abs_nonneg t]

private theorem gammaInterpolationTwist_bddAbove (t : ℝ) :
    BddAbove ((norm ∘ gammaInterpolationTwist t) ''
      verticalClosedStrip (1 / 2) (3 / 2)) := by
  refine ⟨2000 * (1 + |t|), ?_⟩
  rintro y ⟨z, hz, rfl⟩
  exact gammaInterpolationTwist_bound hz.1 hz.2

private theorem gammaInterpolationTwist_leftBoundary (t : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({(1 / 2 : ℝ)} : Set ℝ),
      ‖gammaInterpolationTwist t z‖ ≤ 2000 := by
  intro z hz
  have hzre : z.re = 1 / 2 := by simpa using hz
  have h := gammaInterpolationTwist_bound (t := t) (z := z)
    (by linarith) (by linarith)
  -- On the lower boundary the exact central Gamma identity removes the
  -- polynomial factor.  We retain a generous absolute constant.
  have hGamma := MAPGammaCompactStripSharp.norm_Gamma_centralPoint_le_exp_pi_half z.im
  have hgeom : MAPGammaCompactStripSharp.centralPoint z.im = z := by
    apply Complex.ext <;> simp [MAPGammaCompactStripSharp.centralPoint, hzre]
  rw [hgeom] at hGamma
  have hnormBasic : ‖gammaInterpolationTwist t z‖ =
      ‖Complex.Gamma z‖ *
        Real.exp (-(orientation t) * (Real.pi / 2) * z.im) *
        Real.exp (z.re ^ 2 - (z.im - t) ^ 2) := by
    unfold gammaInterpolationTwist
    rw [norm_mul, norm_mul, norm_linearTwist, norm_centeredGaussian]
  rw [hnormBasic]
  let r : ℝ := |z.im - t|
  have hnormprod := normalized_exp_product_le_one t z.im
  have hexp : Real.exp (z.re ^ 2) ≤ 3 := by
    rw [hzre]
    calc
      Real.exp ((1 / 2 : ℝ) ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ 3 := Real.exp_one_lt_three.le
  calc
    _ ≤ (3 * Real.exp (-(Real.pi / 2) * |z.im|)) *
        Real.exp (-(orientation t) * (Real.pi / 2) * z.im) *
        Real.exp (z.re ^ 2 - (z.im - t) ^ 2) := by gcongr
    _ = 3 *
        (Real.exp (-(Real.pi / 2) * |z.im|) *
          Real.exp (-(orientation t) * (Real.pi / 2) * z.im)) *
        (Real.exp (z.re ^ 2) * Real.exp (-(r ^ 2))) := by
      rw [show z.re ^ 2 - (z.im - t) ^ 2 =
        z.re ^ 2 + (-(r ^ 2)) by simp [r, sq_abs]; ring, Real.exp_add]
      ring
    _ ≤ 3 * 1 * (3 * 1) := by
      gcongr
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg r))
    _ ≤ 2000 := by norm_num

private theorem gammaInterpolationTwist_rightBoundary (t : ℝ) :
    ∀ z ∈ Complex.re ⁻¹' ({(3 / 2 : ℝ)} : Set ℝ),
      ‖gammaInterpolationTwist t z‖ ≤ 2000 * (1 + |t|) := by
  intro z hz
  have hzre : z.re = 3 / 2 := by simpa using hz
  exact gammaInterpolationTwist_bound (by linarith) (by linarith)

/-- Sharp interpolation form on `1/2 ≤ Re z ≤ 3/2`. -/
theorem norm_Gamma_positive_strip_le_interp
    {a t : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) :
    ‖Complex.Gamma (GammaCompactStripScratch.stripPoint a t)‖ ≤
      Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2) *
        Real.exp (-(Real.pi / 2) * |t|) := by
  let z := GammaCompactStripScratch.stripPoint a t
  have hzre : z.re = a := by simp [z, GammaCompactStripScratch.stripPoint]
  have hz : z ∈ verticalClosedStrip (1 / 2) (3 / 2) := by
    constructor
    · rw [hzre]
      exact ha
    · rw [hzre]
      exact ha'
  have hinterp := norm_le_interp_of_mem_verticalClosedStrip'
    (f := gammaInterpolationTwist t) (z := z)
    (l := (1 / 2 : ℝ)) (u := 3 / 2)
    (a := (2000 : ℝ)) (b := 2000 * (1 + |t|))
    (by norm_num) hz
    (gammaInterpolationTwist_diffContOnCl t)
    (gammaInterpolationTwist_bddAbove t)
    (gammaInterpolationTwist_leftBoundary t)
    (gammaInterpolationTwist_rightBoundary t)
  have htarget : ‖gammaInterpolationTwist t z‖ =
      ‖Complex.Gamma z‖ * Real.exp ((Real.pi / 2) * |t|) *
        Real.exp (a ^ 2) := by
    unfold gammaInterpolationTwist
    rw [norm_mul, norm_mul, norm_linearTwist, norm_centeredGaussian]
    have hzim : z.im = t := by simp [z, GammaCompactStripScratch.stripPoint]
    rw [hzre, hzim, sub_self]
    have hzero : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [hzero, sub_zero]
    have hor : -(orientation t) * (Real.pi / 2) * t =
        (Real.pi / 2) * |t| := by
      rw [show -(orientation t) * (Real.pi / 2) * t =
        (Real.pi / 2) * (-(orientation t) * t) by ring,
        neg_orientation_mul_self_eq_abs]
    rw [hor]
  have hinterp' : ‖gammaInterpolationTwist t z‖ ≤
      Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2) := by
    rw [hzre] at hinterp
    norm_num at hinterp ⊢
    have hw : 1 - (a - 1 / 2) = 3 / 2 - a := by ring
    rw [hw] at hinterp
    exact hinterp
  rw [htarget] at hinterp'
  have hEa : 1 ≤ Real.exp (a ^ 2) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (sq_nonneg a)
  have hEpos : 0 < Real.exp ((Real.pi / 2) * |t|) := Real.exp_pos _
  have hmain : ‖Complex.Gamma z‖ * Real.exp ((Real.pi / 2) * |t|) ≤
      Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2) := by
    have hdrop : ‖Complex.Gamma z‖ * Real.exp ((Real.pi / 2) * |t|) * 1 ≤
        ‖Complex.Gamma z‖ * Real.exp ((Real.pi / 2) * |t|) * Real.exp (a ^ 2) :=
      mul_le_mul_of_nonneg_left hEa
        (mul_nonneg (norm_nonneg _) hEpos.le)
    simpa only [mul_one] using hdrop.trans hinterp'
  have hdiv : ‖Complex.Gamma z‖ ≤
      (Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2)) /
          Real.exp ((Real.pi / 2) * |t|) :=
    (le_div_iff₀ hEpos).2 hmain
  have hquot :
      (Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2)) /
          Real.exp ((Real.pi / 2) * |t|) =
      Real.rpow 2000 (3 / 2 - a) *
        Real.rpow (2000 * (1 + |t|)) (a - 1 / 2) *
          Real.exp (-(Real.pi / 2) * |t|) := by
    rw [div_eq_mul_inv, ← Real.exp_neg]
    congr 2
    ring
  simpa only [z] using hdiv.trans_eq hquot

end
end GammaSharpPositiveStripInterpolation

#print axioms GammaSharpPositiveStripInterpolation.norm_Gamma_positive_strip_le_interp
