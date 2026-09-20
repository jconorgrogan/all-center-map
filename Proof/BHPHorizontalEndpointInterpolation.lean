import BHPAmbientRademacherThreeLines
import RightEdgePSeriesExplicitBound
import BHPRademacherTitchmarshSources

/-!
# Endpoint reduction for the quantitative BHP horizontal strip

The exponent in the Gaussian three-lines estimate is affine in the horizontal
coordinate.  This file records that exact affine reduction, before any
paper-scale logarithmic simplification.
-/

namespace MAPBHPHorizontalEndpointInterpolation

open Complex
open MAPBHPCorrectedContourShift
open MAPBHPAmbientRademacherThreeLines
open MAPBHPRademacherTitchmarshSources
open MAPZeroFreeSiegelSpine
open MAPRightEdgePSeriesExplicitBound

noncomputable section

/-- A three-lines majorant multiplied by `X^x` is bounded by its two endpoint
values.  The proof is the elementary fact that its logarithm is affine in
`x`; no monotonicity direction is assumed. -/
theorem weighted_strip_interpolation_le_endpoint_sum
    {A B X d c W x : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hW : 0 < W)
    (hdx : d ≤ x) (hxc : x ≤ c) :
    Real.rpow A ((c - x) / W) *
        Real.rpow B ((x + (W - c)) / W) * Real.rpow X x ≤
      Real.rpow A ((c - d) / W) *
          Real.rpow B ((d + (W - c)) / W) * Real.rpow X d +
        Real.rpow B 1 * Real.rpow X c := by
  let E : ℝ → ℝ := fun y =>
    Real.log A * ((c - y) / W) +
      Real.log B * ((y + (W - c)) / W) + Real.log X * y
  have hrewrite (y : ℝ) :
      Real.rpow A ((c - y) / W) *
          Real.rpow B ((y + (W - c)) / W) * Real.rpow X y =
        Real.exp (E y) := by
    dsimp [E]
    rw [Real.rpow_def_of_pos hA, Real.rpow_def_of_pos hB,
      Real.rpow_def_of_pos hX, ← Real.exp_add, ← Real.exp_add]
  have hrightRewrite : Real.rpow B 1 * Real.rpow X c =
      Real.exp (E c) := by
    have hc := hrewrite c
    have hratio : (c + (W - c)) / W = 1 := by
      field_simp [ne_of_gt hW]
      ring
    have hAzero : Real.rpow A 0 = 1 := by simp [Real.rpow]
    rw [sub_self, zero_div, hAzero, one_mul, hratio] at hc
    exact hc
  rw [hrewrite x, hrewrite d, hrightRewrite]
  let slope : ℝ :=
    (-Real.log A + Real.log B) / W + Real.log X
  by_cases hslope : 0 ≤ slope
  · have hlog :
        E x ≤ E c := by
      dsimp [slope] at hslope
      dsimp [E]
      have hWne : W ≠ 0 := ne_of_gt hW
      field_simp [hWne] at hslope ⊢
      nlinarith
    exact (Real.exp_le_exp.mpr hlog).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · have hslope' : slope < 0 := lt_of_not_ge hslope
    have hlog :
        E x ≤ E d := by
      dsimp [slope] at hslope'
      dsimp [E]
      have hWne : W ≠ 0 := ne_of_gt hW
      field_simp [hWne] at hslope' ⊢
      nlinarith
    exact (Real.exp_le_exp.mpr hlog).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- Ambient (possibly imprimitive) interpolation majorant. -/
def ambientRademacherMajorant
    (q : ℕ) (kappa rWidth sigma u : ℝ) : ℝ :=
  Real.rpow
    (48 * (1 + kappa⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1))
    (1 - sigma / (1 + rWidth)) *
  Real.rpow
    (rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
    (sigma / (1 + rWidth))

/-- Literal `/w` horizontal point estimate for every nonprincipal ambient
character, now using direct ambient interpolation rather than a primitive
reduction. -/
theorem norm_bhpPerronIntegrand_horizontal_le_ambient
    {kappa rWidth : ℝ} (hkappa : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hr0 : 0 < rWidth) (hrHalf : rWidth ≤ 1 / 2)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {X t x v H : ℝ} (hX : 0 < X) (hH : 0 < H)
    (hv : |v| = H)
    (hsigma0 : 0 ≤ (1 / 2 : ℝ) + x)
    (hsigmaUpper : (1 / 2 : ℝ) + x ≤ 1 + rWidth) :
    ‖bhpPerronIntegrand chi X t
        ((x : ℂ) + Complex.I * v)‖ ≤
      ambientRademacherMajorant q kappa rWidth
        ((1 / 2 : ℝ) + x) (t + v) * (Real.rpow X x / H) := by
  have hL := norm_ambientLFunction_le_wide_interp hkappa hkappaHalf
    hr0 hrHalf chi hchi (sigma := (1 / 2 : ℝ) + x)
      (u := t + v) hsigma0 hsigmaUpper
  have hpow :
      ‖Complex.exp ((((x : ℂ) + Complex.I * v) * Real.log X))‖ =
        Real.rpow X x := by
    rw [← PerronKernel.verticalPower_eq_exp hX x v]
    exact PerronKernel.norm_verticalPower hX x v
  have hden : H ≤ ‖(x : ℂ) + Complex.I * v‖ := by
    rw [← hv]
    calc
      |v| = |(((x : ℂ) + Complex.I * v).im)| := by simp
      _ ≤ ‖(x : ℂ) + Complex.I * v‖ := Complex.abs_im_le_norm _
  have hM0 : 0 ≤ ambientRademacherMajorant q kappa rWidth
      ((1 / 2 : ℝ) + x) (t + v) := by
    unfold ambientRademacherMajorant
    have hq : 0 < (q : ℝ) := by
      exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
    have hleft : 0 < 48 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |t + v|)) (kappa + 1) := by
      have : 0 < 1 + kappa⁻¹ := by positivity
      have hbase : 0 < 2 * (q : ℝ) * (3 + |t + v|) := by
        positivity
      exact mul_pos (mul_pos (by norm_num) this)
        (Real.rpow_pos_of_pos hbase _)
    have hright : 0 < rightEdgePSeries rWidth *
        Real.exp ((1 + rWidth) ^ 2) := by
      have := one_le_rightEdgePSeries hr0
      positivity
    exact mul_nonneg (Real.rpow_nonneg hleft.le _)
      (Real.rpow_nonneg hright.le _)
  have hpow0 : 0 ≤ Real.rpow X x := Real.rpow_nonneg hX.le _
  unfold bhpPerronIntegrand
  rw [norm_div, norm_mul, hpow]
  have harg :
      ((((1 / 2 : ℝ) : ℂ) + t * Complex.I) +
          ((x : ℂ) + Complex.I * v)) =
        ((((1 / 2 : ℝ) + x : ℝ) : ℂ) +
          (t + v) * Complex.I) := by
    push_cast
    ring
  rw [harg]
  calc
    ‖DirichletCharacter.LFunction chi
          (((1 / 2 + x : ℝ) : ℂ) +
            ((t : ℂ) + (v : ℂ)) * Complex.I)‖ * Real.rpow X x /
          ‖(x : ℂ) + Complex.I * v‖ ≤
      ambientRademacherMajorant q kappa rWidth
          ((1 / 2 : ℝ) + x) (t + v) * Real.rpow X x /
          ‖(x : ℂ) + Complex.I * v‖ := by
      gcongr
      simpa [ambientRademacherMajorant] using hL
    _ ≤ ambientRademacherMajorant q kappa rWidth
          ((1 / 2 : ℝ) + x) (t + v) * Real.rpow X x / H := by
      exact div_le_div_of_nonneg_left (mul_nonneg hM0 hpow0) hH hden
    _ = ambientRademacherMajorant q kappa rWidth
          ((1 / 2 : ℝ) + x) (t + v) * (Real.rpow X x / H) := by ring

/-- Exact endpoint reduction when the interpolation width and Gaussian loss
are both the same positive offset `delta`. -/
theorem ambient_majorant_mul_rpow_le_endpoints
    {q : ℕ} {delta X x u : ℝ}
    (hq : 1 ≤ q) (hdelta : 0 < delta) (hX : 0 < X)
    (hdx : delta ≤ x) (hxc : x ≤ 1 / 2 + delta) :
    ambientRademacherMajorant q delta delta ((1 / 2 : ℝ) + x) u *
        Real.rpow X x ≤
      let A := 48 * (1 + delta⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1)
      let B := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
      Real.rpow A (((1 / 2 + delta) - delta) / (1 + delta)) *
          Real.rpow B ((delta + ((1 + delta) - (1 / 2 + delta))) /
            (1 + delta)) *
          Real.rpow X delta +
        Real.rpow B 1 * Real.rpow X (1 / 2 + delta) := by
  let A := 48 * (1 + delta⁻¹) *
    Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1)
  let B := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < 1 + delta⁻¹ := by positivity
    have hqR : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    positivity
  have hB : 0 < B := by
    dsimp [B]
    have := one_le_rightEdgePSeries hdelta
    positivity
  have hW : 0 < 1 + delta := by linarith
  have hbase := weighted_strip_interpolation_le_endpoint_sum
    hA hB hX hW hdx hxc
    (d := delta) (c := 1 / 2 + delta) (W := 1 + delta)
  dsimp only [A, B] at hbase ⊢
  have hleftExp :
      1 - ((1 / 2 : ℝ) + x) / (1 + delta) =
        ((1 / 2 + delta) - x) / (1 + delta) := by
    field_simp [ne_of_gt hW]
    ring
  have hrightExp :
      ((1 / 2 : ℝ) + x) / (1 + delta) =
        (x + ((1 + delta) - (1 / 2 + delta))) / (1 + delta) := by
    field_simp [ne_of_gt hW]
    ring
  have hmajorantRewrite :
      ambientRademacherMajorant q delta delta ((1 / 2 : ℝ) + x) u *
          Real.rpow X x =
        Real.rpow
            (48 * (1 + delta⁻¹) *
              Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1))
            (((1 / 2 + delta) - x) / (1 + delta)) *
          Real.rpow
            (rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2))
            ((x + ((1 + delta) - (1 / 2 + delta))) / (1 + delta)) *
          Real.rpow X x := by
    unfold ambientRademacherMajorant
    rw [hleftExp, hrightExp]
  exact hmajorantRewrite.le.trans hbase

/-- Endpoint reduction with independent Gaussian loss `kappa`, absolutely
convergent right width `rWidth`, and positive left offset `delta`.  This is
the source-faithful form needed to join Titchmarsh's right line
`1/2 + 1/log x0` to the Ramachandra-safe left line
`1/(400 log x0)`. -/
theorem ambient_majorant_mul_rpow_le_general_endpoints
    {q : ℕ} {kappa rWidth delta X x u : ℝ}
    (hq : 1 ≤ q) (hkappa : 0 < kappa) (hrWidth : 0 < rWidth)
    (hdelta : 0 < delta) (hX : 0 < X)
    (hdx : delta ≤ x) (hxc : x ≤ 1 / 2 + rWidth) :
    ambientRademacherMajorant q kappa rWidth ((1 / 2 : ℝ) + x) u *
        Real.rpow X x ≤
      let A := 48 * (1 + kappa⁻¹) *
        Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1)
      let B := rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2)
      Real.rpow A (((1 / 2 + rWidth) - delta) / (1 + rWidth)) *
          Real.rpow B ((delta + (1 / 2)) / (1 + rWidth)) *
          Real.rpow X delta +
        Real.rpow B 1 * Real.rpow X (1 / 2 + rWidth) := by
  let A := 48 * (1 + kappa⁻¹) *
    Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1)
  let B := rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2)
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < 1 + kappa⁻¹ := by positivity
    have hqR : 0 < (q : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hq)
    positivity
  have hB : 0 < B := by
    dsimp [B]
    have := one_le_rightEdgePSeries hrWidth
    positivity
  have hW : 0 < 1 + rWidth := by linarith
  have hbase := weighted_strip_interpolation_le_endpoint_sum
    hA hB hX hW hdx hxc
    (d := delta) (c := 1 / 2 + rWidth) (W := 1 + rWidth)
  dsimp only [A, B] at hbase ⊢
  have hleftExp :
      1 - ((1 / 2 : ℝ) + x) / (1 + rWidth) =
        ((1 / 2 + rWidth) - x) / (1 + rWidth) := by
    field_simp [ne_of_gt hW]
    ring
  have hrightExp :
      ((1 / 2 : ℝ) + x) / (1 + rWidth) =
        (x + (1 / 2)) / (1 + rWidth) := by
    field_simp [ne_of_gt hW]
    ring
  have hmajorantRewrite :
      ambientRademacherMajorant q kappa rWidth ((1 / 2 : ℝ) + x) u *
          Real.rpow X x =
        Real.rpow
            (48 * (1 + kappa⁻¹) *
              Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1))
            (((1 / 2 + rWidth) - x) / (1 + rWidth)) *
          Real.rpow
            (rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2))
            ((x + (1 / 2)) / (1 + rWidth)) *
          Real.rpow X x := by
    unfold ambientRademacherMajorant
    rw [hleftExp, hrightExp]
  have hhalf : (1 + rWidth) - (1 / 2 + rWidth) = (1 / 2 : ℝ) := by
    ring
  rw [hhalf] at hbase
  exact hmajorantRewrite.le.trans hbase

/-- Exact endpoint sum for independent left and right offsets. -/
def ambientHorizontalGeneralEndpointNumerator
    (q : ℕ) (kappa rWidth delta X u : ℝ) : ℝ :=
  let A := 48 * (1 + kappa⁻¹) *
    Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1)
  let B := rightEdgePSeries rWidth * Real.exp ((1 + rWidth) ^ 2)
  Real.rpow A (((1 / 2 + rWidth) - delta) / (1 + rWidth)) *
      Real.rpow B ((delta + (1 / 2)) / (1 + rWidth)) *
      Real.rpow X delta +
    Real.rpow B 1 * Real.rpow X (1 / 2 + rWidth)

theorem ambientHorizontalGeneralEndpointNumerator_nonneg
    (q : ℕ) {kappa rWidth delta X u : ℝ}
    (hkappa : 0 < kappa) (hrWidth : 0 < rWidth) (hX : 0 < X) :
    0 ≤ ambientHorizontalGeneralEndpointNumerator q
      kappa rWidth delta X u := by
  unfold ambientHorizontalGeneralEndpointNumerator
  have hA0 : 0 ≤ 48 * (1 + kappa⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (kappa + 1) := by
    have : 0 ≤ 1 + kappa⁻¹ := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) this)
      (Real.rpow_nonneg (by positivity) _)
  have hB0 : 0 ≤ rightEdgePSeries rWidth *
      Real.exp ((1 + rWidth) ^ 2) := by
    have := one_le_rightEdgePSeries hrWidth
    positivity
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hA0 _)
        (Real.rpow_nonneg hB0 _))
      (Real.rpow_nonneg hX.le _))
    (mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hX.le _))

/-- Both horizontal edges on the literal Titchmarsh-to-Ramachandra
rectangle.  The independent right width is essential: setting it equal to
the much smaller Ramachandra offset would no longer match Theorem 3.19. -/
theorem norm_bhpHorizontalBoundaryIntegral_le_general_endpoints
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {kappa rWidth delta X t H : ℝ}
    (hkappa : 0 < kappa) (hkappaHalf : kappa ≤ 1 / 2)
    (hrWidth : 0 < rWidth) (hrWidthHalf : rWidth ≤ 1 / 2)
    (hdelta : 0 < delta) (hdeltaRight : delta ≤ 1 / 2 + rWidth)
    (hX : 0 < X) (hH : 0 < H) :
    ‖bhpHorizontalBoundaryIntegral chi X t delta
        (1 / 2 + rWidth) H‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (((ambientHorizontalGeneralEndpointNumerator q kappa rWidth delta
              X (t + H) / H) +
          (ambientHorizontalGeneralEndpointNumerator q kappa rWidth delta
              X (t - H) / H)) * (1 / 2 + rWidth - delta)) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hMtop0 : 0 ≤ ambientHorizontalGeneralEndpointNumerator q
      kappa rWidth delta X (t + H) / H :=
    div_nonneg
      (ambientHorizontalGeneralEndpointNumerator_nonneg q hkappa hrWidth hX)
      hH.le
  have hMbottom0 : 0 ≤ ambientHorizontalGeneralEndpointNumerator q
      kappa rWidth delta X (t - H) / H :=
    div_nonneg
      (ambientHorizontalGeneralEndpointNumerator_nonneg q hkappa hrWidth hX)
      hH.le
  apply norm_bhpHorizontalBoundaryIntegral_le_of_pointwise
    chi hdeltaRight hMtop0 hMbottom0
  · intro x hx
    have hx' : x ∈ Set.Ioc delta (1 / 2 + rWidth) := by
      have hdc : delta ≤ (2 : ℝ)⁻¹ + rWidth := by simpa using hdeltaRight
      simpa [Set.uIoc_of_le hdc] using hx
    have hraw := norm_bhpPerronIntegrand_horizontal_le_ambient
      hkappa hkappaHalf hrWidth hrWidthHalf chi hchi hX hH
      (X := X) (t := t) (H := H) (v := H) (x := x)
      (by simpa [abs_of_pos hH])
      (by linarith [hx'.1]) (by linarith [hx'.2])
    have hend := ambient_majorant_mul_rpow_le_general_endpoints
      hq hkappa hrWidth hdelta hX hx'.1.le hx'.2
      (q := q) (u := t + H)
    have hdiv := div_le_div_of_nonneg_right hend hH.le
    calc
      ‖bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * H)‖ ≤
          ambientRademacherMajorant q kappa rWidth
            ((1 / 2 : ℝ) + x) (t + H) *
              (Real.rpow X x / H) := hraw
      _ = (ambientRademacherMajorant q kappa rWidth
            ((1 / 2 : ℝ) + x) (t + H) * Real.rpow X x) / H := by ring
      _ ≤ ambientHorizontalGeneralEndpointNumerator q kappa rWidth delta
            X (t + H) / H := by
        simpa [ambientHorizontalGeneralEndpointNumerator] using hdiv
  · intro x hx
    have hx' : x ∈ Set.Ioc delta (1 / 2 + rWidth) := by
      have hdc : delta ≤ (2 : ℝ)⁻¹ + rWidth := by simpa using hdeltaRight
      simpa [Set.uIoc_of_le hdc] using hx
    have hraw := norm_bhpPerronIntegrand_horizontal_le_ambient
      hkappa hkappaHalf hrWidth hrWidthHalf chi hchi hX hH
      (X := X) (t := t) (H := H) (v := -H) (x := x)
      (by simp [abs_of_pos hH])
      (by linarith [hx'.1]) (by linarith [hx'.2])
    have hend := ambient_majorant_mul_rpow_le_general_endpoints
      hq hkappa hrWidth hdelta hX hx'.1.le hx'.2
      (q := q) (u := t - H)
    have hdiv := div_le_div_of_nonneg_right hend hH.le
    have himag : ((x : ℂ) - Complex.I * H) =
        ((x : ℂ) + Complex.I * (-H)) := by ring
    rw [himag]
    calc
      ‖bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * (-H))‖ ≤
          ambientRademacherMajorant q kappa rWidth
            ((1 / 2 : ℝ) + x) (t - H) *
              (Real.rpow X x / H) := by simpa using hraw
      _ = (ambientRademacherMajorant q kappa rWidth
            ((1 / 2 : ℝ) + x) (t - H) * Real.rpow X x) / H := by ring
      _ ≤ ambientHorizontalGeneralEndpointNumerator q kappa rWidth delta
            X (t - H) / H := by
        simpa [ambientHorizontalGeneralEndpointNumerator] using hdiv

/-- The exact sum of the two affine endpoint values, before division by the
horizontal height. -/
def ambientHorizontalEndpointNumerator
    (q : ℕ) (delta X u : ℝ) : ℝ :=
  let A := 48 * (1 + delta⁻¹) *
    Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1)
  let B := rightEdgePSeries delta * Real.exp ((1 + delta) ^ 2)
  Real.rpow A (((1 / 2 + delta) - delta) / (1 + delta)) *
      Real.rpow B ((delta + ((1 + delta) - (1 / 2 + delta))) /
        (1 + delta)) *
      Real.rpow X delta +
    Real.rpow B 1 * Real.rpow X (1 / 2 + delta)

theorem ambientHorizontalEndpointNumerator_nonneg
    (q : ℕ) {delta X u : ℝ} (hdelta : 0 < delta) (hX : 0 < X) :
    0 ≤ ambientHorizontalEndpointNumerator q delta X u := by
  unfold ambientHorizontalEndpointNumerator
  have hA0 : 0 ≤ 48 * (1 + delta⁻¹) *
      Real.rpow (2 * (q : ℝ) * (3 + |u|)) (delta + 1) := by
    have : 0 ≤ 1 + delta⁻¹ := by positivity
    exact mul_nonneg (mul_nonneg (by norm_num) this)
      (Real.rpow_nonneg (by positivity) _)
  have hB0 : 0 ≤ rightEdgePSeries delta *
      Real.exp ((1 + delta) ^ 2) := by
    have := one_le_rightEdgePSeries hdelta
    positivity
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (Real.rpow_nonneg hA0 _)
        (Real.rpow_nonneg hB0 _))
      (Real.rpow_nonneg hX.le _))
    (mul_nonneg (Real.rpow_nonneg hB0 _) (Real.rpow_nonneg hX.le _))

/-- Both literal horizontal edges, integrated after the exact affine endpoint
reduction.  The `/w` saving is the displayed division by `H`; no maximum or
unquantified Rademacher constant remains. -/
theorem norm_bhpHorizontalBoundaryIntegral_le_exact_endpoints
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hchi : chi ≠ 1)
    {delta X t H : ℝ} (hdelta : 0 < delta)
    (hdeltaHalf : delta ≤ 1 / 2) (hX : 0 < X) (hH : 0 < H) :
    ‖bhpHorizontalBoundaryIntegral chi X t delta
        (1 / 2 + delta) H‖ ≤
      ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
        (((ambientHorizontalEndpointNumerator q delta X (t + H) / H) +
          (ambientHorizontalEndpointNumerator q delta X (t - H) / H)) *
            (1 / 2)) := by
  have hq : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hdc : delta ≤ 1 / 2 + delta := by linarith
  have hMtop0 : 0 ≤
      ambientHorizontalEndpointNumerator q delta X (t + H) / H :=
    div_nonneg (ambientHorizontalEndpointNumerator_nonneg q hdelta hX) hH.le
  have hMbottom0 : 0 ≤
      ambientHorizontalEndpointNumerator q delta X (t - H) / H :=
    div_nonneg (ambientHorizontalEndpointNumerator_nonneg q hdelta hX) hH.le
  suffices hbound :
      ‖bhpHorizontalBoundaryIntegral chi X t delta
          (1 / 2 + delta) H‖ ≤
        ‖((((2 * Real.pi : ℝ) : ℂ)⁻¹) * Complex.I)‖ *
          (((ambientHorizontalEndpointNumerator q delta X (t + H) / H) +
            (ambientHorizontalEndpointNumerator q delta X (t - H) / H)) *
              ((1 / 2 + delta) - delta)) by
    simpa only [add_sub_cancel_right] using hbound
  apply norm_bhpHorizontalBoundaryIntegral_le_of_pointwise
    chi hdc hMtop0 hMbottom0
  · intro x hx
    have hx' : x ∈ Set.Ioc delta (1 / 2 + delta) := by
      simpa [Set.uIoc_of_le hdc] using hx
    have hraw := norm_bhpPerronIntegrand_horizontal_le_ambient
      hdelta hdeltaHalf hdelta hdeltaHalf chi hchi hX hH
      (X := X) (t := t) (H := H) (v := H) (x := x)
      (by simpa [abs_of_pos hH])
      (by linarith [hx'.1]) (by linarith [hx'.2])
    have hend := ambient_majorant_mul_rpow_le_endpoints
      hq hdelta hX hx'.1.le hx'.2
      (q := q) (u := t + H)
    have hdiv := div_le_div_of_nonneg_right hend hH.le
    calc
      ‖bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * H)‖ ≤
          ambientRademacherMajorant q delta delta
            ((1 / 2 : ℝ) + x) (t + H) *
              (Real.rpow X x / H) := hraw
      _ = (ambientRademacherMajorant q delta delta
            ((1 / 2 : ℝ) + x) (t + H) * Real.rpow X x) / H := by ring
      _ ≤ ambientHorizontalEndpointNumerator q delta X (t + H) / H := by
        simpa [ambientHorizontalEndpointNumerator] using hdiv
  · intro x hx
    have hx' : x ∈ Set.Ioc delta (1 / 2 + delta) := by
      simpa [Set.uIoc_of_le hdc] using hx
    have hraw := norm_bhpPerronIntegrand_horizontal_le_ambient
      hdelta hdeltaHalf hdelta hdeltaHalf chi hchi hX hH
      (X := X) (t := t) (H := H) (v := -H) (x := x)
      (by simp [abs_of_pos hH])
      (by linarith [hx'.1]) (by linarith [hx'.2])
    have hend := ambient_majorant_mul_rpow_le_endpoints
      hq hdelta hX hx'.1.le hx'.2
      (q := q) (u := t - H)
    have hdiv := div_le_div_of_nonneg_right hend hH.le
    have himag : ((x : ℂ) - Complex.I * H) =
        ((x : ℂ) + Complex.I * (-H)) := by ring
    rw [himag]
    calc
      ‖bhpPerronIntegrand chi X t ((x : ℂ) + Complex.I * (-H))‖ ≤
          ambientRademacherMajorant q delta delta
            ((1 / 2 : ℝ) + x) (t - H) *
              (Real.rpow X x / H) := by simpa using hraw
      _ = (ambientRademacherMajorant q delta delta
            ((1 / 2 : ℝ) + x) (t - H) * Real.rpow X x) / H := by ring
      _ ≤ ambientHorizontalEndpointNumerator q delta X (t - H) / H := by
        simpa [ambientHorizontalEndpointNumerator] using hdiv

end
end MAPBHPHorizontalEndpointInterpolation

#print axioms MAPBHPHorizontalEndpointInterpolation.weighted_strip_interpolation_le_endpoint_sum
#print axioms MAPBHPHorizontalEndpointInterpolation.norm_bhpPerronIntegrand_horizontal_le_ambient
#print axioms MAPBHPHorizontalEndpointInterpolation.ambient_majorant_mul_rpow_le_endpoints
#print axioms MAPBHPHorizontalEndpointInterpolation.norm_bhpHorizontalBoundaryIntegral_le_exact_endpoints
#print axioms MAPBHPHorizontalEndpointInterpolation.ambient_majorant_mul_rpow_le_general_endpoints
#print axioms MAPBHPHorizontalEndpointInterpolation.ambientHorizontalGeneralEndpointNumerator_nonneg
#print axioms MAPBHPHorizontalEndpointInterpolation.norm_bhpHorizontalBoundaryIntegral_le_general_endpoints
