import MixedMeanFrontend
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Unconditional harmonic front end for the mixed mean

This module starts with `MixedMeanFrontend.literalMixedMean`.  It proves the
finite Fubini normalization and separates the two Mellin clocks before making
any counting assumption.  It also records the literal sinc-square majorant
and converts logarithmic support bands to honest natural-number collars.

No mixed-mean estimate, Shiu estimate, or weighted tuple-count estimate is an
assumption of any theorem in this file.
-/

noncomputable section

namespace MAPMixedHarmonic

open MeasureTheory
open DeterminantCountWeld
open MixedMeanFrontend
open FourierTransform

/-! ## Exact finite Fubini and clock separation -/

/-- The elementary oscillatory moment on a finite interval. -/
def intervalOsc (a b omega : ℝ) : ℂ :=
  ∫ x in a..b,
    Complex.exp ((((x * omega : ℝ) : ℂ) * Complex.I))

theorem intervalIntegrable_tupleTerm_u
    (β g : ℕ → ℂ) (q : LiteralTuple) (t a b : ℝ) :
    IntervalIntegrable (fun u : ℝ ↦ tupleTerm β g q t u) volume a b := by
  apply Continuous.intervalIntegrable
  rw [show (fun u : ℝ ↦ tupleTerm β g q t u) =
      fun u : ℝ ↦ tupleCoefficient β g q *
        Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I) by
    funext u
    exact tupleTerm_frequency_form β g q t u]
  fun_prop

/-- The independent `u` integral is a constant coefficient times its short
frequency moment.  This is the first normalization step needed in the paper's
finite Fubini argument. -/
theorem integral_tupleTerm_u_eq
    (β g : ℕ → ℂ) (q : LiteralTuple) (t a b : ℝ) :
    (∫ u in a..b, tupleTerm β g q t u) =
      tupleCoefficient β g q *
        Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
        intervalOsc a b (shortFrequency q) := by
  rw [show (fun u : ℝ ↦ tupleTerm β g q t u) =
      fun u : ℝ ↦ tupleCoefficient β g q *
        Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I) by
    funext u
    exact tupleTerm_frequency_form β g q t u]
  unfold intervalOsc
  have hexp (u : ℝ) :
      Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I) =
        Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
          Complex.exp ((((u * shortFrequency q : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (∫ u in a..b, tupleCoefficient β g q *
        Complex.exp
          (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
            Complex.I)) =
      ∫ u in a..b,
        (tupleCoefficient β g q *
          Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I))) *
          Complex.exp ((((u * shortFrequency q : ℝ) : ℂ) * Complex.I)) := by
            apply intervalIntegral.integral_congr
            intro u hu
            change tupleCoefficient β g q *
                Complex.exp
                  (((t * jointFrequency q + u * shortFrequency q : ℝ) : ℂ) *
                    Complex.I) =
              (tupleCoefficient β g q *
                Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I))) *
                Complex.exp ((((u * shortFrequency q : ℝ) : ℂ) * Complex.I))
            rw [hexp]
            ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]

theorem intervalIntegrable_integral_tupleTerm_u
    (β g : ℕ → ℂ) (q : LiteralTuple) (a b c d : ℝ) :
    IntervalIntegrable (fun t : ℝ ↦ ∫ u in c..d, tupleTerm β g q t u)
      volume a b := by
  rw [show (fun t : ℝ ↦ ∫ u in c..d, tupleTerm β g q t u) =
      fun t : ℝ ↦ tupleCoefficient β g q *
        Complex.exp ((((t * jointFrequency q : ℝ) : ℂ) * Complex.I)) *
          intervalOsc c d (shortFrequency q) by
    funext t
    exact integral_tupleTerm_u_eq β g q t c d]
  apply Continuous.intervalIntegrable
  fun_prop

/-- Every tuple's iterated integral factors into the product of the two
independent oscillatory moments. -/
theorem iteratedIntegral_tupleTerm_eq
    (β g : ℕ → ℂ) (q : LiteralTuple) (a b c d : ℝ) :
    (∫ t in a..b, ∫ u in c..d, tupleTerm β g q t u) =
      tupleCoefficient β g q *
        intervalOsc a b (jointFrequency q) *
        intervalOsc c d (shortFrequency q) := by
  simp_rw [integral_tupleTerm_u_eq, intervalOsc]
  rw [show (fun t : ℝ ↦ tupleCoefficient β g q *
      Complex.exp (↑(t * jointFrequency q) * Complex.I) *
        ∫ (x : ℝ) in c..d, Complex.exp (↑(x * shortFrequency q) * Complex.I)) =
    fun t : ℝ ↦ (tupleCoefficient β g q *
      Complex.exp (↑(t * jointFrequency q) * Complex.I)) *
        (∫ (x : ℝ) in c..d,
          Complex.exp (↑(x * shortFrequency q) * Complex.I)) by rfl]
  rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_const_mul]

/-- Exact finite Fubini normalization from the literal mixed mean to a sum of
factored tuple moments.  There is no quadrature and no analytic estimate in
this identity. -/
theorem literalMixedMean_eq_sum_factored
    (M N : ℕ) (β g : ℕ → ℂ) (t₀ T U : ℝ) :
    literalMixedMean M N β g t₀ T U =
      ∑ q ∈ dyadicTupleBox M N,
        tupleCoefficient β g q *
          intervalOsc (t₀ - T / 2) (t₀ + T / 2) (jointFrequency q) *
          intervalOsc (-2 * U) (2 * U) (shortFrequency q) := by
  rw [literalMixedMean_eq_integral_tupleSum]
  calc
    (∫ t in (t₀ - T / 2)..(t₀ + T / 2),
        ∫ u in (-2 * U)..(2 * U),
          ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u) =
      ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
        ∑ q ∈ dyadicTupleBox M N,
          ∫ u in (-2 * U)..(2 * U), tupleTerm β g q t u := by
        apply intervalIntegral.integral_congr
        intro t ht
        change (∫ u in (-2 * U)..(2 * U),
            ∑ q ∈ dyadicTupleBox M N, tupleTerm β g q t u) =
          ∑ q ∈ dyadicTupleBox M N,
            ∫ u in (-2 * U)..(2 * U), tupleTerm β g q t u
        rw [intervalIntegral.integral_finsetSum]
        intro q hq
        exact intervalIntegrable_tupleTerm_u β g q t _ _
    _ = ∑ q ∈ dyadicTupleBox M N,
          ∫ t in (t₀ - T / 2)..(t₀ + T / 2),
            ∫ u in (-2 * U)..(2 * U), tupleTerm β g q t u := by
        rw [intervalIntegral.integral_finsetSum]
        intro q hq
        exact intervalIntegrable_integral_tupleTerm_u β g q _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact iteratedIntegral_tupleTerm_eq β g q _ _ _ _

/-! ## Elementary Fourier integration helpers -/

def affinePrimitive (A B c : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (c * (x : ℂ)) * ((A + B * (x : ℂ)) / c - B / c ^ 2)

theorem hasDerivAt_affinePrimitive (A B c : ℂ) (hc : c ≠ 0) (x : ℝ) :
    HasDerivAt (affinePrimitive A B c)
      ((A + B * (x : ℂ)) * Complex.exp (c * (x : ℂ))) x := by
  have hid : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x :=
    (hasDerivAt_id (x : ℂ)).comp_ofReal
  have hcx : HasDerivAt (fun y : ℝ ↦ c * (y : ℂ)) c x := by
    convert hid.const_mul c using 1 <;> ring
  have hexp : HasDerivAt (fun y : ℝ ↦ Complex.exp (c * (y : ℂ)))
      (Complex.exp (c * (x : ℂ)) * c) x := hcx.cexp
  have haff : HasDerivAt (fun y : ℝ ↦ A + B * (y : ℂ)) B x := by
    convert (hid.const_mul B).const_add A using 1 <;> ring
  have hbracket : HasDerivAt
      (fun y : ℝ ↦ (A + B * (y : ℂ)) / c - B / c ^ 2) (B / c) x := by
    convert (haff.div_const c).sub_const (B / c ^ 2) using 1 <;> ring
  unfold affinePrimitive
  convert hexp.mul hbracket using 1
  field_simp [hc]
  ring

theorem integral_affine_mul_exp (A B c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    (∫ x in a..b, (A + B * (x : ℂ)) * Complex.exp (c * (x : ℂ))) =
      affinePrimitive A B c b - affinePrimitive A B c a := by
  apply intervalIntegral.integral_deriv_eq_sub' (affinePrimitive A B c)
  · funext x
    exact (hasDerivAt_affinePrimitive A B c hc x).deriv
  · intro x hx
    exact (hasDerivAt_affinePrimitive A B c hc x).differentiableAt
  · fun_prop

def affineZeroPrimitive (A B : ℂ) (x : ℝ) : ℂ :=
  A * (x : ℂ) + B * (x : ℂ) ^ 2 / 2

theorem hasDerivAt_affineZeroPrimitive (A B : ℂ) (x : ℝ) :
    HasDerivAt (affineZeroPrimitive A B) (A + B * (x : ℂ)) x := by
  have hid : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 x :=
    (hasDerivAt_id (x : ℂ)).comp_ofReal
  unfold affineZeroPrimitive
  convert (hid.const_mul A).add (((hid.pow 2).const_mul B).div_const 2) using 1 <;> ring

theorem integral_affine (A B : ℂ) (a b : ℝ) :
    (∫ x in a..b, (A + B * (x : ℂ))) =
      affineZeroPrimitive A B b - affineZeroPrimitive A B a := by
  apply intervalIntegral.integral_deriv_eq_sub' (affineZeroPrimitive A B)
  · funext x
    exact (hasDerivAt_affineZeroPrimitive A B x).deriv
  · intro x hx
    exact (hasDerivAt_affineZeroPrimitive A B x).differentiableAt
  · fun_prop

/-! ## Literal sinc-square kernel -/

/-- The paper's kernel `eta(v) = (sin (pi v / 4)/(pi v/4))^2`, using
Mathlib's total value `sinc 0 = 1`. -/
def eta (v : ℝ) : ℝ := Real.sinc (Real.pi * v / 4) ^ 2

theorem eta_nonneg (v : ℝ) : 0 ≤ eta v := by
  exact sq_nonneg _

theorem eta_continuous : Continuous eta := by
  unfold eta
  fun_prop

theorem eta_le_one (v : ℝ) : eta v ≤ 1 := by
  unfold eta
  calc
    Real.sinc (Real.pi * v / 4) ^ 2 =
        |Real.sinc (Real.pi * v / 4)| ^ 2 := (sq_abs _).symm
    _ ≤ 1 ^ 2 := (sq_le_sq₀ (abs_nonneg _ ) zero_le_one).2
      (Real.abs_sinc_le_one _)
    _ = 1 := by norm_num

/-- A global integrable envelope for the sinc-square kernel.  The constant is
deliberately loose; the point is a checked `L¹` fact, not constant
optimization. -/
theorem eta_le_cauchy_envelope (v : ℝ) :
    eta v ≤ 8 * (1 + v ^ 2)⁻¹ := by
  by_cases hvsmall : |v| ≤ 1
  · have hvsq : v ^ 2 ≤ 1 := by
      rw [← sq_abs]
      simpa using (sq_le_sq₀ (abs_nonneg v) zero_le_one).2 hvsmall
    have hden : 0 < 1 + v ^ 2 := by positivity
    calc
      eta v ≤ 1 := eta_le_one v
      _ ≤ 8 * (1 + v ^ 2)⁻¹ := by
        change 1 ≤ 8 / (1 + v ^ 2)
        apply (le_div_iff₀ hden).2
        nlinarith
  · have hvabs : 1 < |v| := lt_of_not_ge hvsmall
    have hv0 : v ≠ 0 := by
      intro hv
      subst v
      norm_num at hvabs
    let z : ℝ := Real.pi * v / 4
    have hz0 : z ≠ 0 := by
      dsimp [z]
      exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv0) (by norm_num)
    have hsin : Real.sin z ^ 2 ≤ 1 := by
      calc
        Real.sin z ^ 2 = |Real.sin z| ^ 2 := (sq_abs _).symm
        _ ≤ 1 ^ 2 := (sq_le_sq₀ (abs_nonneg _) zero_le_one).2
          (Real.abs_sin_le_one z)
        _ = 1 := by norm_num
    have hpilo : 4 ≤ Real.pi ^ 2 := by
      nlinarith [Real.one_le_pi_div_two]
    have hzsq : z ^ 2 = Real.pi ^ 2 * v ^ 2 / 16 := by
      dsimp [z]
      ring
    have hzsqpos : 0 < z ^ 2 := sq_pos_of_ne_zero hz0
    have hvsqpos : 0 < v ^ 2 := sq_pos_of_ne_zero hv0
    have heta_decay : eta v ≤ 4 / v ^ 2 := by
      unfold eta
      rw [Real.sinc_of_ne_zero hz0]
      calc
        (Real.sin z / z) ^ 2 = Real.sin z ^ 2 / z ^ 2 := by ring
        _ ≤ 1 / z ^ 2 :=
          div_le_div_of_nonneg_right hsin hzsqpos.le
        _ ≤ 4 / v ^ 2 := by
          apply (div_le_div_iff₀ hzsqpos hvsqpos).2
          rw [hzsq]
          nlinarith [sq_nonneg v]
    have hvsqlower : 1 ≤ v ^ 2 := by
      rw [← sq_abs]
      simpa using (sq_le_sq₀ zero_le_one (abs_nonneg v)).2 hvabs.le
    calc
      eta v ≤ 4 / v ^ 2 := heta_decay
      _ ≤ 8 * (1 + v ^ 2)⁻¹ := by
        change 4 / v ^ 2 ≤ 8 / (1 + v ^ 2)
        apply (div_le_div_iff₀ hvsqpos (by positivity : 0 < 1 + v ^ 2)).2
        nlinarith

theorem eta_integrable : Integrable eta := by
  apply Integrable.mono'
    (integrable_inv_one_add_sq.const_mul (8 : ℝ))
    eta_continuous.aestronglyMeasurable
  filter_upwards with v
  rw [Real.norm_eq_abs, abs_of_nonneg (eta_nonneg v)]
  exact eta_le_cauchy_envelope v

/-- The compact triangular profile paired with `eta` under Mathlib's Fourier
normalization.  Its checked support is the paper's `[-1/4,1/4]` band. -/
def triangularProfile (xi : ℝ) : ℂ :=
  ((4 * max (1 - 4 * |xi|) 0 : ℝ) : ℂ)

theorem triangularProfile_continuous : Continuous triangularProfile := by
  unfold triangularProfile
  fun_prop

theorem triangularProfile_eq_zero_of_band
    {xi : ℝ} (hxi : 1 / 4 ≤ |xi|) :
    triangularProfile xi = 0 := by
  unfold triangularProfile
  have hnonpos : 1 - 4 * |xi| ≤ 0 := by linarith
  rw [max_eq_right hnonpos]
  norm_num

theorem support_triangularProfile_subset :
    Function.support triangularProfile ⊆ Set.Ioo (-(1 / 4 : ℝ)) (1 / 4) := by
  intro xi hxi
  rw [Function.mem_support] at hxi
  have habs : |xi| < 1 / 4 := by
    by_contra h
    exact hxi (triangularProfile_eq_zero_of_band (le_of_not_gt h))
  rw [abs_lt] at habs
  exact habs

theorem triangularProfile_integrable : Integrable triangularProfile := by
  apply triangularProfile_continuous.integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (support_triangularProfile_subset.trans Set.Ioo_subset_Icc_self)

/-! ## Exact Fourier pair for the paper kernel -/

theorem triangular_left {x : ℝ} (hx : x ∈ Set.Icc (-(1 / 4 : ℝ)) 0) :
    triangularProfile x = (4 + 16 * x : ℂ) := by
  unfold triangularProfile
  rw [abs_of_nonpos hx.2]
  have hpos : 0 ≤ 1 - 4 * -x := by linarith [hx.1]
  rw [max_eq_left hpos]
  push_cast
  ring

theorem triangular_right {x : ℝ} (hx : x ∈ Set.Icc 0 (1 / 4 : ℝ)) :
    triangularProfile x = (4 - 16 * x : ℂ) := by
  unfold triangularProfile
  rw [abs_of_nonneg hx.1]
  have hpos : 0 ≤ 1 - 4 * x := by linarith [hx.2]
  rw [max_eq_left hpos]
  push_cast
  ring

theorem fourierInv_triangular_formula {v : ℝ} (hv : v ≠ 0) :
    𝓕⁻ triangularProfile v =
      affinePrimitive 4 16 ((2 * Real.pi * v : ℝ) * Complex.I) 0 -
          affinePrimitive 4 16 ((2 * Real.pi * v : ℝ) * Complex.I) (-(1 / 4)) +
        (affinePrimitive 4 (-16) ((2 * Real.pi * v : ℝ) * Complex.I) (1 / 4) -
          affinePrimitive 4 (-16) ((2 * Real.pi * v : ℝ) * Complex.I) 0) := by
  let c : ℂ := (2 * Real.pi * v : ℝ) * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hv)) Complex.I_ne_zero
  rw [Real.fourierInv_eq']
  have hsupp : Function.support
      (fun x : ℝ ↦ Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
        triangularProfile x) ⊆ Set.Ioc (-(1 / 4 : ℝ)) (1 / 4) := by
    intro x hx
    rw [Function.mem_support] at hx
    have htri : triangularProfile x ≠ 0 := by
      intro hz
      simp [hz] at hx
    have hi := support_triangularProfile_subset (Function.mem_support.2 htri)
    exact ⟨hi.1, hi.2.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hcont : Continuous (fun x : ℝ ↦
      Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
        triangularProfile x) := by
    apply Continuous.smul
    · fun_prop
    · exact triangularProfile_continuous
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (-(1 / 4 : ℝ))) (b := 0) (c := (1 / 4 : ℝ))
    (f := fun x : ℝ ↦
      Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) • triangularProfile x)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · calc
      (∫ x in (-(1 / 4 : ℝ))..0,
          Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
            triangularProfile x) =
        ∫ x in (-(1 / 4 : ℝ))..0,
          (4 + 16 * (x : ℂ)) * Complex.exp (c * (x : ℂ)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
                triangularProfile x =
              (4 + 16 * (x : ℂ)) * Complex.exp (c * (x : ℂ))
            rw [triangular_left (by simpa using hx)]
            rw [smul_eq_mul, mul_comm]
            congr 1
            dsimp [c]
            congr 1
            simp [RCLike.inner_apply]
            push_cast
            ring
      _ = _ := integral_affine_mul_exp 4 16 c hc _ _
  · calc
      (∫ x in (0 : ℝ)..(1 / 4),
          Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
            triangularProfile x) =
        ∫ x in (0 : ℝ)..(1 / 4),
          (4 - 16 * (x : ℂ)) * Complex.exp (c * (x : ℂ)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            change Complex.exp (↑(2 * Real.pi * inner ℝ x v) * Complex.I) •
                triangularProfile x =
              (4 - 16 * (x : ℂ)) * Complex.exp (c * (x : ℂ))
            rw [triangular_right (by simpa using hx)]
            rw [smul_eq_mul, mul_comm]
            congr 1
            dsimp [c]
            congr 1
            simp [RCLike.inner_apply]
            push_cast
            ring
      _ = ∫ x in (0 : ℝ)..(1 / 4),
          (4 + (-16) * (x : ℂ)) * Complex.exp (c * (x : ℂ)) := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
      _ = _ := integral_affine_mul_exp 4 (-16) c hc _ _

theorem triangular_formula_eq_eta {v : ℝ} (hv : v ≠ 0) :
    affinePrimitive 4 16 ((2 * Real.pi * v : ℝ) * Complex.I) 0 -
          affinePrimitive 4 16 ((2 * Real.pi * v : ℝ) * Complex.I) (-(1 / 4)) +
        (affinePrimitive 4 (-16) ((2 * Real.pi * v : ℝ) * Complex.I) (1 / 4) -
          affinePrimitive 4 (-16) ((2 * Real.pi * v : ℝ) * Complex.I) 0) =
      (eta v : ℂ) := by
  have hpiv : Real.pi * v ≠ 0 := mul_ne_zero Real.pi_ne_zero hv
  unfold affinePrimitive eta
  rw [Real.sinc_of_ne_zero (div_ne_zero hpiv (by norm_num))]
  simp
  field_simp [hv]
  ring_nf
  field_simp
  let z : ℂ := (Real.pi : ℂ) * (v : ℂ) / 4
  have hpos :
      Complex.exp ((Real.pi : ℂ) * (v : ℂ) * Complex.I / 2) =
        Complex.cos (2 * z) + Complex.sin (2 * z) * Complex.I := by
    rw [show (Real.pi : ℂ) * (v : ℂ) * Complex.I / 2 =
        (2 * z) * Complex.I by dsimp [z]; ring]
    exact Complex.exp_mul_I _
  have hneg :
      Complex.exp (-((Real.pi : ℂ) * (v : ℂ) * Complex.I / 2)) =
        Complex.cos (2 * z) - Complex.sin (2 * z) * Complex.I := by
    rw [show -((Real.pi : ℂ) * (v : ℂ) * Complex.I / 2) =
        (-2 * z) * Complex.I by dsimp [z]; ring]
    rw [Complex.exp_mul_I]
    simp
    ring
  rw [hpos, hneg, Complex.I_sq]
  have hz : (Real.pi : ℂ) * (v : ℂ) / 4 = z := rfl
  rw [hz, Complex.cos_two_mul, Complex.sin_sq]
  ring

theorem fourierInv_triangular_zero :
    𝓕⁻ triangularProfile (0 : ℝ) = (eta 0 : ℂ) := by
  rw [Real.fourierInv_eq']
  simp only [inner_zero_right, mul_zero]
  simp
  have hsupp : Function.support triangularProfile ⊆
      Set.Ioc (-(1 / 4 : ℝ)) (1 / 4) := fun x hx ↦
    let h := support_triangularProfile_subset hx
    ⟨h.1, h.2.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (triangularProfile_continuous.intervalIntegrable _ _)
    (triangularProfile_continuous.intervalIntegrable _ _)]
  have hleft :
      (∫ x in (-(1 / 4 : ℝ))..0, triangularProfile x) = (1 / 2 : ℂ) := by
    calc
      _ = ∫ x in (-(1 / 4 : ℝ))..0, (4 + 16 * (x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact triangular_left (by simpa using hx)
      _ = _ := by
        rw [integral_affine]
        norm_num [affineZeroPrimitive]
  have hright :
      (∫ x in (0 : ℝ)..(1 / 4), triangularProfile x) = (1 / 2 : ℂ) := by
    calc
      _ = ∫ x in (0 : ℝ)..(1 / 4), (4 + (-16) * (x : ℂ)) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [triangular_right (by simpa using hx)]
        ring
      _ = _ := by
        rw [integral_affine]
        norm_num [affineZeroPrimitive]
  rw [hleft, hright]
  norm_num [eta]

theorem fourierInv_triangular_eq_eta (v : ℝ) :
    𝓕⁻ triangularProfile v = (eta v : ℂ) := by
  by_cases hv : v = 0
  · simpa [hv] using fourierInv_triangular_zero
  · exact (fourierInv_triangular_formula hv).trans (triangular_formula_eq_eta hv)

theorem fourier_triangular_eq_eta (v : ℝ) :
    𝓕 triangularProfile v = (eta v : ℂ) := by
  have h := fourierInv_triangular_eq_eta (-v)
  rw [Real.fourierInv_eq_fourier_neg] at h
  simp only [neg_neg] at h
  unfold eta at h ⊢
  rw [show Real.pi * -v / 4 = -(Real.pi * v / 4) by ring, Real.sinc_neg] at h
  exact h

theorem fourier_triangular_integrable : Integrable (𝓕 triangularProfile) := by
  have hetaC : Integrable (fun v : ℝ ↦ (eta v : ℂ)) := eta_integrable.ofReal
  exact hetaC.congr (Filter.Eventually.of_forall fun v ↦ (fourier_triangular_eq_eta v).symm)

theorem fourier_eta_eq_triangularProfile :
    𝓕 (fun v : ℝ ↦ (eta v : ℂ)) = triangularProfile := by
  have hinv : 𝓕⁻ triangularProfile = (fun v : ℝ ↦ (eta v : ℂ)) := by
    funext v
    exact fourierInv_triangular_eq_eta v
  rw [← hinv]
  exact triangularProfile_continuous.fourier_fourierInv_eq
    triangularProfile_integrable fourier_triangular_integrable

theorem fourier_eta_eq_zero_of_band
    {xi : ℝ} (hxi : 1 / 4 ≤ |xi|) :
    𝓕 (fun v : ℝ ↦ (eta v : ℂ)) xi = 0 := by
  rw [fourier_eta_eq_triangularProfile]
  exact triangularProfile_eq_zero_of_band hxi

/-! ## Angular-frequency support conversion -/

def etaAngularMoment (omega : ℝ) : ℂ :=
  ∫ v : ℝ, (eta v : ℂ) * Complex.exp (((omega * v : ℝ) : ℂ) * Complex.I)

theorem etaAngularMoment_eq_fourier (omega : ℝ) :
    etaAngularMoment omega =
      𝓕 (fun v : ℝ ↦ (eta v : ℂ)) (-omega / (2 * Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold etaAngularMoment
  apply integral_congr_ae
  filter_upwards with v
  rw [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  congr 1
  field_simp [Real.pi_ne_zero]

theorem etaAngularMoment_eq_zero_of_band
    {omega : ℝ} (homega : Real.pi / 2 ≤ |omega|) :
    etaAngularMoment omega = 0 := by
  rw [etaAngularMoment_eq_fourier]
  apply fourier_eta_eq_zero_of_band
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
  norm_num [abs_neg]
  rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
  nlinarith [Real.pi_pos]


/-- The whole-line sinc-square moment at scale `S` and center `center`. -/
def scaledEtaAngularMoment (S center omega : ℝ) : ℂ :=
  ∫ t : ℝ, (eta ((t - center) / S) : ℂ) *
    Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)

theorem scaledEtaAngularMoment_eq
    {S : ℝ} (hS : 0 < S) (center omega : ℝ) :
    scaledEtaAngularMoment S center omega =
      (S : ℂ) * Complex.exp ((((omega * center : ℝ) : ℂ) * Complex.I)) *
        etaAngularMoment (S * omega) := by
  let F : ℝ → ℂ := fun t ↦ (eta ((t - center) / S) : ℂ) *
    Complex.exp (((omega * t : ℝ) : ℂ) * Complex.I)
  have hscale := Measure.integral_comp_mul_left
    (fun y : ℝ ↦ F (center + y)) S
  rw [integral_add_left_eq_self F center] at hscale
  have habsinv : |S⁻¹| = S⁻¹ := abs_of_pos (inv_pos.mpr hS)
  rw [habsinv] at hscale
  rw [Complex.real_smul] at hscale
  have hF : (∫ t : ℝ, F t) = (S : ℂ) * ∫ v : ℝ, F (center + S * v) := by
    rw [hscale]
    push_cast
    field_simp [hS.ne']
  unfold scaledEtaAngularMoment
  change (∫ t : ℝ, F t) = _
  rw [hF]
  have hpoint (v : ℝ) : F (center + S * v) =
      Complex.exp ((((omega * center : ℝ) : ℂ) * Complex.I)) *
        ((eta v : ℂ) * Complex.exp ((((S * omega * v : ℝ) : ℂ) * Complex.I))) := by
    dsimp [F]
    have harg : (center + S * v - center) / S = v := by
      field_simp [hS.ne']
      ring
    rw [harg]
    rw [show omega * (center + S * v) = omega * center + (S * omega * v) by ring]
    push_cast
    rw [add_mul, Complex.exp_add]
    ring
  simp_rw [hpoint]
  rw [integral_const_mul]
  unfold etaAngularMoment
  ring

theorem scaledEtaAngularMoment_eq_zero_of_band
    {S : ℝ} (hS : 0 < S) (center omega : ℝ)
    (homega : Real.pi / (2 * S) ≤ |omega|) :
    scaledEtaAngularMoment S center omega = 0 := by
  rw [scaledEtaAngularMoment_eq hS]
  rw [etaAngularMoment_eq_zero_of_band]
  · ring
  · rw [abs_mul, abs_of_pos hS]
    calc
      Real.pi / 2 = S * (Real.pi / (2 * S)) := by
        field_simp [hS.ne']
      _ ≤ S * |omega| := mul_le_mul_of_nonneg_left homega hS.le


/-! ## Exact support weld to the checked tuple model -/

/-- The exact coefficient attached to a tuple after both sinc-square clocks
have been integrated over the whole line. -/
def sincWeightedTupleTerm (β g : ℕ → ℂ) (St center Su : ℝ)
    (q : LiteralTuple) : ℂ :=
  tupleCoefficient β g q *
    scaledEtaAngularMoment St center (jointFrequency q) *
    scaledEtaAngularMoment Su 0 (shortFrequency q)

/-- The whole dyadic tuple model produced by the two exact Fourier moments. -/
def sincWeightedTupleModel (M N : ℕ) (β g : ℕ → ℂ)
    (St center Su : ℝ) : ℂ :=
  ∑ q ∈ dyadicTupleBox M N, sincWeightedTupleTerm β g St center Su q

/-- The same model restricted to the simultaneous Fourier survivor set. -/
def checkedSincTupleModel (M N : ℕ) (β g : ℕ → ℂ)
    (St center Su : ℝ) : ℂ :=
  ∑ q ∈ frequencyTuples M N (Real.pi / (2 * Su)) (Real.pi / (2 * St)),
    sincWeightedTupleTerm β g St center Su q

/-- Exact support weld: after evaluating the two literal sinc-square moments,
all tuples outside the checked simultaneous-frequency set vanish termwise. -/
theorem sincWeightedTupleModel_eq_checked
    (M N : ℕ) (β g : ℕ → ℂ)
    {St Su : ℝ} (hSt : 0 < St) (hSu : 0 < Su) (center : ℝ) :
    sincWeightedTupleModel M N β g St center Su =
      checkedSincTupleModel M N β g St center Su := by
  unfold sincWeightedTupleModel checkedSincTupleModel frequencyTuples
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hsurv :
      |shortFrequency q| ≤ Real.pi / (2 * Su) ∧
        |jointFrequency q| ≤ Real.pi / (2 * St)
  · simp [hsurv]
  · rw [if_neg hsurv]
    rcases not_and_or.mp hsurv with hshort | hjoint
    · have hz := scaledEtaAngularMoment_eq_zero_of_band hSu 0 (shortFrequency q)
          (le_of_not_ge hshort)
      unfold sincWeightedTupleTerm
      rw [hz]
      ring
    · have hz := scaledEtaAngularMoment_eq_zero_of_band hSt center (jointFrequency q)
          (le_of_not_ge hjoint)
      unfold sincWeightedTupleTerm
      rw [hz]
      ring


/-- Jordan's inequality gives the fixed majorant used for both the central
`t` interval and the larger `u` interval. -/
theorem one_le_four_mul_eta_of_abs_le_two {v : ℝ} (hv : |v| ≤ 2) :
    1 ≤ 4 * eta v := by
  by_cases hv0 : v = 0
  · simp [hv0, eta]
  have hx0 : Real.pi * v / 4 ≠ 0 := by
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hv0) (by norm_num)
  have hxband : |Real.pi * v / 4| ≤ Real.pi / 2 := by
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num at hv ⊢
    nlinarith [Real.pi_pos]
  have hj := Real.mul_abs_le_abs_sin hxband
  have hratio : 2 / Real.pi ≤ |Real.sin (Real.pi * v / 4)| /
      |Real.pi * v / 4| := by
    apply (le_div_iff₀ (abs_pos.mpr hx0)).2
    simpa [mul_assoc] using hj
  have hpi : Real.pi ^ 2 ≤ 16 := by
    nlinarith [Real.pi_pos, Real.pi_le_four]
  unfold eta
  rw [Real.sinc_of_ne_zero hx0]
  have hsquare : (2 / Real.pi) ^ 2 ≤
      (Real.sin (Real.pi * v / 4) / (Real.pi * v / 4)) ^ 2 := by
    have hleft : 0 ≤ 2 / Real.pi := by positivity
    have habs : 2 / Real.pi ≤
        |Real.sin (Real.pi * v / 4) / (Real.pi * v / 4)| := by
      simpa [abs_div] using hratio
    nlinarith [sq_abs (Real.sin (Real.pi * v / 4) /
      (Real.pi * v / 4))]
  have hbase : 1 ≤ 4 * (2 / Real.pi) ^ 2 := by
    calc
      1 ≤ 16 / Real.pi ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos Real.pi_pos)).2 (by simpa using hpi)
      _ = 4 * (2 / Real.pi) ^ 2 := by ring
  exact hbase.trans (mul_le_mul_of_nonneg_left hsquare (by norm_num))

/-! ## Logarithmic support to arithmetic collars -/

/-- The elementary mean-value-free inequality behind both collar
conversions. -/
theorem abs_sub_le_max_mul_abs_log_sub
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| ≤ max x y * |Real.log x - Real.log y| := by
  wlog hxy : x ≤ y generalizing x y
  · have h := this hy hx (le_of_not_ge hxy)
    simpa [abs_sub_comm, max_comm] using h
  have hratio : 1 - x / y ≤ Real.log y - Real.log x := by
    have hpos : 0 < y / x := div_pos hy hx
    have hlog := Real.one_sub_inv_le_log_of_pos hpos
    rw [Real.log_div hy.ne' hx.ne'] at hlog
    convert hlog using 1 <;> field_simp
  have hlogle : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hx)
      (Set.mem_Ioi.mpr hy) hxy
  rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hlogle),
    max_eq_right hxy]
  calc
    -(x - y) = y * (1 - x / y) := by field_simp; ring
    _ ≤ y * (Real.log y - Real.log x) :=
      mul_le_mul_of_nonneg_left hratio hy.le
    _ = y * -(Real.log x - Real.log y) := by ring

/-- A ceiling-valued short collar.  It is intentionally literal: no hidden
`O(1)` is absorbed in the definition. -/
def shortCollar (M : ℕ) (shortBand : ℝ) : ℕ :=
  min M ⌈(2 * M : ℝ) * shortBand⌉₊

/-- A ceiling-valued product collar for the joint Mellin frequency. -/
def productCollar (M N : ℕ) (jointBand : ℝ) : ℕ :=
  ⌈(4 * M * N : ℝ) * jointBand⌉₊

theorem natCast_dist_eq_abs (x y : ℕ) :
    (Nat.dist x y : ℝ) = |(x : ℝ) - (y : ℝ)| := by
  rcases le_total x y with h | h
  · rw [Nat.dist_eq_sub_of_le h,
      show ((y - x : ℕ) : ℝ) = (y : ℝ) - (x : ℝ) from Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    ring
  · rw [Nat.dist_eq_sub_of_le_right h,
      show ((x - y : ℕ) : ℝ) = (x : ℝ) - (y : ℝ) from Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]

theorem dyadic_dist_le_base {M m₁ m₂ : ℕ}
    (hm₁ : m₁ ∈ dyadic M) (hm₂ : m₂ ∈ dyadic M) :
    m₁.dist m₂ ≤ M := by
  simp only [dyadic, Finset.mem_Ioc] at hm₁ hm₂
  rcases le_total m₁ m₂ with h | h
  · rw [Nat.dist_eq_sub_of_le h]
    omega
  · rw [Nat.dist_eq_sub_of_le_right h]
    omega

theorem shortFrequency_to_collar
    {M m₁ m₂ : ℕ} {shortBand : ℝ}
    (hband : 0 ≤ shortBand)
    (hm₁ : m₁ ∈ dyadic M) (hm₂ : m₂ ∈ dyadic M)
    (hfreq : |Real.log m₂ - Real.log m₁| ≤ shortBand) :
    m₁.dist m₂ ≤ shortCollar M shortBand := by
  have hM : 0 < M := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hm₁nat : 0 < m₁ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁
    omega
  have hm₂nat : 0 < m₂ := by
    simp only [dyadic, Finset.mem_Ioc] at hm₂
    omega
  have hm₁pos : 0 < (m₁ : ℝ) := by exact_mod_cast hm₁nat
  have hm₂pos : 0 < (m₂ : ℝ) := by exact_mod_cast hm₂nat
  have hreal := abs_sub_le_max_mul_abs_log_sub hm₁pos hm₂pos
  have hmax : max (m₁ : ℝ) m₂ ≤ 2 * M := by
    simp only [dyadic, Finset.mem_Ioc] at hm₁ hm₂
    norm_cast
    omega
  have hdistreal : (Nat.dist m₁ m₂ : ℝ) ≤ (2 * M : ℝ) * shortBand := by
    rw [natCast_dist_eq_abs]
    calc
      |(m₁ : ℝ) - m₂| ≤
          max (m₁ : ℝ) m₂ * |Real.log m₁ - Real.log m₂| := hreal
      _ = max (m₁ : ℝ) m₂ * |Real.log m₂ - Real.log m₁| := by rw [abs_sub_comm]
      _ ≤ (2 * M : ℝ) * shortBand :=
        mul_le_mul hmax hfreq (abs_nonneg _) (by positivity)
  rw [shortCollar, le_min_iff]
  exact ⟨dyadic_dist_le_base hm₁ hm₂,
    Nat.cast_le.1 (hdistreal.trans (Nat.le_ceil _))⟩

/-- The joint logarithmic clock is the logarithmic difference of the two
products. -/
theorem jointFrequency_eq_log_products
    {q : LiteralTuple}
    (hm₁ : 0 < q.1.1) (hm₂ : 0 < q.1.2)
    (hn₁ : 0 < q.2.1) (hn₂ : 0 < q.2.2) :
    jointFrequency q =
      Real.log (q.1.2 * q.2.2) - Real.log (q.1.1 * q.2.1) := by
  simp only [jointFrequency, shortFrequency, Nat.cast_mul]
  rw [Real.log_mul (by positivity : (q.1.2 : ℝ) ≠ 0) (by positivity : (q.2.2 : ℝ) ≠ 0),
    Real.log_mul (by positivity : (q.1.1 : ℝ) ≠ 0) (by positivity : (q.2.1 : ℝ) ≠ 0)]
  ring

theorem jointFrequency_to_product_collar
    {M N : ℕ} {q : LiteralTuple} {jointBand : ℝ}
    (hband : 0 ≤ jointBand)
    (hq : q ∈ dyadicTupleBox M N)
    (hfreq : |jointFrequency q| ≤ jointBand) :
    (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) ≤
      productCollar M N jointBand := by
  rcases q with ⟨⟨m₁, m₂⟩, ⟨n₁, n₂⟩⟩
  simp [dyadicTupleBox] at hq
  rcases hq with ⟨⟨hm₁, hm₂⟩, hn₁, hn₂⟩
  have hM : 0 < M := by simp only [dyadic, Finset.mem_Ioc] at hm₁; omega
  have hN : 0 < N := by simp only [dyadic, Finset.mem_Ioc] at hn₁; omega
  have hm₁pos : 0 < m₁ := by simp only [dyadic, Finset.mem_Ioc] at hm₁; omega
  have hm₂pos : 0 < m₂ := by simp only [dyadic, Finset.mem_Ioc] at hm₂; omega
  have hn₁pos : 0 < n₁ := by simp only [dyadic, Finset.mem_Ioc] at hn₁; omega
  have hn₂pos : 0 < n₂ := by simp only [dyadic, Finset.mem_Ioc] at hn₂; omega
  have hp₁ : 0 < (m₁ * n₁ : ℝ) := by exact_mod_cast Nat.mul_pos hm₁pos hn₁pos
  have hp₂ : 0 < (m₂ * n₂ : ℝ) := by exact_mod_cast Nat.mul_pos hm₂pos hn₂pos
  have hreal := abs_sub_le_max_mul_abs_log_sub hp₁ hp₂
  have hm₁upper : m₁ ≤ 2 * M := by
    have h := hm₁
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hm₂upper : m₂ ≤ 2 * M := by
    have h := hm₂
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hn₁upper : n₁ ≤ 2 * N := by
    have h := hn₁
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hn₂upper : n₂ ≤ 2 * N := by
    have h := hn₂
    simp only [dyadic, Finset.mem_Ioc] at h
    exact h.2
  have hmax : max (m₁ * n₁ : ℕ) (m₂ * n₂) ≤ 4 * M * N := by
    rw [max_le_iff]
    constructor
    · calc
        m₁ * n₁ ≤ (2 * M) * (2 * N) :=
          Nat.mul_le_mul hm₁upper hn₁upper
        _ = 4 * M * N := by ring
    · calc
        m₂ * n₂ ≤ (2 * M) * (2 * N) :=
          Nat.mul_le_mul hm₂upper hn₂upper
        _ = 4 * M * N := by ring
  have hjoint : jointFrequency ((m₁, m₂), (n₁, n₂)) =
      Real.log (m₂ * n₂) - Real.log (m₁ * n₁) :=
    jointFrequency_eq_log_products hm₁pos hm₂pos hn₁pos hn₂pos
  have hdistreal : (Nat.dist (m₁ * n₁) (m₂ * n₂) : ℝ) ≤
      (4 * M * N : ℝ) * jointBand := by
    rw [natCast_dist_eq_abs]
    calc
      |((m₁ * n₁ : ℕ) : ℝ) - (m₂ * n₂ : ℕ)| ≤
          max ((m₁ * n₁ : ℕ) : ℝ) (m₂ * n₂ : ℕ) *
          |Real.log (m₁ * n₁) - Real.log (m₂ * n₂)| := by
            simpa only [Nat.cast_mul] using hreal
      _ = max ((m₁ * n₁ : ℕ) : ℝ) (m₂ * n₂ : ℕ) *
          |jointFrequency ((m₁, m₂), (n₁, n₂))| := by rw [hjoint, abs_sub_comm]
      _ ≤ (4 * M * N : ℝ) * jointBand := by
        apply mul_le_mul _ hfreq (abs_nonneg _) (by positivity)
        exact_mod_cast hmax
  exact Nat.cast_le.1 (hdistreal.trans (Nat.le_ceil _))

/-- The actual two-frequency survivor set maps into the checked arithmetic
collars, tuple by tuple. -/
theorem frequencyTuples_mem_collars
    {M N : ℕ} {shortBand jointBand : ℝ}
    (hs : 0 ≤ shortBand) (hj : 0 ≤ jointBand)
    {q : LiteralTuple} (hq : q ∈ frequencyTuples M N shortBand jointBand) :
    q.1.1.dist q.1.2 ≤ shortCollar M shortBand ∧
      (q.1.1 * q.2.1).dist (q.1.2 * q.2.2) ≤
        productCollar M N jointBand := by
  simp only [frequencyTuples, Finset.mem_filter] at hq
  rcases hq with ⟨hbox, hshort, hjoint⟩
  simp [dyadicTupleBox] at hbox
  exact ⟨shortFrequency_to_collar hs hbox.1.1 hbox.1.2 hshort,
    jointFrequency_to_product_collar hj
      (by simpa [dyadicTupleBox] using hbox) hjoint⟩

end MAPMixedHarmonic

