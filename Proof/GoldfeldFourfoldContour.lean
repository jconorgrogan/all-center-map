import GoldfeldRieszMellin
import RieszA4Detector
import FinitePoleRectangle

/-!
# The removable zero and the zeta pole in Goldfeld's four-L contour

The translated zero of `L(s,χ)` cancels the Riesz pole at the origin.  The only
remaining pole in `-1 < Re z` is the translated zeta pole `z = 1-β`; this file
constructs its holomorphic remainder and proves the exact finite-rectangle
residue identity.
-/

namespace MAPGoldfeldSiegel

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators Interval
open MAPAppendixA4RieszKernel MAPAppendixA4RieszDetector MAPAppendixA4Detector
open FinitePoleRectangle

noncomputable section

set_option maxHeartbeats 800000

/-- The Riemann zeta function with its pole multiplied away and filled by its
residue. -/
def regularizedRiemannZeta (s : ℂ) : ℂ :=
  Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1 s

@[simp] theorem regularizedRiemannZeta_one : regularizedRiemannZeta 1 = 1 := by
  simp [regularizedRiemannZeta]

/-- Away from the pole the regularization is the literal product. -/
theorem regularizedRiemannZeta_eq_mul {s : ℂ} (hs : s ≠ 1) :
    regularizedRiemannZeta s = (s - 1) * riemannZeta s := by
  simp [regularizedRiemannZeta, Function.update_of_ne hs]

/-- The residue theorem for zeta supplies the removable analytic extension at
one; no source proposition is used. -/
theorem analyticAt_regularizedRiemannZeta (s : ℂ) :
    AnalyticAt ℂ regularizedRiemannZeta s := by
  by_cases hs : s = 1
  · subst s
    apply analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with z hz
      apply DifferentiableAt.congr_of_eventuallyEq
      · exact (differentiableAt_id.sub_const 1).mul
          (differentiableAt_riemannZeta hz)
      · filter_upwards [eventually_ne_nhds hz] with w hw
        exact Function.update_of_ne hw ..
    · change ContinuousAt
        (Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1) 1
      simpa only [continuousAt_update_same] using riemannZeta_residue_one
  · have ha : AnalyticAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) s :=
      (analyticAt_id.sub analyticAt_const).mul
        (analyticOn_riemannZeta s hs)
    apply ha.congr
    filter_upwards [eventually_ne_nhds hs] with w hw
    simpa only [regularizedRiemannZeta] using
      (Function.update_of_ne hw (1 : ℂ)
        (fun u : ℂ => (u - 1) * riemannZeta u)).symm

/-- Local analytic divided differences, with no global-entire assumption. -/
theorem analyticAt_dslope_of_analyticAt
    {f : ℂ → ℂ} {p z : ℂ} (hp : AnalyticAt ℂ f p)
    (hz : AnalyticAt ℂ f z) : AnalyticAt ℂ (dslope f p) z := by
  by_cases hzp : z = p
  · subst z
    rcases hp with ⟨P, hP⟩
    exact ⟨P.fslope, hP.has_fpower_series_dslope_fslope⟩
  · have hdiv : AnalyticAt ℂ (fun w : ℂ => (f w - f p) / (w - p)) z :=
      hz.sub analyticAt_const |>.div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr hzp)
    apply hdiv.congr
    filter_upwards [dslope_eventuallyEq_slope_of_ne f hzp] with w hw
    rw [hw]
    simp only [slope, vsub_eq_sub, div_eq_inv_mul]
    ring

/-- The analytic factor left after canceling the Riesz pole with the
translated zero of `L(s,χ)`. -/
def goldfeldZeroCanceledFactor
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  regularizedRieszKernel k z * shiftedZeroQuotient chi beta z *
    (X : ℂ) ^ z * DirichletCharacter.LFunction psi (beta + z) *
      DirichletCharacter.LFunction (chi * psi) (beta + z)

/-- Analyticity of the zero-canceled factor throughout the pole-free Riesz
strip. -/
theorem analyticAt_goldfeldZeroCanceledFactor
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} {k : ℕ} {X : ℝ} (hX : 0 < X)
    {z : ℂ} (hz : -1 < z.re) :
    AnalyticAt ℂ (goldfeldZeroCanceledFactor chi psi beta k X) z := by
  unfold goldfeldZeroCanceledFactor
  have hpow : Differentiable ℂ (fun w : ℂ => (X : ℂ) ^ w) :=
    differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (((((analyticAt_regularizedRieszKernel k hz).mul
    (analyticAt_shiftedZeroQuotient chi hchi beta z)).mul
      (hpow.analyticAt z)).mul
      (((DirichletCharacter.differentiable_LFunction hpsi).analyticAt
        (beta + z)).comp (by fun_prop))).mul
      (((DirichletCharacter.differentiable_LFunction hmul).analyticAt
        (beta + z)).comp (by fun_prop)))

/-- The numerator after also multiplying away the translated zeta pole. -/
def goldfeldPoleNumerator
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  regularizedRiemannZeta (beta + z) *
    goldfeldZeroCanceledFactor chi psi beta k X z

/-- The numerator is analytic on `Re z > -1`. -/
theorem analyticAt_goldfeldPoleNumerator
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} {k : ℕ} {X : ℝ} (hX : 0 < X)
    {z : ℂ} (hz : -1 < z.re) :
    AnalyticAt ℂ (goldfeldPoleNumerator chi psi beta k X) z := by
  unfold goldfeldPoleNumerator
  exact ((analyticAt_regularizedRiemannZeta (beta + z)).comp (by fun_prop)).mul
    (analyticAt_goldfeldZeroCanceledFactor chi psi hchi hpsi hmul hX hz)

/-- The analytic remainder after subtracting the translated zeta principal
part. -/
def goldfeldPoleRemainder
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) : ℂ → ℂ :=
  dslope (goldfeldPoleNumerator chi psi beta k X) (1 - beta)

/-- The subtracted remainder is analytic throughout `Re z > -1`, provided the
translated pole itself lies there. -/
theorem analyticAt_goldfeldPoleRemainder
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hbeta : beta < 2) {k : ℕ} {X : ℝ} (hX : 0 < X)
    {z : ℂ} (hz : -1 < z.re) :
    AnalyticAt ℂ (goldfeldPoleRemainder chi psi beta k X) z := by
  unfold goldfeldPoleRemainder
  apply analyticAt_dslope_of_analyticAt
  · apply analyticAt_goldfeldPoleNumerator chi psi hchi hpsi hmul hX
    simp
    linarith
  · exact analyticAt_goldfeldPoleNumerator chi psi hchi hpsi hmul hX hz

/-- The literal four-L integrand whose initial line was evaluated in
`GoldfeldRieszMellin`. -/
def goldfeldRawIntegrand
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) (z : ℂ) : ℂ :=
  rieszMellinKernel k z * (X : ℂ) ^ z *
    (riemannZeta (beta + z) * DirichletCharacter.LFunction chi (beta + z) *
      DirichletCharacter.LFunction psi (beta + z) *
        DirichletCharacter.LFunction (chi * psi) (beta + z))

/-- The residue of the translated zeta pole. -/
def goldfeldPoleResidue
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) : ℂ :=
  goldfeldZeroCanceledFactor chi psi beta k X (1 - beta)

/-- At the translated zeta pole the regularized numerator is exactly its
residue. -/
theorem goldfeldPoleNumerator_at_pole
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) :
    goldfeldPoleNumerator chi psi beta k X (1 - beta) =
      goldfeldPoleResidue chi psi beta k X := by
  simp [goldfeldPoleNumerator, goldfeldPoleResidue]

/-- Away from the canceled origin and the zeta pole, the literal integrand is
its analytic remainder plus the displayed principal part. -/
theorem goldfeldRawIntegrand_eq_remainder_add_principal
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (k : ℕ) (X : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hzp : z ≠ (1 - beta : ℝ)) :
    goldfeldRawIntegrand chi psi beta k X z =
      goldfeldPoleRemainder chi psi beta k X z +
        goldfeldPoleResidue chi psi beta k X *
          (z - (1 - beta : ℝ))⁻¹ := by
  have hshift : (beta : ℂ) + z ≠ 1 := by
    intro h
    apply hzp
    apply Complex.ext
    · have hre := congrArg Complex.re h
      simp at hre ⊢
      linarith
    · have him := congrArg Complex.im h
      simp at him ⊢
      exact him
  have hzeta := regularizedRiemannZeta_eq_mul hshift
  have hchiq := shiftedZeroQuotient_eq_div chi hzero hz0
  have hkern := rieszMellinKernel_eq_div_regularized k z
  have hds : goldfeldPoleRemainder chi psi beta k X z =
      (goldfeldPoleNumerator chi psi beta k X z -
        goldfeldPoleNumerator chi psi beta k X (1 - beta)) /
          (z - (1 - beta : ℝ)) := by
    rw [goldfeldPoleRemainder, dslope_of_ne]
    · simp [slope, vsub_eq_sub, div_eq_inv_mul]
    · simpa using hzp
  rw [hds, goldfeldPoleNumerator_at_pole]
  unfold goldfeldRawIntegrand goldfeldPoleNumerator goldfeldZeroCanceledFactor
  rw [hzeta, hchiq, hkern]
  have hpform : (beta : ℂ) + z - 1 = z - (1 - beta : ℝ) := by
    push_cast
    ring
  rw [hpform]
  have hden : z - (1 - beta : ℝ) ≠ 0 := sub_ne_zero.mpr hzp
  field_simp [hden, hz0]
  <;> ring

/-- **Exact finite contour shift with the one surviving zeta residue.** -/
theorem finiteRectangle_goldfeld_shift
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {k : ℕ} {X : ℝ} (hX : 0 < X)
    {B r : ℝ} (hB : 0 < B) (hr : 0 < r)
    (hrleft : -(1 : ℝ) / 2 < (1 - beta) - r)
    (hrright : (1 - beta) + r < 1 / 2)
    (hrbottom : -B < -r) (hrtop : r < B) :
    rectangleBoundaryIntegral
        (goldfeldRawIntegrand chi psi beta k X)
        (-1 / 2) (1 / 2) (-B) B =
      (2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X := by
  let p : Unit → ℂ := fun _ => (1 - beta : ℝ)
  let R : Unit → ℂ := fun _ => goldfeldPoleResidue chi psi beta k X
  let rad : Unit → ℝ := fun _ => r
  let g := goldfeldPoleRemainder chi psi beta k X
  have hsum : (∑ i ∈ ({()} : Finset Unit), R i) =
      goldfeldPoleResidue chi psi beta k X := by simp [R]
  rw [← hsum]
  apply rectangleBoundaryIntegral_eq_two_pi_I_mul_sum_residue
    ({()} : Finset Unit) p R rad
    (goldfeldRawIntegrand chi psi beta k X) g
    (-1 / 2) (1 / 2) (-B) B
  · intro i hi
    simpa [rad] using hr
  · intro i hi
    simpa [p, rad] using hrleft
  · intro i hi
    simpa [p, rad] using hrright
  · intro i hi
    simpa [p, rad] using hrbottom
  · intro i hi
    simpa [p, rad] using hrtop
  · apply boundaryIntervalIntegrable_of_differentiableOn
    intro z hz
    exact (analyticAt_goldfeldPoleRemainder chi psi hchi hpsi hmul
      (by linarith : beta < 2) hX (by
        have hzleft := hz.1.1
        norm_num at hzleft ⊢
        linarith)).differentiableWithinAt
  · intro z hz
    exact (analyticAt_goldfeldPoleRemainder chi psi hchi hpsi hmul
      (by linarith : beta < 2) hX (by
        have hzleft := hz.1.1
        norm_num at hzleft ⊢
        linarith)).differentiableWithinAt
  · intro x
    have hz0 : (x : ℂ) + (-B : ℂ) * I ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    have hzp : (x : ℂ) + (-B : ℂ) * I ≠ (1 - beta : ℝ) := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    simpa [g, p, R] using
      (goldfeldRawIntegrand_eq_remainder_add_principal chi psi hzero k X hz0 hzp)
  · intro x
    have hz0 : (x : ℂ) + (B : ℂ) * I ≠ 0 := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    have hzp : (x : ℂ) + (B : ℂ) * I ≠ (1 - beta : ℝ) := by
      intro hz
      have him := congrArg Complex.im hz
      simp at him
      linarith
    simpa [g, p, R] using
      (goldfeldRawIntegrand_eq_remainder_add_principal chi psi hzero k X hz0 hzp)
  · intro y
    have hz0 : ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
    have hzp : ((1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ (1 - beta : ℝ) := by
      intro hz
      have hre := congrArg Complex.re hz
      simp at hre
      linarith
    simpa [g, p, R] using
      (goldfeldRawIntegrand_eq_remainder_add_principal chi psi hzero k X hz0 hzp)
  · intro y
    have hz0 : ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro hz
      have hre := congrArg Complex.re hz
      norm_num at hre
    have hzp : ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I ≠ (1 - beta : ℝ) := by
      intro hz
      have hre := congrArg Complex.re hz
      simp at hre
      linarith
    simpa [g, p, R] using
      (goldfeldRawIntegrand_eq_remainder_add_principal chi psi hzero k X hz0 hzp)


/-- The initial vertical slice is integrable, derived from absolute convergence
and the Riesz-kernel majorant. -/
theorem integrable_goldfeldRaw_right
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    {beta : ℝ} (hbeta : 1 / 2 < beta) (k : ℕ) (hk : 1 ≤ k)
    {X : ℝ} (hX : 0 < X) :
    Integrable (fun t : ℝ => goldfeldRawIntegrand chi psi beta k X
      ((1 / 2 : ℝ) + t * I)) := by
  let f : ℕ → ℂ := fun n => goldfeldFourfoldCoeff chi psi n
  have hs : 1 < beta + 1 / 2 := by linarith
  have hsLS : LSeriesSummable f (((beta + 1 / 2 : ℝ) : ℂ)) := by
    let z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
    let a : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
    let b : ArithmeticFunction ℂ := toArithmeticFunction (psi ·)
    let d : ArithmeticFunction ℂ := toArithmeticFunction ((chi * psi) ·)
    have hz : LSeriesSummable (fun n => z n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
      simpa [z] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr
        (show 1 < ((((beta + 1 / 2 : ℝ) : ℂ))).re by simpa using hs)
    have ha : LSeriesSummable (fun n => a n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        chi.apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
    have hb : LSeriesSummable (fun n => b n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        psi.apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re psi hs)
    have hd : LSeriesSummable (fun n => d n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
      exact (LSeriesSummable_congr _ fun hn =>
        (chi * psi).apply_eq_toArithmeticFunction_apply hn).mp
          (DirichletCharacter.LSeriesSummable_of_one_lt_re (chi * psi) hs)
    exact ArithmeticFunction.LSeriesSummable_mul
      (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul hz ha) hb) hd
  have hint := integrable_rieszRightIntegrand f beta k hk hX
    (by norm_num : (0 : ℝ) < 1 / 2) hsLS
  apply hint.congr
  exact Filter.Eventually.of_forall fun t => by
    unfold rieszRightIntegrand goldfeldRawIntegrand
    rw [LSeries_goldfeldFourfoldCoeff_eq chi psi]
    · simpa using hs

/-- **Full normalized Goldfeld contour identity.**  Once literal decay of the
two horizontal sides and integrability of the shifted line are supplied, the
finite residue identity passes to the full vertical lines. -/
theorem normalized_full_goldfeld_contour_of_left_integrable_horizontal_decay
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {k : ℕ} (hk : 1 ≤ k) {X : ℝ} (hX : 0 < X)
    {r : ℝ} (hr : 0 < r)
    (hrleft : -(1 : ℝ) / 2 < (1 - beta) - r)
    (hrright : (1 - beta) + r < 1 / 2)
    (hleft : Integrable (fun t : ℝ =>
      goldfeldRawIntegrand chi psi beta k X ((-1 / 2 : ℝ) + t * I)))
    (hminus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (-1 / 2)..(1 / 2),
        goldfeldRawIntegrand chi psi beta k X (x - B * I))
      atTop (𝓝 0))
    (hplus : Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (-1 / 2)..(1 / 2),
        goldfeldRawIntegrand chi psi beta k X (x + B * I))
      atTop (𝓝 0)) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
        ((1 / 2 : ℝ) + t * I)) =
      goldfeldPoleResidue chi psi beta k X +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
            ((-1 / 2 : ℝ) + t * I)) := by
  let R : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    goldfeldRawIntegrand chi psi beta k X ((1 / 2 : ℝ) + t * I)
  let LeftTrunc : ℝ → ℂ := fun B => ∫ t : ℝ in -B..B,
    goldfeldRawIntegrand chi psi beta k X ((-1 / 2 : ℝ) + t * I)
  let Hminus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 / 2)..(1 / 2),
    goldfeldRawIntegrand chi psi beta k X (x - B * I)
  let Hplus : ℝ → ℂ := fun B => ∫ x : ℝ in (-1 / 2)..(1 / 2),
    goldfeldRawIntegrand chi psi beta k X (x + B * I)
  have hright := integrable_goldfeldRaw_right chi psi hbetaLow k hk hX
  have hR : Tendsto R atTop
      (𝓝 (∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
        ((1 / 2 : ℝ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hright
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hL : Tendsto LeftTrunc atTop
      (𝓝 (∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
        ((-1 / 2 : ℝ) + t * I))) := by
    exact MeasureTheory.intervalIntegral_tendsto_integral hleft
      Filter.tendsto_neg_atTop_atBot tendsto_id
  have hbalance : ∀ᶠ B : ℝ in atTop,
      I * (R B - LeftTrunc B) =
        (2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X +
          (Hplus B - Hminus B) := by
    filter_upwards [eventually_gt_atTop r] with B hBr
    have hrect := finiteRectangle_goldfeld_shift chi psi hchi hpsi hmul
      (k := k) (X := X) (B := B) (r := r)
      hzero hbetaLow hbetaHigh hX (show 0 < B by linarith) hr
      hrleft hrright (by linarith) hBr
    unfold rectangleBoundaryIntegral at hrect
    have hminusInt :
        (∫ x : ℝ in (-1 / 2)..(1 / 2),
          goldfeldRawIntegrand chi psi beta k X
            ((x : ℂ) + ((-B : ℝ) : ℂ) * I)) =
        ∫ x : ℝ in (-1 / 2)..(1 / 2),
          goldfeldRawIntegrand chi psi beta k X
            ((x : ℂ) - (B : ℂ) * I) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply congrArg (goldfeldRawIntegrand chi psi beta k X)
      push_cast
      ring
    rw [hminusInt] at hrect
    change Hminus B - Hplus B + I * R B - I * LeftTrunc B =
      (2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X at hrect
    linear_combination hrect
  have hlhs : Tendsto (fun B => I * (R B - LeftTrunc B)) atTop
      (𝓝 (I * ((∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
          ((1 / 2 : ℝ) + t * I)) -
        ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
          ((-1 / 2 : ℝ) + t * I)))) :=
    tendsto_const_nhds.mul (hR.sub hL)
  have hrhs : Tendsto (fun B =>
      (2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X +
        (Hplus B - Hminus B)) atTop
      (𝓝 ((2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X)) := by
    simpa [Hplus, Hminus] using
      tendsto_const_nhds.add (hplus.sub hminus)
  have hlhs' : Tendsto (fun B => I * (R B - LeftTrunc B)) atTop
      (𝓝 ((2 * Real.pi * I) * goldfeldPoleResidue chi psi beta k X)) :=
    hrhs.congr' (hbalance.mono fun B hB => hB.symm)
  have heq := tendsto_nhds_unique hlhs hlhs'
  have hshift :
      (∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
          ((1 / 2 : ℝ) + t * I)) -
        ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
          ((-1 / 2 : ℝ) + t * I) =
        (2 : ℂ) * (Real.pi : ℂ) * goldfeldPoleResidue chi psi beta k X := by
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    apply (mul_left_cancel₀ hI)
    linear_combination heq
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) Real.pi_ne_zero)
  rw [show (∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
      ((1 / 2 : ℝ) + t * I)) =
      (2 : ℂ) * (Real.pi : ℂ) * goldfeldPoleResidue chi psi beta k X +
        ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
          ((-1 / 2 : ℝ) + t * I) by linear_combination hshift]
  have hnorm : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ((2 : ℂ) * (Real.pi : ℂ))) = 1 := by
    norm_cast
    field_simp [Real.pi_ne_zero]
  calc
    _ = ((((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((2 : ℂ) * (Real.pi : ℂ))) *
            goldfeldPoleResidue chi psi beta k X) +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, goldfeldRawIntegrand chi psi beta k X
            ((-1 / 2 : ℝ) + t * I)) := by ring
    _ = _ := by rw [hnorm, one_mul]

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.analyticAt_regularizedRiemannZeta
#print axioms MAPGoldfeldSiegel.finiteRectangle_goldfeld_shift
