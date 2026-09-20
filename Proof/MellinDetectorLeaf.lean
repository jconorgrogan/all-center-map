import DirichletZeros
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# First analytic leaves for the MAP mollified Mellin detector

This file proves two pieces of Appendix A that are available from the pinned
Mathlib revision without assuming a zero-density theorem or a detector.

* The Gamma factor, and the Gamma--Mellin weight `Gamma z * Y ^ z`, are
  holomorphic throughout the strip `-1 < re z < 0`.  In particular this
  contains the shifted detector line `re z = 1 / 2 - beta` for
  `1 / 2 < beta <= 1` in (A.4).
* The divisor value and analytic multiplicity of a regularized Dirichlet
  L-function do not depend on which compact zero rectangle is used, once the
  point lies in both rectangles.  This gives multiplicity-aware monotonicity
  of the literal zero count under rectangle inclusion.

No decay estimate for `Gamma`, contour shift, local zero count, or density
estimate is asserted here.
-/

namespace MAPMellinDetectorLeaf

open Set
open DirichletZeros
open MeasureTheory

noncomputable section

/-! ## Holomorphy of the Gamma--Mellin weight on the detector strip -/

/-- The open strip containing every shifted line in Appendix (A.4). -/
def detectorGammaStrip : Set ℂ :=
  {z | -1 < z.re ∧ z.re < 0}

/-- The Gamma weight that occurs in Mellin inversion in (A.4). -/
def gammaMellinWeight (Y : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma z * (Y : ℂ) ^ z

/-- No pole `-m`, `m : ℕ`, meets the open detector strip. -/
theorem ne_neg_nat_of_mem_detectorGammaStrip {z : ℂ}
    (hz : z ∈ detectorGammaStrip) (m : ℕ) : z ≠ -(m : ℂ) := by
  intro hzm
  have hre : z.re = (-(m : ℂ)).re := congrArg Complex.re hzm
  rcases hz with ⟨hzlow, hzhigh⟩
  cases m with
  | zero =>
      simp only [Nat.cast_zero, neg_zero, Complex.zero_re] at hre
      linarith
  | succ m =>
      have hm : (1 : ℝ) ≤ (m.succ : ℝ) := by exact_mod_cast m.succ_pos
      simp only [Complex.neg_re, Complex.natCast_re] at hre
      linarith

/-- `Gamma` is holomorphic on the whole strip crossed by the shifted contour. -/
theorem analyticOnNhd_Gamma_detectorGammaStrip :
    AnalyticOnNhd ℂ Complex.Gamma detectorGammaStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact (Complex.differentiableAt_Gamma z
      (ne_neg_nat_of_mem_detectorGammaStrip hz)).differentiableWithinAt
  · change IsOpen (Complex.re ⁻¹' Set.Ioo (-1) 0)
    exact isOpen_Ioo.preimage Complex.continuous_re

/-- For positive `Y`, the full Gamma--Mellin weight in (A.4) is holomorphic
on the shifted strip. -/
theorem analyticOnNhd_gammaMellinWeight_detectorGammaStrip
    {Y : ℝ} (hY : 0 < Y) :
    AnalyticOnNhd ℂ (gammaMellinWeight Y) detectorGammaStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    exact ((Complex.differentiableAt_Gamma z
        (ne_neg_nat_of_mem_detectorGammaStrip hz)).mul
      (differentiableAt_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hY.ne')))).differentiableWithinAt
  · change IsOpen (Complex.re ⁻¹' Set.Ioo (-1) 0)
    exact isOpen_Ioo.preimage Complex.continuous_re

/-- The point on the shifted line `re z = 1 / 2 - beta` with ordinate `u`. -/
def shiftedDetectorPoint (beta u : ℝ) : ℂ :=
  (1 / 2 - beta : ℝ) + u * Complex.I

/-- The shifted detector line from (A.4) lies strictly between the Gamma poles
at `0` and `-1` throughout the zero-density strip. -/
theorem shiftedDetectorPoint_mem_detectorGammaStrip
    {beta u : ℝ} (hbeta_low : 1 / 2 < beta) (hbeta_high : beta ≤ 1) :
    shiftedDetectorPoint beta u ∈ detectorGammaStrip := by
  constructor <;> simp only [shiftedDetectorPoint, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero]
  · linarith
  · linarith

/-- Pointwise holomorphy of the exact Gamma--Mellin weight along (A.4). -/
theorem analyticAt_gammaMellinWeight_shiftedDetectorPoint
    {Y beta u : ℝ} (hY : 0 < Y)
    (hbeta_low : 1 / 2 < beta) (hbeta_high : beta ≤ 1) :
    AnalyticAt ℂ (gammaMellinWeight Y) (shiftedDetectorPoint beta u) :=
  analyticOnNhd_gammaMellinWeight_detectorGammaStrip hY
    _ (shiftedDetectorPoint_mem_detectorGammaStrip hbeta_low hbeta_high)

/-- Euler's integral bounds complex Gamma by real Gamma at the same real
part.  This elementary estimate is the numerator bound used after shifting
Gamma twice by its functional equation. -/
theorem norm_Gamma_le_realGamma_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Complex.GammaIntegral]
  calc
    ‖∫ x : ℝ in Set.Ioi 0, ((-x).exp : ℝ) * (x : ℂ) ^ (s - 1)‖ ≤
        ∫ x : ℝ in Set.Ioi 0,
          ‖((-x).exp : ℝ) * (x : ℂ) ^ (s - 1)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ in Set.Ioi 0,
          Real.exp (-x) * x ^ (s.re - 1) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      rw [norm_mul, Complex.norm_real,
        Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp [abs_of_pos (Real.exp_pos (-x))]
    _ = Real.Gamma s.re := (Real.Gamma_eq_integral hs).symm

/-- Two applications of `Gamma (z + 1) = z * Gamma z`, followed by Euler's
integral, give quadratic decay in the imaginary direction throughout the
detector strip.  This avoids importing Stirling's formula. -/
theorem im_sq_mul_norm_Gamma_le_realGamma_add_two
    {z : ℂ} (hzlow : -1 < z.re) (hzhigh : z.re < 0) :
    z.im ^ 2 * ‖Complex.Gamma z‖ ≤ Real.Gamma (z.re + 2) := by
  have hz : z ≠ 0 := by
    intro hz
    subst z
    simp at hzhigh
  have hzadd : z + 1 ≠ 0 := by
    intro hzadd
    have hre := congrArg Complex.re hzadd
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have hshift : 0 < (z + 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hGamma := norm_Gamma_le_realGamma_re hshift
  have hrec :
      Complex.Gamma (z + 2) = (z + 1) * z * Complex.Gamma z := by
    calc
      Complex.Gamma (z + 2) = Complex.Gamma ((z + 1) + 1) := by ring_nf
      _ = (z + 1) * Complex.Gamma (z + 1) :=
        Complex.Gamma_add_one (z + 1) hzadd
      _ = (z + 1) * z * Complex.Gamma z := by
        rw [Complex.Gamma_add_one z hz]
        simp only [mul_assoc]
  have hproduct :
      ‖z + 1‖ * ‖z‖ * ‖Complex.Gamma z‖ ≤
        Real.Gamma (z.re + 2) := by
    rw [hrec, norm_mul, norm_mul] at hGamma
    norm_num [Complex.add_re] at hGamma
    exact hGamma
  have himz : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have himzadd : |z.im| ≤ ‖z + 1‖ := by
    simpa only [Complex.add_im, Complex.one_im, add_zero] using
      Complex.abs_im_le_norm (z + 1)
  have himsq : z.im ^ 2 ≤ ‖z + 1‖ * ‖z‖ := by
    rw [← sq_abs, pow_two]
    exact mul_le_mul himzadd himz (abs_nonneg z.im) (norm_nonneg (z + 1))
  exact (mul_le_mul_of_nonneg_right himsq (norm_nonneg _)).trans hproduct

/-- Quadratic vertical decay of Gamma on the exact shifted line in (A.4). -/
theorem u_sq_mul_norm_Gamma_shiftedDetectorPoint_le
    {beta u : ℝ} (hbeta_low : 1 / 2 < beta) (hbeta_high : beta ≤ 1) :
    u ^ 2 * ‖Complex.Gamma (shiftedDetectorPoint beta u)‖ ≤
      Real.Gamma (5 / 2 - beta) := by
  have hz := shiftedDetectorPoint_mem_detectorGammaStrip
    (u := u) hbeta_low hbeta_high
  have hbound := im_sq_mul_norm_Gamma_le_realGamma_add_two hz.1 hz.2
  have him : (shiftedDetectorPoint beta u).im = u := by
    simp [shiftedDetectorPoint]
  have hre : (shiftedDetectorPoint beta u).re + 2 = 5 / 2 - beta := by
    simp [shiftedDetectorPoint]
    ring
  rw [him, hre] at hbound
  exact hbound

/-- Division form of the preceding decay estimate, useful for tail bounds. -/
theorem norm_Gamma_shiftedDetectorPoint_le_div_sq
    {beta u : ℝ} (hbeta_low : 1 / 2 < beta) (hbeta_high : beta ≤ 1)
    (hu : u ≠ 0) :
    ‖Complex.Gamma (shiftedDetectorPoint beta u)‖ ≤
      Real.Gamma (5 / 2 - beta) / u ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_ne_zero hu)).2
  simpa only [mul_comm] using
    u_sq_mul_norm_Gamma_shiftedDetectorPoint_le hbeta_low hbeta_high

/-- The factor `Y ^ z` has constant norm on a vertical line, so the exact
Gamma--Mellin weight inherits the same quadratic decay. -/
theorem u_sq_mul_norm_gammaMellinWeight_shiftedDetectorPoint_le
    {Y beta u : ℝ} (hY : 0 < Y)
    (hbeta_low : 1 / 2 < beta) (hbeta_high : beta ≤ 1) :
    u ^ 2 * ‖gammaMellinWeight Y (shiftedDetectorPoint beta u)‖ ≤
      Real.Gamma (5 / 2 - beta) * Real.rpow Y (1 / 2 - beta) := by
  rw [gammaMellinWeight, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hY]
  have hre : (shiftedDetectorPoint beta u).re = 1 / 2 - beta := by
    simp [shiftedDetectorPoint]
  rw [hre]
  calc
    u ^ 2 * (‖Complex.Gamma (shiftedDetectorPoint beta u)‖ *
        Real.rpow Y (1 / 2 - beta)) =
      (u ^ 2 * ‖Complex.Gamma (shiftedDetectorPoint beta u)‖) *
        Real.rpow Y (1 / 2 - beta) := by ring
    _ ≤ Real.Gamma (5 / 2 - beta) * Real.rpow Y (1 / 2 - beta) :=
      mul_le_mul_of_nonneg_right
        (u_sq_mul_norm_Gamma_shiftedDetectorPoint_le hbeta_low hbeta_high)
        (Real.rpow_nonneg hY.le _)

/-! ## Compact-rectangle divisor transport -/

variable {q : ℕ} [NeZero q]

/-- Rectangle containment with the directions needed by zero-count
monotonicity: increasing the left edge or decreasing the height shrinks the
closed rectangle.  No positivity assumption on either height is hidden. -/
theorem zeroRectangle_mono {sigmaOuter sigmaInner TOuter TInner : ℝ}
    (hsigma : sigmaOuter ≤ sigmaInner) (hT : TInner ≤ TOuter) :
    zeroRectangle sigmaInner TInner ⊆ zeroRectangle sigmaOuter TOuter := by
  intro z hz
  rw [zeroRectangle, Complex.mem_reProdIm] at hz ⊢
  exact ⟨⟨hsigma.trans hz.1.1, hz.1.2⟩,
    ⟨(by linarith [hz.2.1]), hz.2.2.trans hT⟩⟩

/-- A divisor value at a point is independent of the compact rectangle used
to expose it.  This is the domain-transport fact needed to preserve analytic
multiplicity when a contour rectangle changes. -/
theorem zeroDivisor_apply_eq_of_mem_rectangles
    (chi : DirichletCharacter ℂ q)
    {sigmaOne TOne sigmaTwo TTwo : ℝ} {rho : ℂ}
    (hone : rho ∈ zeroRectangle sigmaOne TOne)
    (htwo : rho ∈ zeroRectangle sigmaTwo TTwo) :
    zeroDivisor chi sigmaOne TOne rho =
      zeroDivisor chi sigmaTwo TTwo rho := by
  rw [zeroDivisor_apply_of_mem chi sigmaOne TOne hone,
    zeroDivisor_apply_of_mem chi sigmaTwo TTwo htwo]

/-- The analytic multiplicity is therefore independent of the containing
zero rectangle. -/
theorem zeroMultiplicity_eq_of_mem_rectangles
    (chi : DirichletCharacter ℂ q)
    {sigmaOne TOne sigmaTwo TTwo : ℝ} {rho : ℂ}
    (hone : rho ∈ zeroRectangle sigmaOne TOne)
    (htwo : rho ∈ zeroRectangle sigmaTwo TTwo) :
    zeroMultiplicity chi sigmaOne TOne rho =
      zeroMultiplicity chi sigmaTwo TTwo rho := by
  unfold zeroMultiplicity
  rw [zeroDivisor_apply_eq_of_mem_rectangles chi hone htwo]

/-- Divisor support transports from an inner closed rectangle to an outer
closed rectangle, including points on every boundary component. -/
theorem zeroSupport_mono
    (chi : DirichletCharacter ℂ q)
    {sigmaOuter sigmaInner TOuter TInner : ℝ}
    (hsigma : sigmaOuter ≤ sigmaInner) (hT : TInner ≤ TOuter) :
    zeroSupport chi sigmaInner TInner ⊆
      zeroSupport chi sigmaOuter TOuter := by
  intro rho hrho
  have hinner : rho ∈ zeroRectangle sigmaInner TInner :=
    (zeroDivisor chi sigmaInner TInner).supportWithinDomain
      ((zeroSupport_mem_iff chi sigmaInner TInner rho).mp hrho)
  have houter : rho ∈ zeroRectangle sigmaOuter TOuter :=
    zeroRectangle_mono hsigma hT hinner
  rw [zeroSupport_mem_iff, zeroDivisor_apply_eq_of_mem_rectangles chi houter hinner]
  exact (zeroSupport_mem_iff chi sigmaInner TInner rho).mp hrho

/-- The literal compact-rectangle zero count is monotone under rectangle
inclusion, with every zero counted using its analytic multiplicity. -/
theorem dirichletZeroCount_mono
    (chi : DirichletCharacter ℂ q)
    {sigmaOuter sigmaInner TOuter TInner : ℝ}
    (hsigma : sigmaOuter ≤ sigmaInner) (hT : TInner ≤ TOuter) :
    dirichletZeroCount chi sigmaInner TInner ≤
      dirichletZeroCount chi sigmaOuter TOuter := by
  have hsupport := zeroSupport_mono chi hsigma hT
  have hrewrite :
      dirichletZeroCount chi sigmaInner TInner =
        ∑ rho ∈ zeroSupport chi sigmaInner TInner,
          zeroMultiplicity chi sigmaOuter TOuter rho := by
    unfold dirichletZeroCount
    apply Finset.sum_congr rfl
    intro rho hrho
    have hinner : rho ∈ zeroRectangle sigmaInner TInner :=
      (zeroDivisor chi sigmaInner TInner).supportWithinDomain
        ((zeroSupport_mem_iff chi sigmaInner TInner rho).mp hrho)
    have houter : rho ∈ zeroRectangle sigmaOuter TOuter :=
      zeroRectangle_mono hsigma hT hinner
    exact zeroMultiplicity_eq_of_mem_rectangles chi hinner houter
  rw [hrewrite]
  unfold dirichletZeroCount
  exact Finset.sum_le_sum_of_subset_of_nonneg hsupport
    (fun _ _ _ => Nat.zero_le _)

/-! ## Excluding the artificial right edge -/

/-- The regularization used by the divisor has no zero in `re s >= 1`.
For a principal character, the proof treats the updated value at `s = 1`
separately and multiplies away the pole elsewhere. -/
theorem regularizedLFunction_ne_zero_of_one_le_re
    (chi : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re) :
    regularizedLFunction chi s ≠ 0 := by
  classical
  by_cases hchi : chi = 1
  · subst chi
    simp only [regularizedLFunction, eq_self, if_true]
    by_cases hsone : s = 1
    · subst s
      exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero q
    · rw [DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne hsone]
      exact mul_ne_zero (sub_ne_zero.mpr hsone)
        (DirichletCharacter.LFunction_ne_zero_of_one_le_re 1
          (.inr hsone) hs)
  · simp only [regularizedLFunction, if_neg hchi]
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re chi
      (.inl hchi) hs

/-- Every supported zero lies strictly to the left of the closed rectangle's
right edge.  Thus the artificial endpoint `re rho = 1` contributes nothing. -/
theorem re_lt_one_of_mem_zeroSupport
    (chi : DirichletCharacter ℂ q) {sigma T : ℝ} {rho : ℂ}
    (hrho : rho ∈ zeroSupport chi sigma T) : rho.re < 1 := by
  have hdiv : zeroDivisor chi sigma T rho ≠ 0 :=
    (zeroSupport_mem_iff chi sigma T rho).mp hrho
  have hrect : rho ∈ zeroRectangle sigma T :=
    (zeroDivisor chi sigma T).supportWithinDomain hdiv
  have hre : rho.re ≤ 1 := by
    exact (Complex.mem_reProdIm.mp hrect).1.2
  exact lt_of_le_of_ne hre fun heq =>
    (regularizedLFunction_ne_zero_of_one_le_re chi (by linarith))
      (regularizedLFunction_eq_zero_of_mem_zeroSupport chi sigma T hrho)

end

end MAPMellinDetectorLeaf
