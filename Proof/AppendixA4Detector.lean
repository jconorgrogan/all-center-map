import MollifierCoefficientIdentity
import GammaMellinInversion
import MellinDetectorLeaf
import DirichletZeros
import PrimitiveEulerZeroTransport
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exact analytic spine of Appendix (A.4)

This module starts the detector at the literal coefficient identity already
proved in `MollifierCoefficientIdentity`.  It imports the exact inverse Mellin
formula from `GammaMellinInversion` and proves the removable-zero extension,
finite contour shift, and explicit boundary-error inequalities without
assuming a density estimate.
-/

namespace MAPAppendixA4Detector

open Set MeasureTheory Complex Filter
open scoped Topology
open MAPMollifierCoefficientIdentity MAPMellinDetectorLeaf

noncomputable section

/-! `GammaMellinInversion` supplies the exact full right-line identity
`exp_neg_nat_div_eq_detector_right_line`; it is imported rather than duplicated here. -/

/-! ## Entire finite mollifier and the removable zero at `z = 0` -/

/-- The L-series definition of the mollifier is a literal finite sum. -/
theorem mollifier_eq_sum_range {q U : ℕ}
    (chi : DirichletCharacter ℂ q) (s : ℂ) :
    mollifier chi U s =
      ∑ n ∈ Finset.range (U + 1),
        LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U) s n := by
  unfold mollifier LSeries
  rw [tsum_eq_sum]
  intro n hn
  have hnU : U < n := by
    simpa only [Finset.mem_range, not_lt] using hn
  rw [LSeries.term_def]
  split_ifs with hn0
  · rfl
  · simp [truncatedMoebius, not_le.mpr hnU]

/-- The finite mollifier is entire. -/
theorem analyticAt_mollifier {q U : ℕ}
    (chi : DirichletCharacter ℂ q) (s : ℂ) :
    AnalyticAt ℂ (mollifier chi U) s := by
  have heq : mollifier chi U = fun z =>
      ∑ n ∈ Finset.range (U + 1),
        LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U) z n := by
    funext z
    exact mollifier_eq_sum_range chi z
  rw [heq]
  apply Finset.analyticAt_fun_sum
  intro n hn
  have hdiff : Differentiable ℂ (fun z =>
      LSeries.term (((chi ·) : ℕ → ℂ) * truncatedMoebius U) z n) :=
    fun z => (LSeries.hasDerivAt_term
      (((chi ·) : ℕ → ℂ) * truncatedMoebius U) n z).differentiableAt
  exact hdiff.analyticAt s

variable {q : ℕ} [NeZero q]

/-! ## Reusable quantitative foundation interfaces

These propositions name missing analytic theorems; they are deliberately not
inhabited here.  The first is shared by the A.4 contour tails and the A.5
unit-interval zero count. -/

/-- Conductor/height-uniform polynomial growth for primitive nonprincipal
Dirichlet L-functions on the fixed strip needed by A.4 and A.5. -/
def PrimitiveLPolynomialStripGrowth : Prop :=
  ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q),
      chi.IsPrimitive → chi ≠ 1 →
      ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 3 / 2 →
        ‖DirichletCharacter.LFunction chi s‖ ≤
          C * ((q : ℝ) * (|s.im| + 2)) ^ D

/-- Compact-strip Stirling decay needed to convert height
`V = (log R)^2` into arbitrary powers of `R^{-1}`. -/
def GammaCompactStripExponentialDecay : Prop :=
  ∃ C E : ℝ, 0 < C ∧ 0 ≤ E ∧
    ∀ a t : ℝ, -1 / 2 ≤ a → a ≤ 1 / 2 → 1 ≤ |t| →
      ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
        C * (1 + |t|) ^ E * Real.exp (-(Real.pi / 4) * |t|)

/-! ## Canonical removable-singularity integrand -/

/-- The divided difference provides the canonical analytic quotient of the
translated L-function at the crossed zero. -/
def shiftedZeroQuotient
    (chi : DirichletCharacter ℂ q) (rho z : ℂ) : ℂ :=
  dslope (DirichletCharacter.LFunction chi) rho (rho + z)

theorem shiftedZeroQuotient_eq_div
    (chi : DirichletCharacter ℂ q) {rho z : ℂ}
    (hrho : DirichletCharacter.LFunction chi rho = 0) (hz : z ≠ 0) :
    shiftedZeroQuotient chi rho z =
      DirichletCharacter.LFunction chi (rho + z) / z := by
  rw [shiftedZeroQuotient, dslope_of_ne]
  · simp [slope, hrho, div_eq_inv_mul]
  · intro h
    apply hz
    have : rho + z = rho + 0 := by simpa using h
    exact add_left_cancel this

theorem analyticAt_shiftedZeroQuotient
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (rho z : ℂ) : AnalyticAt ℂ (shiftedZeroQuotient chi rho) z := by
  by_cases hz : z = 0
  · subst z
    have hL : AnalyticAt ℂ (DirichletCharacter.LFunction chi) rho :=
      (DirichletCharacter.differentiable_LFunction hchi).analyticAt rho
    rcases hL with ⟨p, hp⟩
    have hds : AnalyticAt ℂ
        (dslope (DirichletCharacter.LFunction chi) rho) rho :=
      ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
    have hds' : AnalyticAt ℂ
        (dslope (DirichletCharacter.LFunction chi) rho) (rho + 0) := by
      simpa using hds
    have hadd : AnalyticAt ℂ (fun w : ℂ => rho + w) 0 := by fun_prop
    simpa [shiftedZeroQuotient, Function.comp_def] using hds'.comp hadd
  · have hdiv : AnalyticAt ℂ
        (fun w : ℂ => (DirichletCharacter.LFunction chi (rho + w) -
          DirichletCharacter.LFunction chi rho) / w) z := by
      apply AnalyticAt.div
      · exact ((DirichletCharacter.differentiable_LFunction hchi).analyticAt
          (rho + z)).comp (by fun_prop) |>.sub analyticAt_const
      · exact analyticAt_id
      · exact hz
    apply hdiv.congr
    have hne : rho + z ≠ rho := by
      intro h
      apply hz
      have : rho + z = rho + 0 := by simpa using h
      exact add_left_cancel this
    have hev := dslope_eventuallyEq_slope_of_ne
      (DirichletCharacter.LFunction chi) hne
    have hmap : Tendsto (fun w : ℂ => rho + w) (nhds z) (nhds (rho + z)) :=
      tendsto_const_nhds.add tendsto_id
    filter_upwards [hev.comp_tendsto hmap, isOpen_ne.mem_nhds hz] with w hw hw0
    simp only [Function.comp_apply] at hw
    rw [shiftedZeroQuotient, hw]
    simp [slope, div_eq_inv_mul]

/-- The explicit analytic replacement for the raw A.4 integrand. -/
def regularizedDetectorIntegrand
    (chi : DirichletCharacter ℂ q) (rho : ℂ)
    (U : ℕ) (Y : ℝ) (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) * shiftedZeroQuotient chi rho z *
    (Y : ℂ) ^ z * mollifier chi U (rho + z)

/-- An analytic function vanishing at zero admits a globally defined analytic
factor by `z`.  No simplicity assumption is used. -/
theorem exists_analytic_factor_zero
    {f : ℂ → ℂ} (hf : ∀ z, AnalyticAt ℂ f z) (hzero : f 0 = 0) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧ ∀ z, f z = z * g z := by
  obtain ⟨g, hg0, hfg⟩ := (hf 0).exists_eq_sum_add_pow_mul 1
  have hfactor (z : ℂ) : f z = z * g z := by
    simpa [hzero, smul_eq_mul] using hfg z
  refine ⟨g, ?_, hfactor⟩
  intro z
  by_cases hz : z = 0
  · simpa [hz] using hg0
  · have hquot : AnalyticAt ℂ (fun w => f w / w) z :=
      (hf z).div analyticAt_id hz
    have heq : (fun w => f w / w) =ᶠ[𝓝 z] g := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      apply (div_eq_iff hw).2
      simpa [mul_comm] using hfactor w
    exact hquot.congr heq

/-- A primitive nonprincipal Dirichlet L-function translated by one of its
zeros has an analytic factor by the translation variable.  This statement is
multiplicity safe: a zero of any positive analytic order supplies at least
one factor. -/
theorem exists_translatedL_zero_factor
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0) :
    ∃ g : ℂ → ℂ, (∀ z, AnalyticAt ℂ g z) ∧
      ∀ z, DirichletCharacter.LFunction chi (rho + z) = z * g z := by
  apply exists_analytic_factor_zero
  · intro z
    have hdiff : Differentiable ℂ (fun w =>
        DirichletCharacter.LFunction chi (rho + w)) := by
      intro w
      exact (DirichletCharacter.differentiableAt_LFunction chi (rho + w)
        (Or.inr hchi)).comp w (by fun_prop)
    exact hdiff.analyticAt z
  · simpa using hrho

/-- For a nonprincipal character the translated L-function is analytic at
`z = 1-rho`; hence the contour crosses no pole there.  Primitivity is not
needed for this local fact. -/
theorem analyticAt_translatedL_one_sub
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (rho : ℂ) :
    AnalyticAt ℂ (fun z =>
      DirichletCharacter.LFunction chi (rho + z)) (1 - rho) := by
  have hdiff : Differentiable ℂ (fun z =>
      DirichletCharacter.LFunction chi (rho + z)) := by
    intro z
    exact (DirichletCharacter.differentiableAt_LFunction chi (rho + z)
      (Or.inr hchi)).comp z (by fun_prop)
  exact hdiff.analyticAt (1 - rho)

/-- The strip on which `Gamma (z + 1)` has no pole and the detector extension
is holomorphic. -/
def contourStrip : Set ℂ := {z | -1 < z.re}

/-- `Gamma (z + 1)` is analytic throughout the contour strip. -/
theorem analyticOnNhd_Gamma_add_one_contourStrip :
    AnalyticOnNhd ℂ (fun w => Complex.Gamma (w + 1)) contourStrip := by
  apply DifferentiableOn.analyticOnNhd
  · intro z hz
    have hne (m : ℕ) : z + 1 ≠ -(m : ℂ) := by
      intro h
      have hre := congrArg Complex.re h
      change -1 < z.re at hz
      simp only [Complex.add_re, Complex.one_re, Complex.neg_re,
        Complex.natCast_re] at hre
      have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact ((Complex.differentiableAt_Gamma (z + 1) hne).comp z
      (by fun_prop)).differentiableWithinAt
  · change IsOpen (Complex.re ⁻¹' Set.Ioi (-1))
    exact isOpen_Ioi.preimage Complex.continuous_re

theorem analyticAt_Gamma_add_one_of_mem_contourStrip
    {z : ℂ} (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (fun w => Complex.Gamma (w + 1)) z :=
  analyticOnNhd_Gamma_add_one_contourStrip z hz

/-- The canonical detector integrand is analytic on the whole shifted
rectangle, including `z = 0`. -/
theorem analyticAt_regularizedDetectorIntegrand
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho z : ℂ} {U : ℕ} {Y : ℝ} (hY : 0 < Y)
    (hz : z ∈ contourStrip) :
    AnalyticAt ℂ (regularizedDetectorIntegrand chi rho U Y) z := by
  unfold regularizedDetectorIntegrand
  have hpowDiff : Differentiable ℂ (fun w : ℂ => (Y : ℂ) ^ w) :=
    differentiable_id.const_cpow
      (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
  exact ((((analyticAt_Gamma_add_one_of_mem_contourStrip hz).mul
    (analyticAt_shiftedZeroQuotient chi hchi rho z)).mul
    (hpowDiff.analyticAt z)).mul
    ((analyticAt_mollifier chi (rho + z)).comp (by fun_prop)))

/-- Away from zero, the canonical extension is the literal raw A.4
Gamma--L--mollifier integrand. -/
theorem regularizedDetectorIntegrand_eq_raw
    (chi : DirichletCharacter ℂ q) {rho z : ℂ} {U : ℕ} {Y : ℝ}
    (hrho : DirichletCharacter.LFunction chi rho = 0) (hz : z ≠ 0) :
    regularizedDetectorIntegrand chi rho U Y z =
      gammaMellinWeight Y z *
        DirichletCharacter.LFunction chi (rho + z) *
        mollifier chi U (rho + z) := by
  rw [regularizedDetectorIntegrand, shiftedZeroQuotient_eq_div chi hrho hz,
    gammaMellinWeight, Complex.Gamma_add_one z hz]
  field_simp

/-- A holomorphic extension of the raw Appendix (A.4) integrand across
`z = 0`.  Away from zero it equals the literal Gamma--L--mollifier product.
The absence of a pole at `1-rho` is encoded by the nonprincipal hypothesis,
which makes the translated L-function entire. -/
theorem exists_detectorExtension
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (U : ℕ)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    {Y : ℝ} (hY : 0 < Y) :
    ∃ F : ℂ → ℂ,
      (∀ z ∈ contourStrip, AnalyticAt ℂ F z) ∧
      (∀ z, z ≠ 0 →
        F z = gammaMellinWeight Y z *
          DirichletCharacter.LFunction chi (rho + z) *
          mollifier chi U (rho + z)) := by
  obtain ⟨g, hg, hLg⟩ := exists_translatedL_zero_factor chi hchi hrho
  let F : ℂ → ℂ := fun z =>
    Complex.Gamma (z + 1) * (Y : ℂ) ^ z * g z * mollifier chi U (rho + z)
  refine ⟨F, ?_, ?_⟩
  · intro z hz
    unfold F
    have hpowDiff : Differentiable ℂ (fun w : ℂ => (Y : ℂ) ^ w) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
    exact (((analyticAt_Gamma_add_one_of_mem_contourStrip hz).mul
      (hpowDiff.analyticAt z)).mul
      (hg z)).mul
      ((analyticAt_mollifier chi (rho + z)).comp (by fun_prop))
  · intro z hz
    unfold F gammaMellinWeight
    rw [hLg z, Complex.Gamma_add_one z hz]
    ring

/-! ## Exact finite rectangle balance -/

/-- The four-side identity underlying the contour shift.  This is an exact
finite statement; no limit or tail estimate is hidden in it. -/
theorem finite_rectangle_balance
    (F : ℂ → ℂ) {a c B : ℝ} (ha : a ≤ c) (hB : 0 ≤ B)
    (hF : ∀ z ∈ Set.uIcc a c ×ℂ Set.uIcc (-B) B, AnalyticAt ℂ F z) :
    (∫ x : ℝ in a..c, F (x - B * I)) -
        (∫ x : ℝ in a..c, F (x + B * I)) +
      I * (∫ y : ℝ in -B..B, F (c + y * I)) -
      I * (∫ y : ℝ in -B..B, F (a + y * I)) = 0 := by
  have hdiff : DifferentiableOn ℂ F
      (Set.uIcc a c ×ℂ Set.uIcc (-B) B) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    F (a - B * I) (c + B * I) (by
      simpa [Complex.reProdIm, ha, hB] using hdiff)
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h

/-- Exact finite rectangle shift for the paper endpoints
`a = 1/2 - Re rho` and `c = 1/2`.  This is the residue-cancelled topological
core of (A.4). -/
theorem finiteRectangle_mollifiedDetector_shift
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} {U : ℕ} {Y B : ℝ}
    (hY : 0 < Y) (hB : 0 ≤ B)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1) :
    let a : ℝ := 1 / 2 - rho.re
    (∫ x : ℝ in a..(1 / 2),
        regularizedDetectorIntegrand chi rho U Y (x - B * I)) -
      (∫ x : ℝ in a..(1 / 2),
        regularizedDetectorIntegrand chi rho U Y (x + B * I)) +
      I * (∫ t : ℝ in -B..B,
        regularizedDetectorIntegrand chi rho U Y ((1 / 2 : ℝ) + t * I)) -
      I * (∫ t : ℝ in -B..B,
        regularizedDetectorIntegrand chi rho U Y (a + t * I)) = 0 := by
  dsimp only
  apply finite_rectangle_balance
  · linarith
  · exact hB
  · intro z hz
    apply analyticAt_regularizedDetectorIntegrand chi hchi hY
    change -1 < z.re
    have hleft : 1 / 2 - rho.re ≤ z.re := by
      have hle : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
      have hzleft := hz.1.1
      rw [min_eq_left hle] at hzleft
      exact hzleft
    linarith

/-- Each horizontal side is bounded by its literal length times a pointwise
majorant.  This is the deterministic boundary estimate used before inserting
Stirling and vertical-growth bounds. -/
theorem horizontal_segment_norm_le
    (F : ℂ → ℂ) {a c B M : ℝ}
    (hM : ∀ x ∈ Set.uIoc a c, ‖F (x + B * I)‖ ≤ M) :
    ‖∫ x : ℝ in a..c, F (x + B * I)‖ ≤ M * |c - a| :=
  intervalIntegral.norm_integral_le_of_norm_le_const hM

/-- The exact contour error is the sum of the two horizontal boundary
integrals.  No asymptotic decay is assumed. -/
theorem vertical_shift_error_le_horizontal_boundaries
    (F : ℂ → ℂ) {a c B : ℝ} (ha : a ≤ c) (hB : 0 ≤ B)
    (hF : ∀ z ∈ Set.uIcc a c ×ℂ Set.uIcc (-B) B,
      AnalyticAt ℂ F z) :
    ‖(∫ y : ℝ in -B..B, F (c + y * I)) -
        (∫ y : ℝ in -B..B, F (a + y * I))‖ ≤
      ‖∫ x : ℝ in a..c, F (x - B * I)‖ +
        ‖∫ x : ℝ in a..c, F (x + B * I)‖ := by
  have hbalance := finite_rectangle_balance F ha hB hF
  have heq :
      I * ((∫ y : ℝ in -B..B, F (c + y * I)) -
        (∫ y : ℝ in -B..B, F (a + y * I))) =
      (∫ x : ℝ in a..c, F (x + B * I)) -
        (∫ x : ℝ in a..c, F (x - B * I)) := by
    linear_combination hbalance
  have hnorm := norm_sub_le
    (∫ x : ℝ in a..c, F (x + B * I))
    (∫ x : ℝ in a..c, F (x - B * I))
  rw [← heq, norm_mul, Complex.norm_I, one_mul] at hnorm
  simpa only [add_comm] using hnorm

/-- If the two horizontal sides have pointwise majorants, the contour-shift
error is bounded explicitly by their sum times the width of the strip. -/
theorem vertical_shift_error_le_pointwise_boundary_majorants
    (F : ℂ → ℂ) {a c B Mminus Mplus : ℝ}
    (ha : a ≤ c) (hB : 0 ≤ B)
    (hF : ∀ z ∈ Set.uIcc a c ×ℂ Set.uIcc (-B) B,
      AnalyticAt ℂ F z)
    (hminus : ∀ x ∈ Set.uIoc a c, ‖F (x - B * I)‖ ≤ Mminus)
    (hplus : ∀ x ∈ Set.uIoc a c, ‖F (x + B * I)‖ ≤ Mplus) :
    ‖(∫ y : ℝ in -B..B, F (c + y * I)) -
        (∫ y : ℝ in -B..B, F (a + y * I))‖ ≤
      (Mminus + Mplus) * |c - a| := by
  refine (vertical_shift_error_le_horizontal_boundaries F ha hB hF).trans ?_
  calc
    ‖∫ x : ℝ in a..c, F (x - B * I)‖ +
        ‖∫ x : ℝ in a..c, F (x + B * I)‖ ≤
      Mminus * |c - a| + Mplus * |c - a| :=
        add_le_add
          (intervalIntegral.norm_integral_le_of_norm_le_const hminus)
          (intervalIntegral.norm_integral_le_of_norm_le_const hplus)
    _ = (Mminus + Mplus) * |c - a| := by ring

/-- Instantiation of the finite contour balance for the genuine detector
extension.  The strip condition is exactly the paper range
`a = 1/2-beta > -1`. -/
theorem exists_finite_detector_contour_balance
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1) (U : ℕ)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    {Y a c B : ℝ} (hY : 0 < Y) (haStrip : -1 < a)
    (hac : a ≤ c) (hB : 0 ≤ B) :
    ∃ F : ℂ → ℂ,
      (∀ z, z ≠ 0 →
        F z = gammaMellinWeight Y z *
          DirichletCharacter.LFunction chi (rho + z) *
          mollifier chi U (rho + z)) ∧
      (∫ x : ℝ in a..c, F (x - B * I)) -
          (∫ x : ℝ in a..c, F (x + B * I)) +
        I * (∫ y : ℝ in -B..B, F (c + y * I)) -
        I * (∫ y : ℝ in -B..B, F (a + y * I)) = 0 := by
  obtain ⟨F, hFanalytic, hFraw⟩ :=
    exists_detectorExtension chi hchi U hrho hY
  refine ⟨F, hFraw, finite_rectangle_balance F hac hB ?_⟩
  intro z hz
  apply hFanalytic z
  rw [contourStrip]
  have haz : a ≤ z.re := by
    simpa [min_eq_left hac] using hz.1.1
  exact lt_of_lt_of_le haStrip haz

end

end MAPAppendixA4Detector
