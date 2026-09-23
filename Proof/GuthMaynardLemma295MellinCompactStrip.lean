import GuthMaynardLemma295MellinPolynomialDecay
import GuthMaynardLemma43FourierIBP
import GuthMaynardLemma295DualTail

/-!
# Uniform Mellin decay on the compact horizontal strip in Lemma 29.5

This file removes the dependence of the fixed-line Schwartz seminorm on the
real part.  The proof expands the logarithmic lift as a fixed compactly
supported Schwartz function times `exp (-sigma*u)` and gives an explicit
finite derivative budget uniform for `sigma` in the contour strip.
-/

namespace GuthMaynardLemma295MellinCompactStrip

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295MellinAllLines
open GuthMaynardLemma295DualTail
open GuthMaynardLemma43FourierIBP

noncomputable section

def sourceSigmaZeroSchwartz : 𝓢(ℝ, ℂ) :=
  sigmaLogLiftSchwartz 0 sourceHZero
    (sigmaLogLift_hasCompactSupport 0
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (sigmaLogLift_contDiff 0 sourceHZero_contDiff)

@[simp] theorem sourceSigmaZeroSchwartz_apply (u : ℝ) :
    sourceSigmaZeroSchwartz u = sigmaLogLift 0 sourceHZero u := rfl

def sourceSigmaZeroDerivative (r : ℕ) : 𝓢(ℝ, ℂ) :=
  schwartzIteratedDerivative r sourceSigmaZeroSchwartz

@[simp] theorem sourceSigmaZeroDerivative_apply (r : ℕ) (u : ℝ) :
    sourceSigmaZeroDerivative r u =
      iteratedDeriv r (sigmaLogLift 0 sourceHZero) u := by
  exact schwartzIteratedDerivative_apply r sourceSigmaZeroSchwartz u

 theorem iteratedDeriv_complex_exp_neg_mul (r : ℕ) (sigma : ℝ) :
    iteratedDeriv r (fun u : ℝ => (Real.exp (-sigma * u) : ℂ)) =
      fun u : ℝ => ((-sigma : ℝ) : ℂ) ^ r *
        (Real.exp (-sigma * u) : ℂ) := by
  induction r with
  | zero => simp [iteratedDeriv_zero]
  | succ r ih =>
      rw [show r + 1 = r.succ by rfl, iteratedDeriv_succ, ih]
      funext u
      have hinner : HasDerivAt (fun u : ℝ => -sigma * u) (-sigma) u := by
        simpa using (hasDerivAt_id u).const_mul (-sigma)
      have hexpR : HasDerivAt (fun u : ℝ => Real.exp (-sigma * u))
          (Real.exp (-sigma * u) * (-sigma)) u := hinner.exp
      have hexpC : HasDerivAt (fun u : ℝ => (Real.exp (-sigma * u) : ℂ))
          ((Real.exp (-sigma * u) * (-sigma) : ℝ) : ℂ) u := by
        change HasDerivAt
          (Complex.ofRealCLM ∘ fun u : ℝ => Real.exp (-sigma * u)) _ u
        simpa using (Complex.ofRealCLM.hasFDerivAt.comp u
          hexpR.hasFDerivAt).hasDerivAt
      have hmul := hexpC.const_mul (((-sigma : ℝ) : ℂ) ^ r)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hmul.deriv

theorem sigmaLogLift_factor (sigma u : ℝ) :
    sigmaLogLift sigma sourceHZero u =
      (Real.exp (-sigma * u) : ℂ) * sigmaLogLift 0 sourceHZero u := by
  simp [sigmaLogLift]

theorem iteratedDeriv_sigmaLogLift (q : ℕ) (sigma u : ℝ) :
    iteratedDeriv q (sigmaLogLift sigma sourceHZero) u =
      ∑ r ∈ Finset.range (q + 1),
        (q.choose r : ℂ) *
          (((-sigma : ℝ) : ℂ) ^ r * (Real.exp (-sigma * u) : ℂ)) *
          sourceSigmaZeroDerivative (q - r) u := by
  have hweightR : ContDiff ℝ (q : ℕ∞)
      (fun y : ℝ => Real.exp (-sigma * y)) := by fun_prop
  have hweightC : ContDiff ℝ (q : ℕ∞)
      (fun y : ℝ => (Real.exp (-sigma * y) : ℂ)) := by
    simpa only [Function.comp_apply] using! Complex.ofRealCLM.contDiff.comp hweightR
  have hweight : ContDiffAt ℝ (q : ℕ∞)
      (fun y : ℝ => (Real.exp (-sigma * y) : ℂ)) u := hweightC.contDiffAt
  have hbase : ContDiffAt ℝ (q : ℕ∞)
      (sigmaLogLift 0 sourceHZero) u :=
    (sigmaLogLift_contDiff 0 sourceHZero_contDiff).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [show sigmaLogLift sigma sourceHZero =
      (fun y : ℝ => (Real.exp (-sigma * y) : ℂ)) *
        sigmaLogLift 0 sourceHZero by
    funext y; exact sigmaLogLift_factor sigma y]
  rw [iteratedDeriv_mul hweight hbase]
  apply Finset.sum_congr rfl
  intro r hr
  rw [congrFun (iteratedDeriv_complex_exp_neg_mul r sigma) u]
  simp only [sourceSigmaZeroDerivative_apply]


def sourceLogSupport : Set ℝ :=
  Set.Icc (-Real.log (5 / 2 : ℝ)) (-Real.log (1 / 2 : ℝ))

theorem tsupport_sourceSigmaZeroSchwartz_subset :
    tsupport (fun u : ℝ => sourceSigmaZeroSchwartz u) ⊆ sourceLogSupport := by
  apply closure_minimal
  · intro u hu
    by_contra hnot
    apply hu
    have hz := sourceHZero_support (Real.exp (-u))
    have hexpNot : Real.exp (-u) ∉ Set.Icc (1 / 2 : ℝ) (5 / 2 : ℝ) := by
      intro hx
      apply hnot
      constructor
      · have h := Real.exp_le_exp.mp
          (show Real.exp (-u) ≤ Real.exp (Real.log (5 / 2 : ℝ)) by
            simpa [Real.exp_log (by norm_num : (0 : ℝ) < 5 / 2)] using hx.2)
        linarith
      · have h := Real.exp_le_exp.mp
          (show Real.exp (Real.log (1 / 2 : ℝ)) ≤ Real.exp (-u) by
            rw [Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
            exact hx.1)
        linarith
    change sigmaLogLift 0 sourceHZero u = 0
    simp [sigmaLogLift, hz hexpNot]
  · exact isClosed_Icc

theorem tsupport_sourceSigmaZeroDerivative_subset (r : ℕ) :
    tsupport (fun u : ℝ => sourceSigmaZeroDerivative r u) ⊆ sourceLogSupport := by
  induction r with
  | zero =>
      simpa [sourceSigmaZeroDerivative, schwartzIteratedDerivative] using
        tsupport_sourceSigmaZeroSchwartz_subset
  | succ r ih =>
      change tsupport
        (fun u : ℝ =>
          ((SchwartzMap.derivCLM ℂ ℂ)^[r.succ] sourceSigmaZeroSchwartz) u) ⊆ _
      rw [Function.iterate_succ_apply']
      exact (SchwartzMap.tsupport_derivCLM_subset ℂ
        ((SchwartzMap.derivCLM ℂ ℂ)^[r] sourceSigmaZeroSchwartz)).trans ih

def stripSigmaRadius (n : ℕ) (upper : ℝ) : ℝ :=
  max |deepLeftSigma n| |upper|

def sourceLogSupportRadius : ℝ :=
  max |(-Real.log (5 / 2 : ℝ))| |(-Real.log (1 / 2 : ℝ))|

def stripPowerRadius (n : ℕ) (upper : ℝ) : ℝ := max 1 (stripSigmaRadius n upper)

def stripExponentialBudget (n : ℕ) (upper : ℝ) : ℝ :=
  Real.exp (stripSigmaRadius n upper * sourceLogSupportRadius)

theorem stripSigmaRadius_nonneg (n : ℕ) (upper : ℝ) : 0 ≤ stripSigmaRadius n upper := by
  exact le_max_of_le_left (abs_nonneg _)

theorem sourceLogSupportRadius_nonneg : 0 ≤ sourceLogSupportRadius := by
  exact le_max_of_le_left (abs_nonneg _)

theorem stripPowerRadius_nonneg (n : ℕ) (upper : ℝ) : 0 ≤ stripPowerRadius n upper := by
  exact (zero_le_one.trans (le_max_left _ _))

theorem norm_pow_mul_exp_le_strip
    {n : ℕ} {upper sigma u : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) upper)
    (m r : ℕ) (hne : sourceSigmaZeroDerivative r u ≠ 0) :
    ‖(((-sigma : ℝ) : ℂ) ^ m * (Real.exp (-sigma * u) : ℂ))‖ ≤
      stripPowerRadius n upper ^ m * stripExponentialBudget n upper := by
  have huTs : u ∈ tsupport (fun y : ℝ => sourceSigmaZeroDerivative r y) :=
    subset_tsupport _ hne
  have hu : u ∈ sourceLogSupport :=
    tsupport_sourceSigmaZeroDerivative_subset r huTs
  have hsigmaAbs : |sigma| ≤ stripSigmaRadius n upper := by
    exact abs_le_max_abs_abs hsigma.1 hsigma.2
  have huAbs : |u| ≤ sourceLogSupportRadius := by
    exact abs_le_max_abs_abs hu.1 hu.2
  have hsigR : |sigma| ≤ stripPowerRadius n upper :=
    hsigmaAbs.trans (le_max_right _ _)
  have hpow : |sigma| ^ m ≤ stripPowerRadius n upper ^ m :=
    pow_le_pow_left₀ (abs_nonneg _) hsigR m
  have hprod : |sigma| * |u| ≤
      stripSigmaRadius n upper * sourceLogSupportRadius :=
    mul_le_mul hsigmaAbs huAbs (abs_nonneg _) (stripSigmaRadius_nonneg n upper)
  have hexponent : -sigma * u ≤
      stripSigmaRadius n upper * sourceLogSupportRadius := by
    calc
      -sigma * u ≤ |sigma| * |u| := by
        simpa [abs_mul, abs_neg] using le_abs_self (-sigma * u)
      _ ≤ _ := hprod
  have hexp : Real.exp (-sigma * u) ≤ stripExponentialBudget n upper := by
    exact Real.exp_le_exp.mpr hexponent
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul hpow hexp (Real.exp_pos _).le
    (pow_nonneg (stripPowerRadius_nonneg n upper) _)

def stripDerivativeL1Constant (n q : ℕ) (upper : ℝ) : ℝ :=
  stripExponentialBudget n upper *
    ∑ r ∈ Finset.range (q + 1),
      (q.choose r : ℝ) * stripPowerRadius n upper ^ r *
        ∫ u : ℝ, ‖sourceSigmaZeroDerivative (q - r) u‖

theorem stripDerivativeL1Constant_nonneg (n q : ℕ) (upper : ℝ) :
    0 ≤ stripDerivativeL1Constant n q upper := by
  unfold stripDerivativeL1Constant
  apply mul_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg
  intro r hr
  exact mul_nonneg
    (mul_nonneg (by positivity) (pow_nonneg (stripPowerRadius_nonneg n upper) _))
    (integral_nonneg (fun _ => norm_nonneg _))


theorem norm_iteratedDeriv_sigmaLogLift_le
    {n : ℕ} {upper sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) upper)
    (q : ℕ) (u : ℝ) :
    ‖iteratedDeriv q (sigmaLogLift sigma sourceHZero) u‖ ≤
      ∑ r ∈ Finset.range (q + 1),
        stripExponentialBudget n upper * (q.choose r : ℝ) *
          stripPowerRadius n upper ^ r *
            ‖sourceSigmaZeroDerivative (q - r) u‖ := by
  rw [iteratedDeriv_sigmaLogLift]
  apply norm_sum_le_of_le
  intro r hr
  by_cases hzero : sourceSigmaZeroDerivative (q - r) u = 0
  · simp [hzero]
  · rw [norm_mul, norm_mul]
    have hfactor := norm_pow_mul_exp_le_strip hsigma r (q - r) hzero
    have hchoose : ‖(q.choose r : ℂ)‖ = (q.choose r : ℝ) := by simp
    rw [hchoose]
    calc
      (q.choose r : ℝ) *
          ‖(((-sigma : ℝ) : ℂ) ^ r * (Real.exp (-sigma * u) : ℂ))‖ *
          ‖sourceSigmaZeroDerivative (q - r) u‖ ≤
        (q.choose r : ℝ) *
          (stripPowerRadius n upper ^ r * stripExponentialBudget n upper) *
          ‖sourceSigmaZeroDerivative (q - r) u‖ := by
            gcongr
      _ = stripExponentialBudget n upper * (q.choose r : ℝ) *
          stripPowerRadius n upper ^ r *
            ‖sourceSigmaZeroDerivative (q - r) u‖ := by ring

theorem integral_norm_iteratedDeriv_sigmaLogLift_le
    {n : ℕ} {upper sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) upper)
    (q : ℕ) :
    (∫ u : ℝ, ‖iteratedDeriv q (sigmaLogLift sigma sourceHZero) u‖) ≤
      stripDerivativeL1Constant n q upper := by
  let f : 𝓢(ℝ, ℂ) := sigmaLogLiftSchwartz sigma sourceHZero
    (sigmaLogLift_hasCompactSupport sigma
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (sigmaLogLift_contDiff sigma sourceHZero_contDiff)
  have hleft : Integrable (fun u : ℝ =>
      ‖iteratedDeriv q (sigmaLogLift sigma sourceHZero) u‖) := by
    have h := (schwartzIteratedDerivative q f).integrable
      (μ := (volume : Measure ℝ)) |>.norm
    simpa [f, schwartzIteratedDerivative_apply] using! h
  have hterm : ∀ r ∈ Finset.range (q + 1), Integrable (fun u : ℝ =>
      stripExponentialBudget n upper * (q.choose r : ℝ) *
        stripPowerRadius n upper ^ r *
          ‖sourceSigmaZeroDerivative (q - r) u‖) := by
    intro r hr
    exact ((sourceSigmaZeroDerivative (q - r)).integrable
      (μ := (volume : Measure ℝ))).norm.const_mul
        (stripExponentialBudget n upper * (q.choose r : ℝ) *
          stripPowerRadius n upper ^ r)
  have hright : Integrable (fun u : ℝ =>
      ∑ r ∈ Finset.range (q + 1),
        stripExponentialBudget n upper * (q.choose r : ℝ) *
          stripPowerRadius n upper ^ r *
            ‖sourceSigmaZeroDerivative (q - r) u‖) :=
    integrable_finsetSum _ hterm
  calc
    (∫ u : ℝ, ‖iteratedDeriv q (sigmaLogLift sigma sourceHZero) u‖) ≤
      ∫ u : ℝ, ∑ r ∈ Finset.range (q + 1),
        stripExponentialBudget n upper * (q.choose r : ℝ) *
          stripPowerRadius n upper ^ r *
            ‖sourceSigmaZeroDerivative (q - r) u‖ := by
      exact MeasureTheory.integral_mono hleft hright
        (norm_iteratedDeriv_sigmaLogLift_le hsigma q)
    _ = stripDerivativeL1Constant n q upper := by
      rw [MeasureTheory.integral_finsetSum _ hterm]
      simp_rw [MeasureTheory.integral_const_mul]
      unfold stripDerivativeL1Constant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    {n : ℕ} {upper sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) upper)
    (q : ℕ) (t : ℝ) :
    |t / (2 * Real.pi)| ^ q *
        ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      stripDerivativeL1Constant n q upper := by
  let f : 𝓢(ℝ, ℂ) := sigmaLogLiftSchwartz sigma sourceHZero
    (sigmaLogLift_hasCompactSupport sigma
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (sigmaLogLift_contDiff sigma sourceHZero_contDiff)
  rw [mellin_vertical_eq_fourier_sigmaLogLift]
  have hFourier :
      𝓕 (sigmaLogLift sigma sourceHZero) (t / (2 * Real.pi)) =
        ((𝓕 f : 𝓢(ℝ, ℂ)) (t / (2 * Real.pi))) := by
    exact congrFun (SchwartzMap.fourier_coe f).symm _
  rw [hFourier]
  exact (absPow_mul_norm_fourier_le_integral_iteratedDerivative
    f q (t / (2 * Real.pi))).trans
      (by simpa [f] using! integral_norm_iteratedDeriv_sigmaLogLift_le hsigma q)

def uniformStripMellinDecayConstant (n k : ℕ) (upper : ℝ) : ℝ :=
  stripDerivativeL1Constant n 0 upper +
    (2 * Real.pi) ^ k * stripDerivativeL1Constant n k upper

theorem uniformStripMellinDecayConstant_nonneg (n k : ℕ) (upper : ℝ) :
    0 ≤ uniformStripMellinDecayConstant n k upper := by
  unfold uniformStripMellinDecayConstant
  exact add_nonneg (stripDerivativeL1Constant_nonneg n 0 upper)
    (mul_nonneg (pow_nonneg (by positivity) _)
      (stripDerivativeL1Constant_nonneg n k upper))

/-- Uniform arbitrary-order Mellin decay across the complete second contour
strip.  This is the compact-strip leaf needed to make both horizontal edges
vanish with one constant independent of their real coordinate. -/
theorem one_add_absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    (n k : ℕ) {upper sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) upper) (t : ℝ) :
    (1 + |t| ^ k) * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      uniformStripMellinDecayConstant n k upper := by
  have hzero := absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    hsigma 0 t
  have hk := absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    hsigma k t
  have hzero' : ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      stripDerivativeL1Constant n 0 upper := by
    simpa using hzero
  have hscale :
      |t| ^ k * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
        (2 * Real.pi) ^ k * stripDerivativeL1Constant n k upper := by
    calc
      |t| ^ k * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ =
          (2 * Real.pi) ^ k *
            (|t / (2 * Real.pi)| ^ k *
              ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), div_pow]
        field_simp [Real.pi_ne_zero]
      _ ≤ (2 * Real.pi) ^ k * stripDerivativeL1Constant n k upper :=
        mul_le_mul_of_nonneg_left hk (pow_nonneg (by positivity) _)
  unfold uniformStripMellinDecayConstant
  nlinarith


/-- Specialization covering the raw first rectangle, and hence also the
reflected rectangle whose right edge is `1/2`. -/
theorem one_add_absPow_mul_norm_mellin_sourceHZero_deepLeft_to_two_le
    (n k : ℕ) {sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) (2 : ℝ)) (t : ℝ) :
    (1 + |t| ^ k) * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      uniformStripMellinDecayConstant n k 2 :=
  one_add_absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    n k hsigma t

/-- Exact reflected-rectangle specialization. -/
theorem one_add_absPow_mul_norm_mellin_sourceHZero_deepLeft_to_half_le
    (n k : ℕ) {sigma : ℝ}
    (hsigma : sigma ∈ Set.Icc (deepLeftSigma n) (1 / 2 : ℝ)) (t : ℝ) :
    (1 + |t| ^ k) * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      uniformStripMellinDecayConstant n k (1 / 2) :=
  one_add_absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
    n k hsigma t

end
end GuthMaynardLemma295MellinCompactStrip

#print axioms GuthMaynardLemma295MellinCompactStrip.iteratedDeriv_sigmaLogLift
#print axioms GuthMaynardLemma295MellinCompactStrip.integral_norm_iteratedDeriv_sigmaLogLift_le
#print axioms GuthMaynardLemma295MellinCompactStrip.one_add_absPow_mul_norm_mellin_sourceHZero_uniform_strip_le
#print axioms GuthMaynardLemma295MellinCompactStrip.one_add_absPow_mul_norm_mellin_sourceHZero_deepLeft_to_two_le
