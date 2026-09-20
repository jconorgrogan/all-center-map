import MRTProposition51HardBranch
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# A literal smooth cutoff and the resulting compact logarithmic dual function

This supplies the cutoff left implicit in MRT Proposition 5.1.  Its inner
radius is `1/2` and outer radius is `1`, exactly matching the source's two
cutoff windows.  The logarithmic support proof uses the actual MAP aperture
and the source support `x ∈ [X/2,4X]`.
-/

namespace MAPLiteralCutoffDual

open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MAPAllCenterApertureTransfer
open MAPMRTProposition51HardBranch
open MAPMRTCorollary53Source

noncomputable section

private theorem baseAperture_le_quarter {ε X : ℝ} (hX : 4 ≤ X) :
    baseAperture ε X ≤ X / 4 := by
  have hXone : 1 ≤ X := by linarith
  have hreserve : apertureReserve ε ≤ 1 / 1200 := by
    unfold apertureReserve
    exact min_le_right _ _
  have hexponent : 2 / 15 + apertureReserve ε ≤ 1 / 2 := by linarith
  have hpow : Real.rpow X (2 / 15 + apertureReserve ε) ≤
      Real.rpow X (1 / 2) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hsqrt : Real.sqrt X ≤ X / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  rw [show Real.rpow X (1 / 2) = Real.sqrt X from
    (Real.sqrt_eq_rpow X).symm] at hpow
  unfold baseAperture
  nlinarith

/-- The canonical `C^∞` real bump with inner radius `1/2` and outer radius `1`. -/
def literalCutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The concrete MRT cutoff. -/
def literalCutoff (y : ℝ) : ℝ := literalCutoffBump y

theorem literalCutoff_contDiff {n : ℕ∞} : ContDiff ℝ n literalCutoff := by
  exact literalCutoffBump.contDiff

theorem literalCutoff_continuous : Continuous literalCutoff :=
  (literalCutoff_contDiff (n := (0 : ℕ∞))).continuous

theorem literalCutoff_one {y : ℝ} (hy : |y| ≤ 1 / 2) :
    literalCutoff y = 1 := by
  apply literalCutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, literalCutoffBump] using hy

theorem literalCutoff_zero {y : ℝ} (hy : 1 ≤ |y|) :
    literalCutoff y = 0 := by
  apply literalCutoffBump.zero_of_le_dist
  simpa [Real.dist_eq] using hy

theorem literalCutoff_nonneg (y : ℝ) : 0 ≤ literalCutoff y :=
  literalCutoffBump.nonneg

theorem literalCutoff_le_one (y : ℝ) : literalCutoff y ≤ 1 :=
  literalCutoffBump.le_one

theorem abs_literalCutoff_le_one (y : ℝ) : |literalCutoff y| ≤ 1 := by
  rw [abs_of_nonneg (literalCutoff_nonneg y)]
  exact literalCutoff_le_one y

/-- The actual first derivative passed to the differentiated source identity. -/
def literalCutoffDeriv (y : ℝ) : ℝ := deriv literalCutoff y

theorem literalCutoff_hasDerivAt (y : ℝ) :
    HasDerivAt literalCutoff (literalCutoffDeriv y) y := by
  exact ((literalCutoff_contDiff (n := (1 : ℕ∞))).differentiable
    (by norm_num)).differentiableAt.hasDerivAt

theorem literalCutoffDeriv_continuous : Continuous literalCutoffDeriv := by
  exact (literalCutoff_contDiff (n := (2 : ℕ))).continuous_deriv (by norm_num)

theorem literalCutoffDeriv_zero {y : ℝ} (hy : 1 < |y|) :
    literalCutoffDeriv y = 0 := by
  have heq : literalCutoff =ᶠ[nhds y] 0 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds (show y ∈ Metric.ball y (|y| - 1) by
      simp [sub_pos.mpr hy])] with z hz
    apply literalCutoff_zero
    have hdist : |z - y| < |y| - 1 := by simpa [Real.dist_eq] using hz
    have := abs_sub_abs_le_abs_sub y z
    rw [abs_sub_comm] at this
    linarith
  simpa using heq.deriv_eq

/-- The source's concrete logarithmic function `G`. -/
def literalLogarithmicDualFunction
    (ε X beta : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  logarithmicDualFunction X (baseAperture ε X) beta literalCutoff g

private theorem exp_lt_quarter_of_lt_neg_log_four {u : ℝ}
    (hu : u < -Real.log 4) : Real.exp u < 1 / 4 := by
  have h := Real.exp_lt_exp.mpr hu
  rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)] at h
  norm_num at h ⊢
  exact h

private theorem five_lt_exp_of_log_five_lt {u : ℝ}
    (hu : Real.log 5 < u) : 5 < Real.exp u := by
  have h := Real.exp_lt_exp.mpr hu
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 5)] at h
  exact h

theorem literalLogarithmicDualFunction_eq_zero_off_logWindow
    {ε X beta u : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hu : u ∉ Set.Icc (-Real.log 4) (Real.log 5)) :
    literalLogarithmicDualFunction ε X beta g u = 0 := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hHquarter := baseAperture_le_quarter (ε := ε) hX
  have hpoint : ∀ x : ℝ,
      (literalCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x = 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
    · have hHpos := baseAperture_pos (ε := ε) hXpos
      apply mul_eq_zero_of_left
      exact_mod_cast literalCutoff_zero (y := (X * Real.exp u - x) / baseAperture ε X) (by
        rw [abs_div, abs_of_pos hHpos]
        apply (le_div_iff₀ hHpos).2
        simp only [Set.mem_Icc, not_and_or, not_le] at hu
        rcases hu with hlo | hhi
        · have he := exp_lt_quarter_of_lt_neg_log_four hlo
          have hxe : X * Real.exp u < X / 4 := by
            calc
              X * Real.exp u < X * (1 / 4) := mul_lt_mul_of_pos_left he hXpos
              _ = X / 4 := by ring
          rw [abs_of_nonpos (by linarith [hx.1])]
          linarith [hx.1, hHquarter]
        · have he := five_lt_exp_of_log_five_lt hhi
          have hxe : 5 * X < X * Real.exp u := by
            nlinarith
          rw [abs_of_nonneg (by linarith [hx.2])]
          linarith [hx.2, hHquarter])
    · rw [hgSupport x hx, mul_zero]
  unfold literalLogarithmicDualFunction logarithmicDualFunction
  rw [show (∫ x : ℝ,
      (literalCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x) = 0 by
    simp_rw [hpoint]
    simp]
  simp

theorem literalLogarithmicDualFunction_hasCompactSupport
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    HasCompactSupport (literalLogarithmicDualFunction ε X beta g) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log 4) (Real.log 5)))
  intro u hu
  by_contra hout
  exact hu (literalLogarithmicDualFunction_eq_zero_off_logWindow
    hX hgSupport hout)

theorem literalLogarithmicDualFunction_continuous
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hg : Integrable g) :
    Continuous (literalLogarithmicDualFunction ε X beta g) := by
  have hinner : Continuous (fun u : ℝ ↦ ∫ x : ℝ,
      (literalCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x) := by
    apply MeasureTheory.continuous_of_dominated (bound := fun x ↦ ‖g x‖)
    · intro u
      exact ((Complex.continuous_ofReal.comp
        (literalCutoff_continuous.comp (by fun_prop))).aestronglyMeasurable).mul
          hg.aestronglyMeasurable
    · intro u
      filter_upwards with x
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa using mul_le_of_le_one_left (norm_nonneg (g x))
        (abs_literalCutoff_le_one ((X * Real.exp u - x) / baseAperture ε X))
    · exact hg.norm
    · filter_upwards with x
      exact ((Complex.continuous_ofReal.comp
        (literalCutoff_continuous.comp (by fun_prop))).mul continuous_const)
  unfold literalLogarithmicDualFunction logarithmicDualFunction
  exact (((continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))).mul
    (Complex.continuous_exp.comp (by fun_prop))).mul hinner)

theorem literalLogarithmicDualFunction_integrable
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (literalLogarithmicDualFunction ε X beta g) := by
  exact (literalLogarithmicDualFunction_continuous
      (lt_of_lt_of_le (by norm_num) hX) hg).integrable_of_hasCompactSupport
    (literalLogarithmicDualFunction_hasCompactSupport hX hgSupport)

/-- The literal two-variable kernel occurring when the Fourier transform of
`literalCutoff` is opened in the one-scale projection calculation. -/
def literalOneScaleFubiniKernel
    (T u : ℝ) (G : ℝ → ℂ) (v y : ℝ) : ℂ :=
  G (u - 2 * Real.pi * v / T) *
    (additivePhase (-v * y) * (literalCutoff y : ℂ))

theorem literalCutoff_integrable_complex :
    Integrable (fun y : ℝ ↦ (literalCutoff y : ℂ)) := by
  exact (literalCutoff_continuous.integrable_of_hasCompactSupport
    literalCutoffBump.hasCompactSupport).ofReal

/-- The concrete cutoff, regarded as a complex Schwartz function. -/
def literalCutoffSchwartz : SchwartzMap ℝ ℂ :=
  (literalCutoffBump.hasCompactSupport.comp_left
      (show Complex.ofReal (0 : ℝ) = 0 by simp)).toSchwartzMap
    (ContDiff.continuousLinearMap_comp Complex.ofRealCLM
      (literalCutoff_contDiff (n := (⊤ : ℕ∞))))

theorem literalCutoffSchwartz_coe :
    (literalCutoffSchwartz : ℝ → ℂ) = fun y ↦ (literalCutoff y : ℂ) := by
  rfl

/-- The Fourier kernel of the literal cutoff is integrable.  This is the
actual Schwartz input needed by the projection Fubini argument. -/
theorem literalCutoffFourierKernel_integrable :
    Integrable (cutoffFourierKernel literalCutoff) := by
  have hfourier : Integrable
      (fun v : ℝ ↦ (𝓕 literalCutoffSchwartz) v) :=
    (𝓕 literalCutoffSchwartz).integrable
  apply hfourier.congr
  filter_upwards with v
  unfold cutoffFourierKernel
  rw [SchwartzMap.fourier_coe]
  rfl

theorem literalCutoffFourierKernel_continuous :
    Continuous (cutoffFourierKernel literalCutoff) := by
  have hcontinuous : Continuous
      (fun v : ℝ ↦ (𝓕 literalCutoffSchwartz) v) :=
    (𝓕 literalCutoffSchwartz).continuous
  convert hcontinuous using 1

/-- This is the exact Fubini legality needed by the one-scale Equation (79)
transform, with no additional regularity assumption on `G` beyond `L¹`. -/
theorem literalOneScaleFubiniKernel_integrable
    {T u : ℝ} {G : ℝ → ℂ} (hT : 0 < T) (hG : Integrable G) :
    Integrable (Function.uncurry (literalOneScaleFubiniKernel T u G))
      (volume.prod volume) := by
  let a : ℝ := 2 * Real.pi / T
  have ha : a ≠ 0 := by
    unfold a
    positivity
  have hv : Integrable (fun v : ℝ ↦ G (u - a * v)) :=
    (hG.comp_sub_left u).comp_mul_left' ha
  have hp := hv.mul_prod literalCutoff_integrable_complex
  have hphase : AEStronglyMeasurable
      (Function.uncurry fun v y : ℝ ↦ additivePhase (-v * y))
      (volume.prod volume) := by
    exact (show Continuous
      (Function.uncurry fun v y : ℝ ↦ additivePhase (-v * y)) by
        unfold additivePhase
        exact Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
  have hb := hp.bdd_mul hphase
    (Filter.Eventually.of_forall fun z : ℝ × ℝ ↦ by
      rcases z with ⟨v, y⟩
      change ‖additivePhase (-v * y)‖ ≤ 1
      unfold additivePhase
      rw [Complex.norm_exp]
      simp)
  convert hb using 1
  · funext z
    rcases z with ⟨v, y⟩
    unfold literalOneScaleFubiniKernel Function.uncurry a
    ring

/-- Fully concrete Equation-(79) Fubini input for the source dual function. -/
theorem literalDual_oneScaleFubiniKernel_integrable
    {ε X beta T u : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hT : 0 < T) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (Function.uncurry
      (literalOneScaleFubiniKernel T u
        (literalLogarithmicDualFunction ε X beta g)))
      (volume.prod volume) :=
  literalOneScaleFubiniKernel_integrable hT
    (literalLogarithmicDualFunction_integrable hX hg hgSupport)

end
end MAPLiteralCutoffDual

#print axioms MAPLiteralCutoffDual.literalLogarithmicDualFunction_integrable
#print axioms MAPLiteralCutoffDual.literalCutoffFourierKernel_integrable
#print axioms MAPLiteralCutoffDual.literalDual_oneScaleFubiniKernel_integrable
