import MRTProposition51HardBranch
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# A single faithful smooth cutoff for MRT Proposition 5.1

The cutoff has plateau radius `1/10` and support radius `1/8`.  The narrow
support forces a positive Fourier phase throughout `|ξ| ≤ 1`, giving the
uniform lower bound required by the smooth Gallagher step.  The same function
can therefore be used in equations (72), (74), and (76).
-/

namespace MAPMRTFaithfulSmoothCutoff

open MeasureTheory Set Filter
open scoped FourierTransform Topology
open MAPMRTProposition51HardBranch MAPMRTCorollary53Source

noncomputable section

/-- Canonical smooth cutoff, one on `[-1/10,1/10]` and supported in
`[-1/8,1/8]`. -/
def faithfulCutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 10
  rOut := 1 / 8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def faithfulCutoff (y : ℝ) : ℝ := faithfulCutoffBump y

theorem faithfulCutoff_contDiff {n : ℕ∞} :
    ContDiff ℝ n faithfulCutoff := faithfulCutoffBump.contDiff

theorem faithfulCutoff_continuous : Continuous faithfulCutoff :=
  (faithfulCutoff_contDiff (n := (0 : ℕ∞))).continuous

theorem faithfulCutoff_one {y : ℝ} (hy : |y| ≤ 1 / 10) :
    faithfulCutoff y = 1 := by
  apply faithfulCutoffBump.one_of_mem_closedBall
  simpa [Metric.mem_closedBall, Real.dist_eq, faithfulCutoffBump] using hy

theorem faithfulCutoff_zero {y : ℝ} (hy : 1 / 8 ≤ |y|) :
    faithfulCutoff y = 0 := by
  apply faithfulCutoffBump.zero_of_le_dist
  simpa [Real.dist_eq, faithfulCutoffBump] using hy

theorem faithfulCutoff_zero_of_one_le {y : ℝ} (hy : 1 ≤ |y|) :
    faithfulCutoff y = 0 :=
  faithfulCutoff_zero (by linarith)

theorem faithfulCutoff_nonneg (y : ℝ) : 0 ≤ faithfulCutoff y :=
  faithfulCutoffBump.nonneg

theorem faithfulCutoff_le_one (y : ℝ) : faithfulCutoff y ≤ 1 :=
  faithfulCutoffBump.le_one

theorem abs_faithfulCutoff_le_one (y : ℝ) : |faithfulCutoff y| ≤ 1 := by
  rw [abs_of_nonneg (faithfulCutoff_nonneg y)]
  exact faithfulCutoff_le_one y

theorem faithfulCutoff_integrable : Integrable faithfulCutoff :=
  faithfulCutoff_continuous.integrable_of_hasCompactSupport
    faithfulCutoffBump.hasCompactSupport

/-- The faithful cutoff as a complex Schwartz function. -/
def faithfulCutoffSchwartz : SchwartzMap ℝ ℂ :=
  (faithfulCutoffBump.hasCompactSupport.comp_left
      (show Complex.ofReal (0 : ℝ) = 0 by simp)).toSchwartzMap
    (ContDiff.continuousLinearMap_comp Complex.ofRealCLM
      (faithfulCutoff_contDiff (n := (⊤ : ℕ∞))))

theorem faithfulCutoffSchwartz_coe :
    (faithfulCutoffSchwartz : ℝ → ℂ) =
      fun y ↦ (faithfulCutoff y : ℂ) := by
  rfl

/-- The faithful Fourier kernel belongs to `L²`. -/
theorem faithfulCutoffFourierKernel_memLp_two :
    MemLp (cutoffFourierKernel faithfulCutoff) 2 := by
  have hm : MemLp (fun xi : ℝ ↦ (𝓕 faithfulCutoffSchwartz) xi) 2 :=
    (𝓕 faithfulCutoffSchwartz).memLp 2
  unfold cutoffFourierKernel
  rw [← faithfulCutoffSchwartz_coe]
  exact hm

theorem integrable_sq_norm_faithfulCutoffFourierKernel :
    Integrable (fun xi : ℝ ↦
      ‖cutoffFourierKernel faithfulCutoff xi‖ ^ 2) := by
  exact (memLp_two_iff_integrable_sq_norm
    faithfulCutoffFourierKernel_memLp_two.aestronglyMeasurable).1
      faithfulCutoffFourierKernel_memLp_two

theorem faithfulCutoff_integral_lower :
    (1 / 5 : ℝ) ≤ ∫ y : ℝ, faithfulCutoff y := by
  have hset : (∫ y : ℝ in Icc (-(1 / 10 : ℝ)) (1 / 10), faithfulCutoff y) =
      (1 / 5 : ℝ) := by
    calc
      (∫ y : ℝ in Icc (-(1 / 10 : ℝ)) (1 / 10), faithfulCutoff y) =
          ∫ _y : ℝ in Icc (-(1 / 10 : ℝ)) (1 / 10), (1 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict measurableSet_Icc] with y hy
        rw [faithfulCutoff_one]
        exact (abs_le).2 hy
      _ = (1 / 5 : ℝ) := by norm_num [Real.volume_Icc]
  rw [← hset]
  exact setIntegral_le_integral faithfulCutoff_integrable
    (Filter.Eventually.of_forall faithfulCutoff_nonneg)

private theorem cosine_half_le_on_support
    {xi y : ℝ} (hxi : |xi| ≤ 1) (hy : |y| < 1 / 8) :
    (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * (-xi * y)) := by
  have hp : 0 < Real.pi := Real.pi_pos
  have hang : |2 * Real.pi * (-xi * y)| ≤ Real.pi / 4 := by
    calc
      |2 * Real.pi * (-xi * y)| = 2 * Real.pi * |xi| * |y| := by
        simp only [abs_mul, abs_neg, abs_of_pos hp]
        norm_num
        ring
      _ ≤ 2 * Real.pi * 1 * (1 / 8) := by
        gcongr
      _ = Real.pi / 4 := by ring
  rw [← Real.cos_abs]
  rw [← Real.cos_pi_div_three]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
  · linarith
  · exact hang.trans (by nlinarith)

private theorem faithfulCutoff_mul_cos_lower
    {xi : ℝ} (hxi : |xi| ≤ 1) (y : ℝ) :
    (1 / 2 : ℝ) * faithfulCutoff y ≤
      faithfulCutoff y * Real.cos (2 * Real.pi * (-xi * y)) := by
  by_cases hy : |y| < 1 / 8
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left
      (cosine_half_le_on_support hxi hy) (faithfulCutoff_nonneg y)
  · have hz := faithfulCutoff_zero (le_of_not_gt hy)
    simp [hz]

private theorem integrable_faithfulCutoff_mul_cos (xi : ℝ) :
    Integrable (fun y : ℝ ↦
      faithfulCutoff y * Real.cos (2 * Real.pi * (-xi * y))) := by
  exact faithfulCutoff_integrable.bdd_mul
    (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ ↦ Real.cos (2 * Real.pi * (-xi * y))))
    (Filter.Eventually.of_forall fun y ↦ by
      simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (2 * Real.pi * (-xi * y)))
  |>.congr (by
    filter_upwards with y
    ring)

private theorem faithfulCutoffFourierKernel_eq_integral (xi : ℝ) :
    cutoffFourierKernel faithfulCutoff xi =
      ∫ y : ℝ, additivePhase (-xi * y) * (faithfulCutoff y : ℂ) := by
  unfold cutoffFourierKernel
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  unfold additivePhase
  congr 1
  push_cast
  ring_nf

private theorem integrable_faithfulCutoff_complex_phase (xi : ℝ) :
    Integrable (fun y : ℝ ↦
      additivePhase (-xi * y) * (faithfulCutoff y : ℂ)) := by
  have hc : Integrable (fun y : ℝ ↦ (faithfulCutoff y : ℂ)) :=
    Complex.ofRealCLM.integrable_comp faithfulCutoff_integrable
  have hp : AEStronglyMeasurable (fun y : ℝ ↦ additivePhase (-xi * y)) := by
    unfold additivePhase
    fun_prop
  have hb : ∀ᶠ y : ℝ in ae volume, ‖additivePhase (-xi * y)‖ ≤ 1 :=
    Filter.Eventually.of_forall fun y ↦ by
      unfold additivePhase
      rw [show 2 * (Real.pi : ℂ) * ((-xi * y : ℝ) : ℂ) * Complex.I =
        ((2 * Real.pi * (-xi * y) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
  exact hc.bdd_mul hp hb |>.congr (by
    filter_upwards with y
    ring)

private theorem faithfulCutoff_phase_re (xi y : ℝ) :
    (additivePhase (-xi * y) * (faithfulCutoff y : ℂ)).re =
      faithfulCutoff y * Real.cos (2 * Real.pi * (-xi * y)) := by
  unfold additivePhase
  rw [Complex.mul_re, Complex.exp_re]
  simp
  ring

/-- Elementary certified Fourier lower bound required in the published smooth
Gallagher reduction.  The explicit constant `1/10` is deliberately crude. -/
theorem faithfulCutoffFourierKernel_re_lower
    {xi : ℝ} (hxi : |xi| ≤ 1) :
    (1 / 10 : ℝ) ≤ (cutoffFourierKernel faithfulCutoff xi).re := by
  rw [faithfulCutoffFourierKernel_eq_integral]
  have hi := integrable_faithfulCutoff_complex_phase xi
  have hre := Complex.reCLM.integral_comp_comm hi
  change (1 / 10 : ℝ) ≤ Complex.reCLM
    (∫ y : ℝ, additivePhase (-xi * y) * (faithfulCutoff y : ℂ))
  rw [← hre]
  change (1 / 10 : ℝ) ≤ ∫ y : ℝ,
    (additivePhase (-xi * y) * (faithfulCutoff y : ℂ)).re
  simp_rw [faithfulCutoff_phase_re]
  have hmono :
      (∫ y : ℝ, (1 / 2 : ℝ) * faithfulCutoff y) ≤
        ∫ y : ℝ, faithfulCutoff y *
          Real.cos (2 * Real.pi * (-xi * y)) := by
    apply integral_mono
    · exact faithfulCutoff_integrable.const_mul (1 / 2)
    · exact integrable_faithfulCutoff_mul_cos xi
    · exact faithfulCutoff_mul_cos_lower hxi
  rw [integral_const_mul] at hmono
  nlinarith [faithfulCutoff_integral_lower]

/-- Norm form used directly in Plancherel. -/
theorem faithfulCutoffFourierKernel_norm_lower
    {xi : ℝ} (hxi : |xi| ≤ 1) :
    (1 / 10 : ℝ) ≤ ‖cutoffFourierKernel faithfulCutoff xi‖ := by
  exact (faithfulCutoffFourierKernel_re_lower hxi).trans
    ((le_abs_self _).trans (Complex.abs_re_le_norm _))

#print axioms faithfulCutoffFourierKernel_re_lower
#print axioms faithfulCutoffFourierKernel_norm_lower

end
end MAPMRTFaithfulSmoothCutoff
