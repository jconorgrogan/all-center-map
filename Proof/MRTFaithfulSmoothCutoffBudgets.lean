import MRTFaithfulSmoothCutoff
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Derivative and L1 budgets for the faithful MRT cutoff

These are the concrete cutoff facts consumed by the existing low/high
projection calculus.  The constants remain explicit existential data; no
analytic estimate is assumed.
-/

namespace MAPMRTFaithfulSmoothCutoffBudgets

open MeasureTheory
open scoped FourierTransform
open MAPMRTFaithfulSmoothCutoff MAPMRTProposition51HardBranch

noncomputable section

def faithfulCutoffDeriv (y : ℝ) : ℝ := deriv faithfulCutoff y

theorem faithfulCutoff_hasDerivAt (y : ℝ) :
    HasDerivAt faithfulCutoff (faithfulCutoffDeriv y) y := by
  exact ((faithfulCutoff_contDiff (n := (⊤ : ℕ∞))).differentiable
    (by simp)).differentiableAt.hasDerivAt

theorem faithfulCutoffDeriv_continuous : Continuous faithfulCutoffDeriv := by
  exact (faithfulCutoff_contDiff (n := (⊤ : ℕ∞))).continuous_deriv (by simp)

theorem faithfulCutoffDeriv_hasCompactSupport :
    HasCompactSupport faithfulCutoffDeriv := by
  exact faithfulCutoffBump.hasCompactSupport.deriv

/-- A nonzero derivative of the faithful cutoff is still confined to the
same closed radius-`1/8` support as the cutoff itself.  This is the exact
support fact needed when the differentiated packet is recentered on page 47. -/
theorem abs_le_eighth_of_faithfulCutoffDeriv_ne_zero
    {y : ℝ} (hy : faithfulCutoffDeriv y ≠ 0) : |y| ≤ 1 / 8 := by
  have hsupp : y ∈ Function.support (deriv faithfulCutoff) := by
    simpa [faithfulCutoffDeriv] using hy
  have hts : y ∈ tsupport faithfulCutoff := support_deriv_subset hsupp
  change y ∈ tsupport faithfulCutoffBump at hts
  rw [faithfulCutoffBump.tsupport_eq] at hts
  simpa [Metric.mem_closedBall, Real.dist_eq, faithfulCutoffBump] using hts

/-- A finite nonnegative absolute derivative budget for the concrete bump. -/
theorem exists_faithfulCutoffDeriv_bound :
    ∃ Bcut : ℝ, 0 ≤ Bcut ∧ ∀ y : ℝ, |faithfulCutoffDeriv y| ≤ Bcut := by
  obtain ⟨Bcut, hBcut⟩ :=
    faithfulCutoffDeriv_continuous.bounded_above_of_compact_support
      faithfulCutoffDeriv_hasCompactSupport
  have hnonneg : 0 ≤ Bcut :=
    (norm_nonneg (faithfulCutoffDeriv 0)).trans (hBcut 0)
  refine ⟨Bcut, hnonneg, ?_⟩
  intro y
  simpa [Real.norm_eq_abs] using hBcut y

def faithfulCutoffDerivBudget : ℝ :=
  Classical.choose exists_faithfulCutoffDeriv_bound

theorem faithfulCutoffDerivBudget_nonneg : 0 ≤ faithfulCutoffDerivBudget :=
  (Classical.choose_spec exists_faithfulCutoffDeriv_bound).1

theorem abs_faithfulCutoffDeriv_le (y : ℝ) :
    |faithfulCutoffDeriv y| ≤ faithfulCutoffDerivBudget :=
  (Classical.choose_spec exists_faithfulCutoffDeriv_bound).2 y

def faithfulCutoffSecond (y : ℝ) : ℝ := deriv faithfulCutoffDeriv y

theorem faithfulCutoffSecond_hasDerivAt (y : ℝ) :
    HasDerivAt faithfulCutoffDeriv (faithfulCutoffSecond y) y := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) faithfulCutoffDeriv := by
    unfold faithfulCutoffDeriv
    exact (contDiff_infty_iff_deriv.mp faithfulCutoff_contDiff).2
  exact (hd.differentiable (by simp)).differentiableAt.hasDerivAt

theorem faithfulCutoffSecond_continuous : Continuous faithfulCutoffSecond := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) faithfulCutoffDeriv := by
    unfold faithfulCutoffDeriv
    exact (contDiff_infty_iff_deriv.mp faithfulCutoff_contDiff).2
  unfold faithfulCutoffSecond
  exact hd.continuous_deriv (by simp)

theorem faithfulCutoffSecond_hasCompactSupport :
    HasCompactSupport faithfulCutoffSecond := by
  unfold faithfulCutoffSecond
  exact faithfulCutoffDeriv_hasCompactSupport.deriv

theorem faithfulCutoffDeriv_zero_of_one_le {y : ℝ} (hy : 1 ≤ |y|) :
    faithfulCutoffDeriv y = 0 := by
  by_contra hn
  have hsmall := abs_le_eighth_of_faithfulCutoffDeriv_ne_zero hn
  linarith

theorem faithfulCutoffSecond_zero_of_one_le {y : ℝ} (hy : 1 ≤ |y|) :
    faithfulCutoffSecond y = 0 := by
  have hout : y ∉ tsupport faithfulCutoffDeriv := by
    intro hmem
    have hmem' : y ∈ tsupport faithfulCutoff :=
      tsupport_deriv_subset hmem
    change y ∈ tsupport faithfulCutoffBump at hmem'
    rw [faithfulCutoffBump.tsupport_eq] at hmem'
    have hsmall : |y| ≤ 1 / 8 := by
      simpa [Metric.mem_closedBall, Real.dist_eq, faithfulCutoffBump] using hmem'
    linarith
  have heq : faithfulCutoffDeriv =ᶠ[nhds y] 0 := by
    exact notMem_tsupport_iff_eventuallyEq.mp hout
  unfold faithfulCutoffSecond
  simpa using heq.deriv_eq

theorem faithfulCutoffDeriv_abs_integrable :
    Integrable (fun y : ℝ ↦ |faithfulCutoffDeriv y|) := by
  simpa [Real.norm_eq_abs] using
    (faithfulCutoffDeriv_continuous.integrable_of_hasCompactSupport
      faithfulCutoffDeriv_hasCompactSupport).norm

theorem faithfulCutoffSecond_abs_integrable :
    Integrable (fun y : ℝ ↦ |faithfulCutoffSecond y|) := by
  simpa [Real.norm_eq_abs] using
    (faithfulCutoffSecond_continuous.integrable_of_hasCompactSupport
      faithfulCutoffSecond_hasCompactSupport).norm

def faithfulCutoffSecondBudget : ℝ :=
  Classical.choose (faithfulCutoffSecond_continuous.bounded_above_of_compact_support
    faithfulCutoffSecond_hasCompactSupport)

theorem abs_faithfulCutoffSecond_le (y : ℝ) :
    |faithfulCutoffSecond y| ≤ faithfulCutoffSecondBudget := by
  simpa [faithfulCutoffSecondBudget, Real.norm_eq_abs] using
    (Classical.choose_spec
      (faithfulCutoffSecond_continuous.bounded_above_of_compact_support
        faithfulCutoffSecond_hasCompactSupport) y)

theorem faithfulCutoffSecondBudget_nonneg : 0 ≤ faithfulCutoffSecondBudget :=
  (abs_nonneg (faithfulCutoffSecond 0)).trans
    (abs_faithfulCutoffSecond_le 0)

def faithfulCutoffFourierSchwartz : SchwartzMap ℝ ℂ :=
  (SchwartzMap.fourierTransformCLM ℂ) faithfulCutoffSchwartz

def faithfulCutoffFourierDerivSchwartz : SchwartzMap ℝ ℂ :=
  (SchwartzMap.derivCLM ℂ ℂ) faithfulCutoffFourierSchwartz

def faithfulCutoffFourierDeriv (y : ℝ) : ℂ :=
  faithfulCutoffFourierDerivSchwartz y

theorem faithfulCutoffFourierKernel_eq_schwartz :
    cutoffFourierKernel faithfulCutoff = faithfulCutoffFourierSchwartz := by
  unfold cutoffFourierKernel faithfulCutoffFourierSchwartz
  rw [← faithfulCutoffSchwartz_coe]
  funext y
  rw [SchwartzMap.fourierTransformCLM_apply]
  exact congrFun (SchwartzMap.fourier_coe faithfulCutoffSchwartz).symm y

theorem faithfulCutoffFourierKernel_integrable :
    Integrable (cutoffFourierKernel faithfulCutoff) := by
  rw [faithfulCutoffFourierKernel_eq_schwartz]
  exact faithfulCutoffFourierSchwartz.integrable

theorem faithfulCutoffFourierKernel_continuous :
    Continuous (cutoffFourierKernel faithfulCutoff) := by
  rw [faithfulCutoffFourierKernel_eq_schwartz]
  exact faithfulCutoffFourierSchwartz.continuous

theorem faithfulCutoffFourierDeriv_integrable :
    Integrable faithfulCutoffFourierDeriv :=
  faithfulCutoffFourierDerivSchwartz.integrable

theorem faithfulCutoffFourierDeriv_continuous :
    Continuous faithfulCutoffFourierDeriv :=
  faithfulCutoffFourierDerivSchwartz.continuous

theorem faithfulCutoffFourierKernel_hasDerivAt (y : ℝ) :
    HasDerivAt (cutoffFourierKernel faithfulCutoff)
      (faithfulCutoffFourierDeriv y) y := by
  rw [faithfulCutoffFourierKernel_eq_schwartz]
  unfold faithfulCutoffFourierDeriv faithfulCutoffFourierDerivSchwartz
  rw [SchwartzMap.derivCLM_apply]
  exact faithfulCutoffFourierSchwartz.differentiable.differentiableAt.hasDerivAt

def faithfulCutoffFourierDecayConstant (q : ℕ) : ℝ :=
  2 ^ q * (Finset.Iic (q, 0)).sup
    (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2)
      faithfulCutoffFourierSchwartz

def faithfulCutoffFourierDerivDecayConstant (q : ℕ) : ℝ :=
  2 ^ q * (Finset.Iic (q, 0)).sup
    (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2)
      faithfulCutoffFourierDerivSchwartz

theorem faithfulCutoffFourierDecayConstant_nonneg (q : ℕ) :
    0 ≤ faithfulCutoffFourierDecayConstant q := by
  unfold faithfulCutoffFourierDecayConstant
  positivity

theorem faithfulCutoffFourierDerivDecayConstant_nonneg (q : ℕ) :
    0 ≤ faithfulCutoffFourierDerivDecayConstant q := by
  unfold faithfulCutoffFourierDerivDecayConstant
  positivity

theorem norm_faithfulCutoffFourierKernel_le_decay (q : ℕ) (y : ℝ) :
    ‖cutoffFourierKernel faithfulCutoff y‖ ≤
      faithfulCutoffFourierDecayConstant q / (1 + |y|) ^ q := by
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (q, 0)) (k := q) (n := 0)
    le_rfl le_rfl faithfulCutoffFourierSchwartz y
  have hs' :
      (1 + |y|) ^ q * ‖faithfulCutoffFourierSchwartz y‖ ≤
        faithfulCutoffFourierDecayConstant q := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero,
      faithfulCutoffFourierDecayConstant] using hs
  have hden : 0 < (1 + |y|) ^ q := by positivity
  rw [faithfulCutoffFourierKernel_eq_schwartz]
  exact (le_div_iff₀ hden).2 (by simpa [mul_comm] using hs')

theorem norm_faithfulCutoffFourierDeriv_le_decay (q : ℕ) (y : ℝ) :
    ‖faithfulCutoffFourierDeriv y‖ ≤
      faithfulCutoffFourierDerivDecayConstant q / (1 + |y|) ^ q := by
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (q, 0)) (k := q) (n := 0)
    le_rfl le_rfl faithfulCutoffFourierDerivSchwartz y
  have hs' :
      (1 + |y|) ^ q * ‖faithfulCutoffFourierDerivSchwartz y‖ ≤
        faithfulCutoffFourierDerivDecayConstant q := by
    simpa only [Real.norm_eq_abs, norm_iteratedFDeriv_zero,
      faithfulCutoffFourierDerivDecayConstant] using hs
  have hden : 0 < (1 + |y|) ^ q := by positivity
  exact (le_div_iff₀ hden).2 (by
    simpa [faithfulCutoffFourierDeriv, mul_comm] using hs')

#print axioms faithfulCutoff_hasDerivAt
#print axioms abs_le_eighth_of_faithfulCutoffDeriv_ne_zero
#print axioms exists_faithfulCutoffDeriv_bound
#print axioms faithfulCutoffSecond_hasDerivAt
#print axioms faithfulCutoffSecond_zero_of_one_le
#print axioms faithfulCutoffDeriv_abs_integrable
#print axioms faithfulCutoffSecond_abs_integrable
#print axioms abs_faithfulCutoffSecond_le
#print axioms faithfulCutoffFourierKernel_integrable
#print axioms faithfulCutoffFourierKernel_hasDerivAt
#print axioms norm_faithfulCutoffFourierKernel_le_decay
#print axioms norm_faithfulCutoffFourierDeriv_le_decay

end
end MAPMRTFaithfulSmoothCutoffBudgets
