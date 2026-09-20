import MRTFaithfulSmoothCutoff

/-!
# A faithful smooth cutoff and the resulting compact logarithmic dual function

This supplies the cutoff left implicit in MRT Proposition 5.1.  Its inner
radius is `1/2` and outer radius is `1`, exactly matching the source's two
cutoff windows.  The logarithmic support proof uses the actual MAP aperture
and the source support `x ∈ [X/2,4X]`.
-/

namespace MAPFaithfulCutoffDual

open MeasureTheory Set Filter
open scoped Topology FourierTransform
open MAPAllCenterApertureTransfer
open MAPMRTProposition51HardBranch
open MAPMRTCorollary53Source
open MAPMRTFaithfulSmoothCutoff

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

/-- The source's concrete logarithmic function `G`. -/
def faithfulLogarithmicDualFunction
    (ε X beta : ℝ) (g : ℝ → ℂ) : ℝ → ℂ :=
  logarithmicDualFunction X (baseAperture ε X) beta faithfulCutoff g

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

theorem faithfulLogarithmicDualFunction_eq_zero_off_logWindow
    {ε X beta u : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hu : u ∉ Set.Icc (-Real.log 4) (Real.log 5)) :
    faithfulLogarithmicDualFunction ε X beta g u = 0 := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hHquarter := baseAperture_le_quarter (ε := ε) hX
  have hpoint : ∀ x : ℝ,
      (faithfulCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x = 0 := by
    intro x
    by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
    · have hHpos := baseAperture_pos (ε := ε) hXpos
      apply mul_eq_zero_of_left
      exact_mod_cast faithfulCutoff_zero_of_one_le (y := (X * Real.exp u - x) / baseAperture ε X) (by
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
  unfold faithfulLogarithmicDualFunction logarithmicDualFunction
  rw [show (∫ x : ℝ,
      (faithfulCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x) = 0 by
    simp_rw [hpoint]
    simp]
  simp

theorem faithfulLogarithmicDualFunction_hasCompactSupport
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    HasCompactSupport (faithfulLogarithmicDualFunction ε X beta g) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log 4) (Real.log 5)))
  intro u hu
  by_contra hout
  exact hu (faithfulLogarithmicDualFunction_eq_zero_off_logWindow
    hX hgSupport hout)

theorem faithfulLogarithmicDualFunction_continuous
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hg : Integrable g) :
    Continuous (faithfulLogarithmicDualFunction ε X beta g) := by
  have hinner : Continuous (fun u : ℝ ↦ ∫ x : ℝ,
      (faithfulCutoff ((X * Real.exp u - x) / baseAperture ε X) : ℂ) * g x) := by
    apply MeasureTheory.continuous_of_dominated (bound := fun x ↦ ‖g x‖)
    · intro u
      exact ((Complex.continuous_ofReal.comp
        (faithfulCutoff_continuous.comp (by fun_prop))).aestronglyMeasurable).mul
          hg.aestronglyMeasurable
    · intro u
      filter_upwards with x
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa using mul_le_of_le_one_left (norm_nonneg (g x))
        (abs_faithfulCutoff_le_one ((X * Real.exp u - x) / baseAperture ε X))
    · exact hg.norm
    · filter_upwards with x
      exact ((Complex.continuous_ofReal.comp
        (faithfulCutoff_continuous.comp (by fun_prop))).mul continuous_const)
  unfold faithfulLogarithmicDualFunction logarithmicDualFunction
  exact (((continuous_const.mul (Complex.continuous_ofReal.comp (by fun_prop))).mul
    (Complex.continuous_exp.comp (by fun_prop))).mul hinner)

theorem faithfulLogarithmicDualFunction_integrable
    {ε X beta : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X) (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    Integrable (faithfulLogarithmicDualFunction ε X beta g) := by
  exact (faithfulLogarithmicDualFunction_continuous
      (lt_of_lt_of_le (by norm_num) hX) hg).integrable_of_hasCompactSupport
    (faithfulLogarithmicDualFunction_hasCompactSupport hX hgSupport)

/-- The faithful two-variable kernel used in the one-scale equation-(79)
projection calculation. -/
def faithfulOneScaleFubiniKernel
    (T u : ℝ) (G : ℝ → ℂ) (v y : ℝ) : ℂ :=
  G (u - 2 * Real.pi * v / T) *
    (additivePhase (-v * y) * (faithfulCutoff y : ℂ))

theorem faithfulCutoff_integrable_complex :
    Integrable (fun y : ℝ ↦ (faithfulCutoff y : ℂ)) :=
  faithfulCutoff_integrable.ofReal

/-- Exact Fubini legality for the faithful cutoff and an arbitrary `L¹`
logarithmic dual. -/
theorem faithfulOneScaleFubiniKernel_integrable
    {T u : ℝ} {G : ℝ → ℂ} (hT : 0 < T) (hG : Integrable G) :
    Integrable (Function.uncurry (faithfulOneScaleFubiniKernel T u G))
      (volume.prod volume) := by
  let a : ℝ := 2 * Real.pi / T
  have ha : a ≠ 0 := by
    unfold a
    positivity
  have hv : Integrable (fun v : ℝ ↦ G (u - a * v)) :=
    (hG.comp_sub_left u).comp_mul_left' ha
  have hp := hv.mul_prod faithfulCutoff_integrable_complex
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
  funext z
  rcases z with ⟨v, y⟩
  unfold faithfulOneScaleFubiniKernel Function.uncurry a
  ring


#print axioms MAPFaithfulCutoffDual.faithfulLogarithmicDualFunction_integrable
#print axioms MAPFaithfulCutoffDual.faithfulOneScaleFubiniKernel_integrable

end
end MAPFaithfulCutoffDual
