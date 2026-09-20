import GuthMaynardS2ShortGapPhase
import GuthMaynardS1Source

namespace GuthMaynardS2ShortGapKernel
open Real Complex Set MeasureTheory
open scoped Topology
open GuthMaynardLemma62Fubini
open GuthMaynardS2ShortGapPhase
open GuthMaynardSectionThreeCutoff GuthMaynardSectionThreeCutoffDerivativeBudget
open GuthMaynardLemma62FarTail GuthMaynardLemma62MellinInsertion
open GuthMaynardLemma62ReflectionSubstitution
open MAPMRTNonstationaryPhaseInverse MAPMRTNonstationaryPhaseTwoIBP
open MAPMRTCorollary53Source MAPMRTVanDerCorputProof
noncomputable section

def budget (j : ℕ) : ℝ := ∫ u : ℝ in (1/2)..3, ‖iteratedDeriv j sectionThreeCutoff u‖
def kernelConstant : ℝ := 4 * budget 2 + 96 * budget 1 + 832 * budget 0

lemma cutoff_eventually_zero {x : ℝ} (hx : x ∉ Icc (1:ℝ) 2) :
    sectionThreeCutoff =ᶠ[𝓝 x] (fun _ => 0) := by
  filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with u hu
  exact sectionThreeCutoff_supported u hu

lemma cutoff_end (x : ℝ) (hx : x ∉ Icc (1:ℝ) 2) :
    sectionThreeCutoff x = 0 ∧ deriv sectionThreeCutoff x = 0 := by
  refine ⟨sectionThreeCutoff_supported x hx, ?_⟩
  exact (cutoff_eventually_zero hx).deriv_eq.trans (by simp)

lemma kernel_integral (t xi : ℝ) : GuthMaynardS1Source.sourceHhat t xi =
    ∫ u : ℝ in (1/2)..3, additivePhase (phase t xi u) * sectionThreeCutoff u := by
  change sectionThreeFourierCoefficient t xi = _
  rw [sectionThreeFourierCoefficient_eq_extendedIntegral t xi (by norm_num : (1/2:ℝ)≤1)
    (by norm_num : (2:ℝ)≤3), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤3)]
  apply intervalIntegral.integral_congr
  intro u hu
  have hu0 : 0 < u := by rw [uIcc_of_le (by norm_num)] at hu; linarith [hu.1]
  unfold sectionThreeBaseIntegrand sectionThreeFourierPhase sectionThreeOscillatory
    phase additivePhase
  rw [← oscillatoryPowerExp_eq_cpow hu0]
  unfold oscillatoryPowerExp
  simp only
  calc
    _ = (Complex.exp (((-2 * Real.pi * u * xi : ℝ) : ℂ) * I) *
        Complex.exp (I * (t : ℂ) * (Real.log u : ℂ))) * sectionThreeCutoff u := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      field_simp [Real.pi_ne_zero]
      ring

/-- Uniform short-gap estimate for the literal Fourier coefficient, all signs. -/
theorem norm_sourceHhat_le {t xi : ℝ} (hxi : xi ≠ 0) (ht : |t| ≤ |xi|) :
    ‖GuthMaynardS1Source.sourceHhat t xi‖ ≤ kernelConstant / |xi| ^ 2 := by
  let p := first t xi
  let p' := second t
  let p'' := third t
  let E := fun u => additivePhase (phase t xi u)
  let Ed := fun u => ((2 * Real.pi : ℂ) * Complex.I * (p u : ℂ)) * E u
  have hx : 0 < |xi| := abs_pos.mpr hxi
  have hp0 : ∀ u ∈ Icc (1/2:ℝ) 3, p u ≠ 0 := by
    intro u hu
    exact abs_pos.mp ((by positivity : 0 < |xi|/2).trans_le (first_lower ht hu))
  have hp : ∀ u ∈ Icc (1/2:ℝ) 3, HasDerivAt p (p' u) u := by
    intro u hu; exact first_deriv (by linarith [hu.1])
  have hp' : ∀ u ∈ Icc (1/2:ℝ) 3, HasDerivAt p' (p'' u) u := by
    intro u hu; exact second_deriv (by linarith [hu.1])
  have hE : ∀ u ∈ Icc (1/2:ℝ) 3, HasDerivAt E (Ed u) u := by
    intro u hu; exact hasDerivAt_additivePhase_comp (phase_deriv (by linarith [hu.1]))
  have hpCont : ContinuousOn p (Icc (1/2:ℝ) 3) := fun u hu => (hp u hu).continuousAt.continuousWithinAt
  have hp'Cont : ContinuousOn p' (Icc (1/2:ℝ) 3) := fun u hu => (hp' u hu).continuousAt.continuousWithinAt
  have hp''Cont : ContinuousOn p'' (Icc (1/2:ℝ) 3) := by
    apply continuousOn_const.div (continuousOn_const.mul (continuousOn_id.pow 3))
    intro u hu; exact mul_ne_zero Real.pi_ne_zero (pow_ne_zero 3 (by change u ≠ 0; linarith [hu.1]))
  have hECont : ContinuousOn E (Icc (1/2:ℝ) 3) := fun u hu => (hE u hu).continuousAt.continuousWithinAt
  have hEdCont : ContinuousOn Ed (Icc (1/2:ℝ) 3) := by
    exact ((continuousOn_const.mul continuousOn_const).mul
      (Complex.continuous_ofReal.comp_continuousOn hpCont)).mul hECont
  have hqddCont : ContinuousOn (inversePhaseDerivativeSecond p p' p'') (Icc (1/2:ℝ) 3) := by
    unfold inversePhaseDerivativeSecond
    apply ContinuousOn.mul
    · apply Complex.continuous_ofReal.comp_continuousOn
      apply ContinuousOn.div
      · exact (hp''Cont.mul hpCont).sub (continuousOn_const.mul (hp'Cont.pow 2))
      · exact continuousOn_const.mul (hpCont.pow 3)
      · intro u hu; exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (pow_ne_zero 3 (hp0 u hu))
    · exact continuousOn_const
  have ha : ∀ u ∈ Icc (1/2:ℝ) 3, HasDerivAt sectionThreeCutoff (deriv sectionThreeCutoff u) u := by
    intro u _; exact (sectionThreeCutoff_contDiff.differentiable (by simp) u).hasDerivAt
  have ha' : ∀ u ∈ Icc (1/2:ℝ) 3,
      HasDerivAt (deriv sectionThreeCutoff) (deriv (deriv sectionThreeCutoff) u) u := by
    intro u _
    exact ((contDiff_infty_iff_deriv.mp sectionThreeCutoff_contDiff).2.differentiable (by simp) u).hasDerivAt
  have ha''Cont : ContinuousOn (deriv (deriv sectionThreeCutoff)) (Icc (1/2:ℝ) 3) :=
    ((contDiff_infty_iff_deriv.mp sectionThreeCutoff_contDiff).2.continuous_deriv (by simp)).continuousOn
  have hl := cutoff_end (1/2) (by norm_num)
  have hr := cutoff_end 3 (by norm_num)
  have h := norm_integral_le_two_ibp_budgets (by norm_num : (1/2:ℝ)≤3) hE
    (fun u hu => hasDerivAt_inversePhaseDerivative (hp0 u hu) (hp u hu))
    (fun u hu => hasDerivAt_inversePhaseDerivativeDeriv (hp0 u hu) (hp u hu) (hp' u hu))
    ha ha' hEdCont hqddCont ha''Cont
    (fun u hu => inversePhaseDerivative_mul_phaseDeriv (hp0 u hu))
    hl.1 hr.1 hl.2 hr.2
    (le_refl (budget 0))
    (show (∫ u : ℝ in (1/2)..3, ‖deriv sectionThreeCutoff u‖) ≤ budget 1 by simp [budget, iteratedDeriv_succ])
    (show (∫ u : ℝ in (1/2)..3, ‖deriv (deriv sectionThreeCutoff) u‖) ≤ budget 2 by simp [budget, iteratedDeriv_succ])
    (fun u hu => (inverse_bounds hxi ht hu).1)
    (fun u hu => (inverse_bounds hxi ht hu).2.1)
    (fun u hu => (inverse_bounds hxi ht hu).2.2)
    (fun u _ => norm_additivePhase _) (by positivity) (by positivity) (by positivity)
  rw [kernel_integral]
  exact h.trans_eq (by unfold kernelConstant; field_simp; ring)

#print axioms norm_sourceHhat_le
end
end GuthMaynardS2ShortGapKernel
