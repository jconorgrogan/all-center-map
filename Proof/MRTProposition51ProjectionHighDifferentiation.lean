import MRTProposition51ProjectionHighDerivative
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# MRT Proposition 5.1: differentiation under the source `x` integral

This module discharges the dominated-differentiation step immediately before
MRT equation (77), under the literal smooth bounded-cutoff and integrable-dual
function hypotheses used in the source proof.
-/

namespace MAPMRTProposition51ProjectionHighDifferentiation

open MeasureTheory Set Filter
open MAPMRTCorollary53Source MAPMRTProposition51HardBranch
open MAPMRTProposition51ProjectionHighDerivative MAPMRTVanDerCorputProof

noncomputable section
open scoped Topology
set_option maxHeartbeats 1200000

theorem sourceDualIntegrandDerivative_factor
    (X H beta : ℝ) (cutoff cutoff' : ℝ → ℝ) (g : ℝ → ℂ)
    (u x : ℝ) :
    sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x =
      sourceDualIntegrandDerivative X H beta cutoff cutoff'
        (fun _ ↦ 1) u x * g x := by
  unfold sourceDualIntegrandDerivative
  simp

theorem sourceDualIntegrand_factor
    (X H beta : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    (u x : ℝ) :
    sourceDualIntegrand X H beta cutoff g u x =
      ((Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
        additivePhase (beta * X * Real.exp u) *
        (cutoff ((X * Real.exp u - x) / H) : ℂ)) * g x := by
  unfold sourceDualIntegrand
  ring

/-- The exact differentiated-integral identity needed to instantiate equation
(77) with the source `G`. -/
theorem hasDerivAt_logarithmicDualFunction
    {X H beta B u : ℝ} {cutoff cutoff' : ℝ → ℝ} {g : ℝ → ℂ}
    (hH : 0 < H) (hB : 0 ≤ B)
    (hcutoffCont : Continuous cutoff)
    (hcutoff'Cont : Continuous cutoff')
    (hcutoffDeriv : ∀ y, HasDerivAt cutoff (cutoff' y) y)
    (hcutoffBound : ∀ y, |cutoff y| ≤ B)
    (hcutoff'Bound : ∀ y, |cutoff' y| ≤ B)
    (hg : Integrable g) :
    HasDerivAt (logarithmicDualFunction X H beta cutoff g)
      (∫ x : ℝ,
        sourceDualIntegrandDerivative X H beta cutoff cutoff' g u x) u := by
  let s : Set ℝ := Set.Icc (u - 1) (u + 1)
  let C : ℝ := Real.sqrt X * Real.exp ((|u| + 1) / 2) *
    (B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp (|u| + 1) * B +
      B * (|X| * Real.exp (|u| + 1) / H))
  let bound : ℝ → ℝ := fun x ↦ C * ‖g x‖
  have hs : s ∈ 𝓝 u := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds u zero_lt_one)
    intro z hz
    have habs : |z - u| < 1 := by simpa [Real.dist_eq] using hz
    rw [abs_lt] at habs
    exact ⟨by linarith, by linarith⟩
  have hFmeas : ∀ z : ℝ,
      AEStronglyMeasurable
        (sourceDualIntegrand X H beta cutoff g z) := by
    intro z
    have hcReal : Continuous (fun x : ℝ ↦
        cutoff ((X * Real.exp z - x) / H)) := by
      exact hcutoffCont.comp (by fun_prop)
    have hc : Continuous (fun x : ℝ ↦
        (cutoff ((X * Real.exp z - x) / H) : ℂ)) := by
      exact Complex.continuous_ofReal.comp hcReal
    have hscalar : Continuous (fun x : ℝ ↦
        (Real.sqrt X : ℂ) * (Real.exp (z / 2) : ℂ) *
          additivePhase (beta * X * Real.exp z) *
          (cutoff ((X * Real.exp z - x) / H) : ℂ)) := by
      fun_prop
    rw [show sourceDualIntegrand X H beta cutoff g z =
        fun x ↦ ((Real.sqrt X : ℂ) * (Real.exp (z / 2) : ℂ) *
          additivePhase (beta * X * Real.exp z) *
          (cutoff ((X * Real.exp z - x) / H) : ℂ)) * g x by
      funext x; exact sourceDualIntegrand_factor X H beta cutoff g z x]
    exact hscalar.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hFint : Integrable (sourceDualIntegrand X H beta cutoff g u) := by
    let K : ℝ := Real.sqrt X * Real.exp (u / 2) * B
    have hscalarMeas := hFmeas u
    have hscalarOnly : AEStronglyMeasurable (fun x : ℝ ↦
        (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
          additivePhase (beta * X * Real.exp u) *
          (cutoff ((X * Real.exp u - x) / H) : ℂ)) := by
      have hcReal : Continuous (fun x : ℝ ↦
          cutoff ((X * Real.exp u - x) / H)) :=
        hcutoffCont.comp (by fun_prop)
      exact (by fun_prop : Continuous (fun x : ℝ ↦
        (Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
          additivePhase (beta * X * Real.exp u) *
          (cutoff ((X * Real.exp u - x) / H) : ℂ))).aestronglyMeasurable
    have hscalarBound : ∀ x : ℝ,
        ‖(Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
          additivePhase (beta * X * Real.exp u) *
          (cutoff ((X * Real.exp u - x) / H) : ℂ)‖ ≤ K := by
      intro x
      unfold K
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_additivePhase, mul_one]
      rw [abs_of_nonneg (Real.sqrt_nonneg X),
        abs_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (hcutoffBound ((X * Real.exp u - x) / H)) (by positivity)
    rw [show sourceDualIntegrand X H beta cutoff g u =
        fun x ↦ ((Real.sqrt X : ℂ) * (Real.exp (u / 2) : ℂ) *
          additivePhase (beta * X * Real.exp u) *
          (cutoff ((X * Real.exp u - x) / H) : ℂ)) * g x by
      funext x; exact sourceDualIntegrand_factor X H beta cutoff g u x]
    exact hg.bdd_mul hscalarOnly (Filter.Eventually.of_forall hscalarBound)
  have hF'deriv : ∀ x z, HasDerivAt
      (fun y ↦ sourceDualIntegrand X H beta cutoff g y x)
      (sourceDualIntegrandDerivative X H beta cutoff cutoff' g z x) z := by
    intro x z
    exact hasDerivAt_sourceDualIntegrand hH.ne' hcutoffDeriv
  have hF'meas : AEStronglyMeasurable
      (sourceDualIntegrandDerivative X H beta cutoff cutoff' g u) := by
    have hc : Continuous (fun x : ℝ ↦
        sourceDualIntegrandDerivative X H beta cutoff cutoff'
          (fun _ ↦ 1) u x) := by
      unfold sourceDualIntegrandDerivative
      fun_prop
    rw [show sourceDualIntegrandDerivative X H beta cutoff cutoff' g u =
        fun x ↦ sourceDualIntegrandDerivative X H beta cutoff cutoff'
          (fun _ ↦ 1) u x * g x by
      funext x
      exact sourceDualIntegrandDerivative_factor X H beta cutoff cutoff' g u x]
    exact hc.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hboundInt : Integrable bound := by
    unfold bound
    exact hg.norm.const_mul C
  have hbound : ∀ x : ℝ, ∀ z ∈ s,
      ‖sourceDualIntegrandDerivative X H beta cutoff cutoff' g z x‖ ≤ bound x := by
    intro x z hz
    have hzTop : z ≤ |u| + 1 := by
      have huabs : u ≤ |u| := le_abs_self u
      exact hz.2.trans (by linarith)
    have he : Real.exp z ≤ Real.exp (|u| + 1) := Real.exp_le_exp.mpr hzTop
    have heHalf : Real.exp (z / 2) ≤ Real.exp ((|u| + 1) / 2) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hm := norm_sourceDualIntegrandDerivative_le hH hB
      hcutoffBound hcutoff'Bound (X := X) (beta := beta) (u := z) (x := x) (g := g)
    unfold bound C
    refine hm.trans ?_
    have hsq : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hEz : 0 ≤ Real.exp (z / 2) := Real.exp_nonneg _
    have hEtop : 0 ≤ Real.exp ((|u| + 1) / 2) := Real.exp_nonneg _
    have hinner :
        B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp z * B +
            B * (|X| * Real.exp z / H) ≤
          B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp (|u| + 1) * B +
            B * (|X| * Real.exp (|u| + 1) / H) := by
      gcongr
    have hinner0 : 0 ≤
        B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp z * B +
          B * (|X| * Real.exp z / H) := by positivity
    calc
      Real.sqrt X * Real.exp (z / 2) *
          (B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp z * B +
            B * (|X| * Real.exp z / H)) * ‖g x‖ ≤
        Real.sqrt X * Real.exp ((|u| + 1) / 2) *
          (B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp z * B +
            B * (|X| * Real.exp z / H)) * ‖g x‖ := by gcongr
      _ ≤ Real.sqrt X * Real.exp ((|u| + 1) / 2) *
          (B / 2 + 2 * Real.pi * |beta| * |X| * Real.exp (|u| + 1) * B +
            B * (|X| * Real.exp (|u| + 1) / H)) * ‖g x‖ := by gcongr
  have hparam := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x ↦ sourceDualIntegrand X H beta cutoff g z x)
    (F' := fun z x ↦ sourceDualIntegrandDerivative X H beta cutoff cutoff' g z x)
    (bound := bound) hs
    (Filter.Eventually.of_forall hFmeas) hFint hF'meas
    (Filter.Eventually.of_forall hbound) hboundInt
    (Filter.Eventually.of_forall fun x z hz ↦ hF'deriv x z)
  have hderiv := hparam.2
  have hfun : (fun z ↦ ∫ x : ℝ,
      sourceDualIntegrand X H beta cutoff g z x) =
      logarithmicDualFunction X H beta cutoff g := by
    funext z
    exact (logarithmicDualFunction_eq_integral_sourceDualIntegrand
      (X := X) (H := H) (beta := beta) (u := z)
      (cutoff := cutoff) (g := g) (by
        -- This premise is retained by the older algebra lemma but is not used.
        exact hg.bdd_mul
          ((Complex.continuous_ofReal.comp
            (hcutoffCont.comp (by fun_prop))).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun x ↦ by
            simpa using hcutoffBound ((X * Real.exp z - x) / H)))).symm
  rw [hfun] at hderiv
  exact hderiv

end
end MAPMRTProposition51ProjectionHighDifferentiation

#print axioms MAPMRTProposition51ProjectionHighDifferentiation.hasDerivAt_logarithmicDualFunction
