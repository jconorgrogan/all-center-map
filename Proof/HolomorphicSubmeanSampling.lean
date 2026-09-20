import RecenteredSampling
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul

/-!
# Holomorphic sampling from continuous fourth moments

The MAP fourth-moment consumers are discrete, whereas Ramachandra's proved
source is a continuous fourth moment, uniform in a thin horizontal strip.
This file records the source-faithful deterministic sampling step.  The first
lemma is the exact one-dimensional Sobolev reduction: discrete fourth moments
of a holomorphic trace are controlled by the continuous fourth moment and the
continuous derivative energy.  The remaining analytic task is then isolated
as a Cauchy estimate for that derivative energy from the horizontally-uniform
fourth moment.
-/

namespace HolomorphicSubmeanSampling

open scoped BigOperators
open MeasureTheory CGLProofDAG

noncomputable section

/-- Exact real derivative of a vertical holomorphic trace. -/
theorem hasDerivAt_verticalTrace
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (sigma t : ℝ) :
    HasDerivAt (fun u : ℝ => F ((sigma : ℂ) + u * Complex.I))
      (deriv F ((sigma : ℂ) + t * Complex.I) * Complex.I) t := by
  have hline : HasDerivAt (fun u : ℝ => (sigma : ℂ) + u * Complex.I)
      Complex.I t := by
    convert (hasDerivAt_id t).ofReal_comp.mul_const Complex.I |>.const_add (sigma : ℂ) using 1 <;> simp <;> ring
  exact (hF.differentiableAt.hasDerivAt.comp t hline)

/-- The derivative trace of an entire complex function is continuous. -/
theorem continuous_verticalDerivTrace
    {F : ℂ → ℂ} (hF : Differentiable ℂ F) (sigma : ℝ) :
    Continuous (fun t : ℝ =>
      deriv F ((sigma : ℂ) + t * Complex.I) * Complex.I) := by
  have han : AnalyticOnNhd ℂ F Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hF
  have hderiv : Continuous (deriv F) := han.deriv.continuous
  fun_prop


/-- The fourth power of the norm of a circle average is at most the circle
average of the fourth power.  This is Jensen's inequality in the exact form
needed after Cauchy's derivative formula. -/
theorem norm_circleAverage_pow_four_le {F : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hF : ContinuousOn F (Metric.sphere c |R|)) :
    ‖Real.circleAverage F c R‖ ^ 4 ≤
      Real.circleAverage (fun z => ‖F z‖ ^ 4) c R := by
  have : IsFiniteMeasure (volume.restrict (Set.uIoc 0 (2 * Real.pi))) := by
    rw [Set.uIoc_of_le (by positivity)]; infer_instance
  have : NeZero (volume (Set.uIoc 0 (2 * Real.pi))) := ⟨by simp⟩
  let h : ℝ → ℂ := fun θ => F (circleMap c R θ)
  have hhcont : ContinuousOn h (Set.Icc 0 (2 * Real.pi)) := by
    exact hF.comp (continuous_circleMap c R).continuousOn
      (fun θ _ => circleMap_mem_sphere' c R θ)
  have hhInt : IntervalIntegrable h volume 0 (2 * Real.pi) :=
    hhcont.intervalIntegrable_of_Icc (by positivity)
  have hnormInt : IntervalIntegrable (fun θ => ‖h θ‖) volume 0 (2 * Real.pi) :=
    hhcont.norm.intervalIntegrable_of_Icc (by positivity)
  have hpowInt : IntervalIntegrable (fun θ => ‖h θ‖ ^ 4) volume 0 (2 * Real.pi) :=
    (hhcont.norm.pow 4).intervalIntegrable_of_Icc (by positivity)
  have htriangle : ‖∫ θ in 0..2 * Real.pi, h θ‖ ≤
      ∫ θ in 0..2 * Real.pi, ‖h θ‖ :=
    intervalIntegral.norm_integral_le_integral_norm (by positivity)
  have hjensen :
      (⨍ θ in 0..2 * Real.pi, ‖h θ‖) ^ 4 ≤
        ⨍ θ in 0..2 * Real.pi, ‖h θ‖ ^ 4 := by
    refine (convexOn_pow 4).map_average_le (continuousOn_pow 4)
      isClosed_Ici (by filter_upwards; simp) ?_ ?_
    · simpa [Set.uIoc_of_le (show 0 ≤ 2 * Real.pi by positivity)] using hnormInt.1
    · simpa [Function.comp_apply, Set.uIoc_of_le (show 0 ≤ 2 * Real.pi by positivity)] using hpowInt.1
  rw [Real.circleAverage_eq_intervalAverage, Real.circleAverage_eq_intervalAverage]
  have havgtriangle : ‖⨍ θ in 0..2 * Real.pi, h θ‖ ≤
      ⨍ θ in 0..2 * Real.pi, ‖h θ‖ := by
    rw [interval_average_eq, interval_average_eq]
    rw [norm_smul]
    simp only [Real.norm_eq_abs, sub_zero, abs_inv, abs_of_pos Real.two_pi_pos]
    exact mul_le_mul_of_nonneg_left htriangle (inv_nonneg.mpr Real.two_pi_pos.le)
  calc
    ‖⨍ θ in 0..2 * Real.pi, h θ‖ ^ 4 ≤
        (⨍ θ in 0..2 * Real.pi, ‖h θ‖) ^ 4 :=
      pow_le_pow_left₀ (norm_nonneg _) havgtriangle 4
    _ ≤ ⨍ θ in 0..2 * Real.pi, ‖h θ‖ ^ 4 := hjensen


/-- Cauchy's first-derivative formula rewritten as an ordinary circle average.
The phase-free kernel has norm exactly `R⁻¹` on the circle. -/
theorem cauchyDerivative_eq_circleAverage
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    Real.circleAverage (fun z => (z - c)⁻¹ * F z) c R = deriv F c := by
  rw [Real.circleAverage_eq_circleIntegral hR.ne']
  have hcauchy := (hF.differentiableOn).deriv_eq_smul_circleIntegral hR
      (c := c) (R := R)
  rw [show (fun z => (z - c)⁻¹ • ((z - c)⁻¹ * F z)) =
      (fun z => (1 / (z - c) ^ 2) • F z) by
        funext z
        simp only [smul_eq_mul, one_div]
        rw [← inv_pow]
        ring]
  rw [hcauchy]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- Local form of Cauchy's derivative formula; differentiability is required
only on the closed disk used by the circle integral. -/
theorem cauchyDerivative_eq_circleAverage_on
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R)) :
    Real.circleAverage (fun z => (z - c)⁻¹ * F z) c R = deriv F c := by
  rw [Real.circleAverage_eq_circleIntegral hR.ne']
  have hcauchy := hF.deriv_eq_smul_circleIntegral hR
  rw [show (fun z => (z - c)⁻¹ • ((z - c)⁻¹ * F z)) =
      (fun z => (1 / (z - c) ^ 2) • F z) by
        funext z
        simp only [smul_eq_mul, one_div]
        rw [← inv_pow]
        ring]
  rw [hcauchy]
  simp only [smul_eq_mul]
  field_simp [Real.pi_ne_zero]

/-- Local disk version of the phase-free `L⁴` Cauchy estimate. -/
theorem norm_deriv_pow_four_le_invRadius_circleAverage_on
    {F : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall c R)) :
    ‖deriv F c‖ ^ 4 ≤
      R⁻¹ ^ 4 * Real.circleAverage (fun z => ‖F z‖ ^ 4) c R := by
  have hcont : ContinuousOn (fun z => (z - c)⁻¹ * F z)
      (Metric.sphere c |R|) := by
    intro z hz
    have hzne : z - c ≠ 0 := by
      have hdist : dist z c = |R| := Metric.mem_sphere.mp hz
      have habspos : 0 < |R| := abs_pos.mpr hR.ne'
      intro heq
      have hzc : z = c := sub_eq_zero.mp heq
      subst z
      simp at hdist
      linarith
    have hzball : z ∈ Metric.closedBall c R := by
      rw [Metric.mem_closedBall, ← abs_of_pos hR]
      exact (Metric.mem_sphere.mp hz).le
    exact (((continuousAt_id.sub continuousAt_const).inv₀ hzne).continuousWithinAt.mul
      ((hF.continuousOn z hzball).mono (fun y hy => by
        rw [Metric.mem_closedBall, ← abs_of_pos hR]
        exact (Metric.mem_sphere.mp hy).le)))
  have hbase : ‖deriv F c‖ ^ 4 ≤
      Real.circleAverage (fun z => ‖(z - c)⁻¹ * F z‖ ^ 4) c R := by
    rw [← cauchyDerivative_eq_circleAverage_on hR hF]
    exact norm_circleAverage_pow_four_le hcont
  calc
    ‖deriv F c‖ ^ 4 ≤
        Real.circleAverage (fun z => ‖(z - c)⁻¹ * F z‖ ^ 4) c R := hbase
    _ = Real.circleAverage (fun z => R⁻¹ ^ 4 * ‖F z‖ ^ 4) c R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hnorm : ‖z - c‖ = R := by
        have hd : dist z c = |R| := Metric.mem_sphere.mp hz
        rw [dist_eq_norm, abs_of_pos hR] at hd
        exact hd
      change ‖(z - c)⁻¹ * F z‖ ^ 4 = R⁻¹ ^ 4 * ‖F z‖ ^ 4
      rw [norm_mul, norm_inv, hnorm, mul_pow]
    _ = R⁻¹ ^ 4 * Real.circleAverage (fun z => ‖F z‖ ^ 4) c R := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (𝕜 := ℝ) (E := ℝ)
          (a := R⁻¹ ^ 4) (f := fun z => ‖F z‖ ^ 4) (c := c) (R := R))

/-- Pointwise `L⁴` Cauchy inequality on a circle.  This is the exact
mean-value estimate needed before integrating in the ordinate. -/
theorem norm_deriv_pow_four_le_circleAverage
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    ‖deriv F c‖ ^ 4 ≤
      Real.circleAverage (fun z => ‖(z - c)⁻¹ * F z‖ ^ 4) c R := by
  have hcont : ContinuousOn (fun z => (z - c)⁻¹ * F z)
      (Metric.sphere c |R|) := by
    intro z hz
    have hzne : z - c ≠ 0 := by
      have hdist : dist z c = |R| := Metric.mem_sphere.mp hz
      have habspos : 0 < |R| := abs_pos.mpr hR.ne'
      intro heq
      have hzc : z = c := sub_eq_zero.mp heq
      subst z
      simp at hdist
      linarith
    exact (((continuousAt_id.sub continuousAt_const).inv₀ hzne).mul
      hF.continuous.continuousAt).continuousWithinAt
  rw [← cauchyDerivative_eq_circleAverage hF hR]
  exact norm_circleAverage_pow_four_le hcont


/-- The phase-free Cauchy kernel has the exact `R⁻⁴` cost after taking a
fourth power. -/
theorem norm_deriv_pow_four_le_invRadius_circleAverage
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {c : ℂ} {R : ℝ} (hR : 0 < R) :
    ‖deriv F c‖ ^ 4 ≤
      R⁻¹ ^ 4 * Real.circleAverage (fun z => ‖F z‖ ^ 4) c R := by
  have hbase := norm_deriv_pow_four_le_circleAverage hF (c := c) hR
  calc
    ‖deriv F c‖ ^ 4 ≤
        Real.circleAverage (fun z => ‖(z - c)⁻¹ * F z‖ ^ 4) c R := hbase
    _ = Real.circleAverage (fun z => R⁻¹ ^ 4 * ‖F z‖ ^ 4) c R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hnorm : ‖z - c‖ = R := by
        have hd : dist z c = |R| := Metric.mem_sphere.mp hz
        rw [dist_eq_norm, abs_of_pos hR] at hd
        exact hd
      change ‖(z - c)⁻¹ * F z‖ ^ 4 = R⁻¹ ^ 4 * ‖F z‖ ^ 4
      rw [norm_mul, norm_inv, hnorm, mul_pow]
    _ = R⁻¹ ^ 4 * Real.circleAverage (fun z => ‖F z‖ ^ 4) c R := by
      simpa only [smul_eq_mul] using
        (Real.circleAverage_fun_smul (𝕜 := ℝ) (E := ℝ)
          (a := R⁻¹ ^ 4) (f := fun z => ‖F z‖ ^ 4) (c := c) (R := R))

/-- Squaring a complex differentiable trace produces the derivative used by
fourth-moment Sobolev sampling. -/
theorem hasDerivAt_sq
    {f f' : ℝ → ℂ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (fun t => f t ^ 2) (2 * f x * f' x) x := by
  convert (hf x).pow 2 using 1 <;> ring

/-- A one-separated discrete fourth moment on `[0,T]` is controlled by the
continuous fourth moment and the exact derivative-energy term.  This is the
one-dimensional part of the holomorphic/submean bridge and has no analytic
number-theory assumptions. -/
theorem sum_norm_fourth_le_collar_energy
    {T : ℝ} {W : Finset ℝ} {f f' : ℝ → ℂ}
    (hT : 0 ≤ T) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, 0 ≤ t ∧ t ≤ T) :
    (∑ t ∈ W, ‖f t‖ ^ 4) ≤
      2 * (∫ x in (0 : ℝ)..T + 1, ‖f x‖ ^ 4) +
        4 * ∫ x in (0 : ℝ)..T + 1, ‖f x‖ ^ 2 * ‖f' x‖ ^ 2 := by
  let F : ℝ → ℂ := fun t => f t ^ 2
  let F' : ℝ → ℂ := fun t => 2 * f t * f' t
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hFderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    simpa [F, F'] using hasDerivAt_sq hf x
  have hF'cont : Continuous F' := by
    dsimp [F']
    fun_prop
  have hs := RecenteredSampling.sum_norm_sq_le_collar_energy
    hT hFderiv hF'cont hsep hheight
  norm_num [F, F', norm_pow, norm_mul, pow_two] at hs ⊢
  convert hs using 1 <;> try ring
  congr 1
  rw [← intervalIntegral.integral_mul_const]

/-- Packed unit intervals based at ordinates in `[A,B]` stay inside the single
collar `(A,B+1]`. -/
theorem iUnion_Ioc_unit_subset_interval
    {A B : ℝ} {W : Finset ℝ}
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B) :
    (⋃ t ∈ W, Set.Ioc t (t + 1)) ⊆ Set.Ioc A (B + 1) := by
  intro x hx
  simp only [Set.mem_iUnion, Finset.mem_coe] at hx
  rcases hx with ⟨t, ht, hxt⟩
  exact ⟨lt_of_le_of_lt (hheight t ht).1 hxt.1,
    by linarith [(hheight t ht).2, hxt.2]⟩

/-- Integrals over the packed right unit intervals of a one-separated set in
`[A,B]` are bounded by the integral over the global one-unit collar. -/
theorem sum_unit_interval_integral_le_interval_collar
    {A B : ℝ} {W : Finset ℝ} {g : ℝ → ℝ}
    (hAB : A ≤ B) (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x)
    (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ W, ∫ x in t..t + 1, g x) ≤
      ∫ x in A..B + 1, g x := by
  have hpair := RecenteredSampling.pairwiseDisjoint_Ioc_unit hsep
  have hlocal : ∀ t ∈ W, IntegrableOn g (Set.Ioc t (t + 1)) volume := by
    intro t ht
    exact (hg.intervalIntegrable t (t + 1)).1
  have hunion := integral_biUnion_finset W
    (fun _t _ht => measurableSet_Ioc) hpair hlocal
  have hglobalInt : IntegrableOn g (Set.Ioc A (B + 1)) volume :=
    (hg.intervalIntegrable A (B + 1)).1
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc A (B + 1))] g := by
    filter_upwards with x
    exact hg0 x
  have hmono :
      (∫ x in ⋃ t ∈ W, Set.Ioc t (t + 1), g x) ≤
        ∫ x in Set.Ioc A (B + 1), g x := by
    exact setIntegral_mono_set hglobalInt hnonneg
      (iUnion_Ioc_unit_subset_interval hheight).eventuallyLE
  rw [hunion] at hmono
  calc
    (∑ t ∈ W, ∫ x in t..t + 1, g x) =
        ∑ t ∈ W, ∫ x in Set.Ioc t (t + 1), g x := by
      apply Finset.sum_congr rfl
      intro t ht
      exact intervalIntegral.integral_of_le (by linarith)
    _ ≤ ∫ x in Set.Ioc A (B + 1), g x := hmono
    _ = ∫ x in A..B + 1, g x :=
      (intervalIntegral.integral_of_le (by linarith)).symm

/-- Two-sided form of the exact fourth-moment Sobolev sampler. -/
theorem sum_norm_fourth_le_interval_collar_energy
    {A B : ℝ} {W : Finset ℝ} {f f' : ℝ → ℂ}
    (hAB : A ≤ B) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ W, ‖f t‖ ^ 4) ≤
      2 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
        4 * ∫ x in A..B + 1, ‖f x‖ ^ 2 * ‖f' x‖ ^ 2 := by
  let F : ℝ → ℂ := fun t => f t ^ 2
  let F' : ℝ → ℂ := fun t => 2 * f t * f' t
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hFderiv : ∀ x, HasDerivAt F (F' x) x := by
    intro x
    simpa [F, F'] using hasDerivAt_sq hf x
  have hF'cont : Continuous F' := by
    dsimp [F']
    fun_prop
  have hlocal : ∀ t ∈ W, ‖F t‖ ^ 2 ≤
      2 * (∫ x in t..t + 1, ‖F x‖ ^ 2) +
        ∫ x in t..t + 1, ‖F' x‖ ^ 2 := by
    intro t ht
    exact RecenteredSampling.norm_sq_le_unit_interval_energy hFderiv hF'cont t
  have hs : (∑ t ∈ W, ‖F t‖ ^ 2) ≤
      2 * (∫ x in A..B + 1, ‖F x‖ ^ 2) +
        ∫ x in A..B + 1, ‖F' x‖ ^ 2 := by
    calc
      (∑ t ∈ W, ‖F t‖ ^ 2) ≤
          ∑ t ∈ W, (2 * (∫ x in t..t + 1, ‖F x‖ ^ 2) +
            ∫ x in t..t + 1, ‖F' x‖ ^ 2) := by
        exact Finset.sum_le_sum fun t ht => hlocal t ht
      _ = 2 * (∑ t ∈ W, ∫ x in t..t + 1, ‖F x‖ ^ 2) +
          ∑ t ∈ W, ∫ x in t..t + 1, ‖F' x‖ ^ 2 := by
        rw [Finset.mul_sum]
        simp only [Finset.sum_add_distrib]
      _ ≤ 2 * (∫ x in A..B + 1, ‖F x‖ ^ 2) +
          ∫ x in A..B + 1, ‖F' x‖ ^ 2 := by
        gcongr
        · exact sum_unit_interval_integral_le_interval_collar hAB
            ((hfcont.pow 2).norm.pow 2) (fun _ => sq_nonneg _)
            hsep hheight
        · exact sum_unit_interval_integral_le_interval_collar hAB
            (hF'cont.norm.pow 2) (fun _ => sq_nonneg _)
            hsep hheight
  norm_num [F, F', norm_pow, norm_mul, pow_two] at hs ⊢
  convert hs using 1 <;> try ring
  congr 1
  rw [← intervalIntegral.integral_mul_const]

/-- Elementary absorption of the mixed derivative energy into fourth powers.
It is deliberately pointwise, avoiding any hidden Holder or integrability
premise. -/
theorem four_mul_norm_sq_mul_norm_sq_le
    (z w : ℂ) :
    4 * ‖z‖ ^ 2 * ‖w‖ ^ 2 ≤ 2 * ‖z‖ ^ 4 + 2 * ‖w‖ ^ 4 := by
  nlinarith [sq_nonneg (‖z‖ ^ 2 - ‖w‖ ^ 2)]

/-- The mixed derivative energy in the Sobolev sampler can be absorbed into
ordinary fourth moments of the trace and its derivative. -/
theorem sum_norm_fourth_le_interval_collar_fourth_deriv
    {A B : ℝ} {W : Finset ℝ} {f f' : ℝ → ℂ}
    (hAB : A ≤ B) (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : Continuous f') (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ W, ‖f t‖ ^ 4) ≤
      4 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
        2 * ∫ x in A..B + 1, ‖f' x‖ ^ 4 := by
  have hfcont : Continuous f :=
    continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hleftCont : Continuous (fun x => 4 * ‖f x‖ ^ 2 * ‖f' x‖ ^ 2) := by
    fun_prop
  have hrightCont : Continuous (fun x => 2 * ‖f x‖ ^ 4 + 2 * ‖f' x‖ ^ 4) := by
    fun_prop
  have hmixedInt :
      (∫ x in A..B + 1, 4 * ‖f x‖ ^ 2 * ‖f' x‖ ^ 2) ≤
        ∫ x in A..B + 1, (2 * ‖f x‖ ^ 4 + 2 * ‖f' x‖ ^ 4) := by
    exact intervalIntegral.integral_mono_on (by linarith)
      (hleftCont.intervalIntegrable _ _) (hrightCont.intervalIntegrable _ _)
      (fun x _ => four_mul_norm_sq_mul_norm_sq_le (f x) (f' x))
  have hsample := sum_norm_fourth_le_interval_collar_energy
    hAB hf hf' hsep hheight
  calc
    (∑ t ∈ W, ‖f t‖ ^ 4) ≤
        2 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
          4 * ∫ x in A..B + 1, ‖f x‖ ^ 2 * ‖f' x‖ ^ 2 := hsample
    _ = 2 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
        ∫ x in A..B + 1, 4 * ‖f x‖ ^ 2 * ‖f' x‖ ^ 2 := by
      congr 1
      convert (intervalIntegral.integral_const_mul
        (a := A) (b := B + 1) (4 : ℝ)
        (fun x => ‖f x‖ ^ 2 * ‖f' x‖ ^ 2)).symm using 1 <;> ring
    _ ≤ 2 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
        ∫ x in A..B + 1, (2 * ‖f x‖ ^ 4 + 2 * ‖f' x‖ ^ 4) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hmixedInt (2 * (∫ x in A..B + 1, ‖f x‖ ^ 4))
    _ = 4 * (∫ x in A..B + 1, ‖f x‖ ^ 4) +
        2 * ∫ x in A..B + 1, ‖f' x‖ ^ 4 := by
      have hfi : IntervalIntegrable (fun x => 2 * ‖f x‖ ^ 4) volume A (B + 1) :=
        ((hfcont.norm.pow 4).const_mul 2).intervalIntegrable _ _
      have hgi : IntervalIntegrable (fun x => 2 * ‖f' x‖ ^ 4) volume A (B + 1) :=
        ((hf'.norm.pow 4).const_mul 2).intervalIntegrable _ _
      rw [intervalIntegral.integral_add hfi hgi,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring


/-- Fubini for two compact real intervals, packaged in the exact orientation
needed to integrate the circle Cauchy estimate in the ordinate. -/
theorem continuous_intervalIntegral_swap
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g))
    {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D) :
    (∫ t in A..B, ∫ theta in C..D, g t theta) =
      ∫ theta in C..D, ∫ t in A..B, g t theta := by
  have hcompact : IsCompact (Set.Icc A B ×ˢ Set.Icc C D) :=
    isCompact_Icc.prod isCompact_Icc
  have hIntClosed : IntegrableOn (Function.uncurry g)
      (Set.Icc A B ×ˢ Set.Icc C D) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact hcompact hg.continuousOn
  have hsubset : Set.Ioc A B ×ˢ Set.Ioc C D ⊆
      Set.Icc A B ×ˢ Set.Icc C D :=
    Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hIntOpen : IntegrableOn (Function.uncurry g)
      (Set.Ioc A B ×ˢ Set.Ioc C D) (volume.prod volume) :=
    hIntClosed.mono_set hsubset
  have hprod : Integrable (Function.uncurry g)
      ((volume.restrict (Set.Ioc A B)).prod
        (volume.restrict (Set.Ioc C D))) := by
    rw [Measure.prod_restrict]
    exact hIntOpen
  simp_rw [intervalIntegral.integral_of_le hAB,
    intervalIntegral.integral_of_le hCD]
  exact integral_integral_swap hprod

/-- Direct two-sided sampler for the vertical trace of an entire function.
The remaining continuous derivative integral is exactly the quantity controlled
by the circle Cauchy estimate above. -/
theorem sum_verticalTrace_fourth_le_continuous_and_deriv
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {sigma A B : ℝ} {W : Finset ℝ}
    (hAB : A ≤ B) (hsep : OneSeparated W)
    (hheight : ∀ t ∈ W, A ≤ t ∧ t ≤ B) :
    (∑ t ∈ W, ‖F ((sigma : ℂ) + t * Complex.I)‖ ^ 4) ≤
      4 * (∫ t in A..B + 1,
        ‖F ((sigma : ℂ) + t * Complex.I)‖ ^ 4) +
      2 * ∫ t in A..B + 1,
        ‖deriv F ((sigma : ℂ) + t * Complex.I)‖ ^ 4 := by
  let f : ℝ → ℂ := fun t => F ((sigma : ℂ) + t * Complex.I)
  let f' : ℝ → ℂ := fun t =>
    deriv F ((sigma : ℂ) + t * Complex.I) * Complex.I
  have hs := sum_norm_fourth_le_interval_collar_fourth_deriv
    hAB (fun t => hasDerivAt_verticalTrace hF sigma t)
    (continuous_verticalDerivTrace hF sigma) hsep hheight
  simpa only [f, f', norm_mul, Complex.norm_I, mul_one] using hs

end
end HolomorphicSubmeanSampling

#print axioms HolomorphicSubmeanSampling.hasDerivAt_verticalTrace
#print axioms HolomorphicSubmeanSampling.continuous_verticalDerivTrace
#print axioms HolomorphicSubmeanSampling.norm_circleAverage_pow_four_le
#print axioms HolomorphicSubmeanSampling.cauchyDerivative_eq_circleAverage
#print axioms HolomorphicSubmeanSampling.cauchyDerivative_eq_circleAverage_on
#print axioms HolomorphicSubmeanSampling.norm_deriv_pow_four_le_invRadius_circleAverage_on
#print axioms HolomorphicSubmeanSampling.norm_deriv_pow_four_le_circleAverage
#print axioms HolomorphicSubmeanSampling.norm_deriv_pow_four_le_invRadius_circleAverage
#print axioms HolomorphicSubmeanSampling.hasDerivAt_sq
#print axioms HolomorphicSubmeanSampling.sum_norm_fourth_le_collar_energy
#print axioms HolomorphicSubmeanSampling.four_mul_norm_sq_mul_norm_sq_le
#print axioms HolomorphicSubmeanSampling.sum_norm_fourth_le_interval_collar_fourth_deriv
#print axioms HolomorphicSubmeanSampling.continuous_intervalIntegral_swap
#print axioms HolomorphicSubmeanSampling.sum_verticalTrace_fourth_le_continuous_and_deriv
