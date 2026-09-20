import GuthMaynardJIterationSigmaIIPoissonSupport

open scoped BigOperators Real FourierTransform ComplexConjugate ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Measurability and integrability of the Lemma 9.2 Poisson pieces

The published argument splits the already integrable finite pair kernel into a
retained second-Poisson part and a rapidly decaying tail.  The tail estimate was
previously available only at the level of its integral.  This file proves the
measurability needed to apply the pointwise majorant, then recovers retained
integrability by subtraction from the exact finite kernel.
-/

/-- The first Poisson factor is continuous in the two profile variables. -/
theorem continuous_sigmaIIZ1_pair
    (M3 Ctau m2 m2' : ℝ) :
    Continuous (fun z : ℝ × ℝ =>
      sigmaIIZ1 M3 Ctau m2 m2' z.1 z.2) := by
  unfold sigmaIIZ1
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry sourcePhase
  fun_prop

/-- Each hard-cutoff tail summand is Borel measurable in an arbitrary
continuous shift. -/
theorem measurable_schwartzIntegerTail_comp
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (F : ℝ → ℂ) (hF : Continuous F) (A B : ℝ)
    (y : X → ℝ) (hy : Continuous y) (j : ℤ) :
    Measurable (fun x => schwartzIntegerTail F A B (y x) j) := by
  unfold schwartzIntegerTail
  have harg : Continuous (fun x : X => (((j : ℝ) - y x) / A)) := by
    fun_prop
  exact Measurable.ite
    (measurableSet_le measurable_const harg.abs.measurable)
    (hF.measurable.comp harg.measurable) measurable_const

/-- The complete tail series is strongly measurable after a continuous
change of the Poisson shift.  Absolute convergence is not needed for this
measurability statement. -/
theorem aestronglyMeasurable_sourceSecondPoissonTail_comp
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X]
    (F : ℝ → ℂ) (hF : Continuous F) (M2 T B : ℝ)
    (y : X → ℝ) (hy : Continuous y) (μ : Measure X) :
    AEStronglyMeasurable (fun x =>
      sourceSecondPoissonTail F M2 T B (y x)) μ := by
  unfold sourceSecondPoissonTail
  have htsum : AEStronglyMeasurable (fun x =>
      ∑' j : ℤ, schwartzIntegerTail F (M2 / T) B (y x) j) μ :=
    AEStronglyMeasurable.tsum
      (L := SummationFilter.unconditional ℤ) (μ := μ) fun j =>
      (measurable_schwartzIntegerTail_comp
        F hF (M2 / T) B y hy j).aestronglyMeasurable
  exact htsum.const_smul (T / M2 : ℝ)

/-- The literal second-Poisson tail pair kernel is strongly measurable. -/
theorem aestronglyMeasurable_sigmaIIZPairTailKernel
    (psi2 f : ℝ → ℝ)
    (hpsi2compact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (hfmeas : AEStronglyMeasurable f)
    (M2 T M3 Ctau B : ℝ) (m2 m2' : ℤ) :
    AEStronglyMeasurable
      (sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2')
      (volume.prod volume) := by
  have hpsi2int : Integrable (fun x : ℝ => (psi2 x : ℂ)) :=
    hpsi2smooth.continuous.integrable_of_hasCompactSupport hpsi2compact
  have hF : Continuous
      (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ))) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hpsi2int
  have hy : Continuous (fun z : ℝ × ℝ =>
      (m2' : ℝ) * z.2 - (m2 : ℝ) * z.1) := by fun_prop
  have htail := aestronglyMeasurable_sourceSecondPoissonTail_comp
    (FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ))) hF
      M2 T B _ hy (volume.prod volume)
  have hpair : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      ((f z.1 * f z.2 : ℝ) : ℂ)) (volume.prod volume) := by
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      ((hfmeas.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).mul
        (hfmeas.comp_quasiMeasurePreserving
          Measure.quasiMeasurePreserving_snd))
  have hfirst : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2)
      (volume.prod volume) :=
    (continuous_sigmaIIZ1_pair M3 Ctau
      (m2 : ℝ) (m2' : ℝ)).aestronglyMeasurable
  simpa only [sigmaIIZPairTailKernel] using hpair.mul (hfirst.mul htail)

/-- The pointwise `T^-100` tail majorant is a genuine integrability theorem,
not merely an estimate for an integral whose integrand might be nonmeasurable. -/
theorem integrable_sigmaIIZPairTailKernel_of_budget
    (psi2 f : ℝ → ℝ) (hf : Integrable f)
    (hpsi2compact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) {K M2 T B Y C M3 Ctau : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y) (hCtau : 0 ≤ Ctau)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m2 m2' : ℤ)
    (hy : ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
      |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y) :
    Integrable (sigmaIIZPairTailKernel psi2 f
      M2 T M3 Ctau B m2 m2') (volume.prod volume) := by
  let D : ℝ := (2 * Ctau) * (C / T ^ 100)
  let g : ℝ × ℝ → ℝ := fun z => |f z.1| * |f z.2| * D
  have hg : Integrable g (volume.prod volume) := by
    exact (hf.norm.mul_prod hf.norm).mul_const D
  apply hg.mono'
    (aestronglyMeasurable_sigmaIIZPairTailKernel psi2 f
      hpsi2compact hpsi2smooth hf.aestronglyMeasurable
      M2 T M3 Ctau B m2 m2')
  filter_upwards with z
  by_cases hz : f z.1 * f z.2 = 0
  · unfold sigmaIIZPairTailKernel g
    rw [hz]
    rw [← abs_mul, hz]
    simp
  · have h := norm_sigmaIIZPairTailKernel_le_time_neg100
      (M3 := M3) psi2 f q hK hM2 hT hB hY hCtau hdecay hbudget
        m2 m2' z (hy z hz)
    simpa only [g, D, abs_mul, mul_assoc] using h

/-- Retained integrability follows from the exact full = retained + tail split.
Thus no separate analytic premise is needed for either Poisson piece. -/
theorem integrable_sigmaIIZPairRetainedKernel_of_budget
    (ellRange : Finset ℤ) (psi2 f : ℝ → ℝ) (hf : Integrable f)
    (hpsi2compact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) {K0 K M2 T B Y C M3 Ctau : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hB : 0 < B) (hY : 0 ≤ Y) (hM3 : M3 ≠ 0)
    (hCtau : 0 ≤ Ctau)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K / (1 + |xi|) ^ (q + 2))
    (hbudget :
      (T / M2) * K *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (m2 m2' : ℤ)
    (hy : ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
      |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0) :
    Integrable (sigmaIIZPairRetainedKernel psi2 f
      M2 T M3 Ctau B m2 m2') (volume.prod volume) := by
  have hfull := integrable_sigmaIIZPairKernel f hf ellRange psi2
    hM3 hCtau M2 T m2 m2'
  have htail := integrable_sigmaIIZPairTailKernel_of_budget
    (M3 := M3) psi2 f hf hpsi2compact hpsi2smooth q hK hM2 hT hB hY hCtau
      hdecay hbudget m2 m2' hy
  have hdiff := hfull.sub htail
  apply hdiff.congr
  filter_upwards with z
  have hsplit := sigmaIIZPairKernel_eq_retained_add_tail
    ellRange psi2 f hpsi2compact hpsi2smooth hM2 hT hdecay2
      M3 Ctau B m2 m2' z hsupport
  change sigmaIIZPairKernel ellRange psi2 f M2 T M3 Ctau m2 m2' z -
      sigmaIIZPairTailKernel psi2 f M2 T M3 Ctau B m2 m2' z = _
  rw [hsplit]
  ring

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.continuous_sigmaIIZ1_pair
#print axioms GuthMaynardJIteration.measurable_schwartzIntegerTail_comp
#print axioms GuthMaynardJIteration.aestronglyMeasurable_sourceSecondPoissonTail_comp
#print axioms GuthMaynardJIteration.aestronglyMeasurable_sigmaIIZPairTailKernel
#print axioms GuthMaynardJIteration.integrable_sigmaIIZPairTailKernel_of_budget
#print axioms GuthMaynardJIteration.integrable_sigmaIIZPairRetainedKernel_of_budget
