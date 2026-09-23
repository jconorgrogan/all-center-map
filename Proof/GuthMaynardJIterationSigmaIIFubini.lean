import GuthMaynardJIterationSigmaIIFourier

open scoped BigOperators Real FourierTransform ComplexConjugate
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def sigmaIITripleKernel (f : ℝ → ℝ) (M3 : ℝ)
    (ell m2 m2' : ℤ) (tau : ℝ) (z : ℝ × ℝ) : ℂ :=
  fourierPairKernel f
    (sigmaIIAffineFrequency M3 ell m2 tau)
    (sigmaIIAffineFrequency M3 ell m2' tau) z.1 z.2

/-- The missing product-space majorant for TeX 1611.  On the bounded
`tau` interval the phase has norm one, so `Integrable f` gives the full
triple integrability needed by Fubini. -/
theorem integrable_sigmaIITripleKernel
    (f : ℝ → ℝ) (hf : Integrable f)
    (M3 Ctau : ℝ) (ell m2 m2' : ℤ) :
    Integrable (Function.uncurry
      (fun tau (z : ℝ × ℝ) => sigmaIITripleKernel f M3 ell m2 m2' tau z))
      ((volume.restrict (Set.uIoc (-Ctau) Ctau)).prod
        (volume.prod volume)) := by
  have hpair : Integrable
      (fun z : ℝ × ℝ => (f z.1 : ℂ) * (f z.2 : ℂ))
      (volume.prod volume) := hf.ofReal.mul_prod hf.ofReal
  have htime : Integrable (fun _ : ℝ => (1 : ℂ))
      (volume.restrict (Set.uIoc (-Ctau) Ctau)) := by
    change IntegrableOn (fun _ : ℝ => (1 : ℂ))
      (Set.uIoc (-Ctau) Ctau)
    exact continuous_const.integrableOn_uIoc
  have hcoef : Integrable
      (fun p : ℝ × (ℝ × ℝ) => (f p.2.1 : ℂ) * (f p.2.2 : ℂ))
      ((volume.restrict (Set.uIoc (-Ctau) Ctau)).prod
        (volume.prod volume)) := by
    simpa using htime.mul_prod hpair
  refine Integrable.mono' hcoef.norm ?_ ?_
  · have hphase : Continuous
        (fun p : ℝ × (ℝ × ℝ) =>
          sourcePhase
            (sigmaIIAffineFrequency M3 ell m2' p.1 * p.2.2 -
              sigmaIIAffineFrequency M3 ell m2 p.1 * p.2.1)) := by
        unfold sigmaIIAffineFrequency sourcePhase
        fun_prop
    simpa [Function.uncurry, sigmaIITripleKernel, fourierPairKernel] using!
      hcoef.aestronglyMeasurable.mul hphase.aestronglyMeasurable
  · filter_upwards with p
    rcases p with ⟨tau, u, u'⟩
    change ‖((f u * f u' : ℝ) : ℂ) *
      sourcePhase
        (sigmaIIAffineFrequency M3 ell m2' tau * u' -
          sigmaIIAffineFrequency M3 ell m2 tau * u)‖ ≤
      ‖(f u : ℂ) * (f u' : ℂ)‖
    rw [norm_mul, norm_sourcePhase, mul_one]
    push_cast
    exact le_rfl

/-- Fubini interchange for the exact corrected affine frequencies.  The
right side is deliberately a product-space integral, avoiding any hidden
second interchange. -/
theorem intervalIntegral_iterated_sigmaIIKernel_eq_prod
    (f : ℝ → ℝ) (hf : Integrable f)
    (M3 Ctau : ℝ) (ell m2 m2' : ℤ) :
    (∫ tau in -Ctau..Ctau,
      ∫ u : ℝ, ∫ u' : ℝ,
        sigmaIITripleKernel f M3 ell m2 m2' tau (u, u')) =
      ∫ z : ℝ × ℝ,
        ∫ tau in -Ctau..Ctau,
          sigmaIITripleKernel f M3 ell m2 m2' tau z := by
  let K : ℝ → (ℝ × ℝ) → ℂ :=
    fun tau z => sigmaIITripleKernel f M3 ell m2 m2' tau z
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Set.uIoc (-Ctau) Ctau)).prod
        (volume.prod volume)) :=
    integrable_sigmaIITripleKernel f hf M3 Ctau ell m2 m2'
  calc
    (∫ tau in -Ctau..Ctau,
      ∫ u : ℝ, ∫ u' : ℝ, K tau (u, u')) =
        ∫ tau in -Ctau..Ctau, ∫ z : ℝ × ℝ, K tau z := by
      apply intervalIntegral.integral_congr_ae_restrict
      filter_upwards [hK.prod_right_ae] with tau htau
      exact integral_integral htau
    _ = ∫ z : ℝ × ℝ, ∫ tau in -Ctau..Ctau, K tau z :=
      intervalIntegral_integral_swap hK
    _ = _ := by rfl

theorem integrable_intervalIntegral_sigmaIITripleKernel
    (f : ℝ → ℝ) (hf : Integrable f)
    (M3 : ℝ) {Ctau : ℝ} (hCtau : 0 ≤ Ctau)
    (ell m2 m2' : ℤ) :
    Integrable (fun z : ℝ × ℝ =>
      ∫ tau in -Ctau..Ctau,
        sigmaIITripleKernel f M3 ell m2 m2' tau z)
      (volume.prod volume) := by
  let K : ℝ → (ℝ × ℝ) → ℂ :=
    fun tau z => sigmaIITripleKernel f M3 ell m2 m2' tau z
  have hK : Integrable (Function.uncurry K)
      ((volume.restrict (Set.uIoc (-Ctau) Ctau)).prod
        (volume.prod volume)) :=
    integrable_sigmaIITripleKernel f hf M3 Ctau ell m2 m2'
  have hright := hK.integral_prod_right
  have horder : -Ctau ≤ Ctau := by linarith
  simpa only [intervalIntegral.integral_of_le horder,
    Set.uIoc_of_le horder, K] using! hright

/-- A single affine Fourier pair can now be integrated in `tau` and moved
to the product `u,u'` space with no assumed Fubini equality. -/
theorem intervalIntegral_affine_fourierPair_eq_prod
    (f : ℝ → ℝ) (hf : Integrable f)
    (M3 Ctau : ℝ) (ell m2 m2' : ℤ) :
    (∫ tau in -Ctau..Ctau,
      FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau) *
        conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2' tau))) =
      ∫ z : ℝ × ℝ,
        ∫ tau in -Ctau..Ctau,
          sigmaIITripleKernel f M3 ell m2 m2' tau z := by
  calc
    (∫ tau in -Ctau..Ctau,
      FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2 tau) *
        conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
          (sigmaIIAffineFrequency M3 ell m2' tau))) =
      ∫ tau in -Ctau..Ctau,
        ∫ u : ℝ, ∫ u' : ℝ,
          sigmaIITripleKernel f M3 ell m2 m2' tau (u, u') := by
      apply intervalIntegral.integral_congr
      intro tau htau
      exact fourier_mul_conj_eq_iteratedIntegral f
        (sigmaIIAffineFrequency M3 ell m2 tau)
        (sigmaIIAffineFrequency M3 ell m2' tau)
    _ = _ := intervalIntegral_iterated_sigmaIIKernel_eq_prod
      f hf M3 Ctau ell m2 m2'

/-- Full finite `ell` Fourier-pair sum after the proved Fubini interchange,
factored exactly into the corrected `Z1*Z2` kernel. -/
theorem finite_affine_fourierPair_eq_integral_Z1_Z2
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) (m2 m2' : ℤ) :
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        ∫ tau in -Ctau..Ctau,
          FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
              (sigmaIIAffineFrequency M3 ell m2 tau) *
            conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
              (sigmaIIAffineFrequency M3 ell m2' tau))) =
      ∫ z : ℝ × ℝ,
        ((f z.1 * f z.2 : ℝ) : ℂ) *
          (sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2 *
            sigmaIIZ2Finite ellRange psi2 M2 T
              (m2 : ℝ) (m2' : ℝ) z.1 z.2) := by
  let w : ℤ → ℂ := fun ell => (psi2 (M2 * (ell : ℝ) / T) : ℂ)
  let K : ℤ → (ℝ × ℝ) → ℂ := fun ell z =>
    ∫ tau in -Ctau..Ctau,
      sigmaIITripleKernel f M3 ell m2 m2' tau z
  have hK : ∀ ell ∈ ellRange, Integrable (fun z => w ell * K ell z)
      (volume.prod volume) := by
    intro ell hell
    exact (integrable_intervalIntegral_sigmaIITripleKernel
      f hf M3 hCtau ell m2 m2').const_mul (w ell)
  calc
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        ∫ tau in -Ctau..Ctau,
          FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
              (sigmaIIAffineFrequency M3 ell m2 tau) *
            conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
              (sigmaIIAffineFrequency M3 ell m2' tau))) =
      ∑ ell ∈ ellRange, ∫ z : ℝ × ℝ, w ell * K ell z := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [intervalIntegral_affine_fourierPair_eq_prod f hf]
        rw [integral_const_mul]
    _ = ∫ z : ℝ × ℝ, ∑ ell ∈ ellRange, w ell * K ell z := by
      exact (integral_finsetSum ellRange hK).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [w, K]
      simp only [sigmaIITripleKernel, fourierPairKernel]
      simp_rw [intervalIntegral.integral_const_mul]
      calc
        (∑ ell ∈ ellRange,
          (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
            (((f z.1 * f z.2 : ℝ) : ℂ) *
              ∫ tau in -Ctau..Ctau,
                sourcePhase
                  (sigmaIIAffineFrequency M3 ell m2' tau * z.2 -
                    sigmaIIAffineFrequency M3 ell m2 tau * z.1))) =
          ((f z.1 * f z.2 : ℝ) : ℂ) *
            ∑ ell ∈ ellRange,
              (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
                ∫ tau in -Ctau..Ctau,
                  sourcePhase
                    (sigmaIIAffineFrequency M3 ell m2' tau * z.2 -
                      sigmaIIAffineFrequency M3 ell m2 tau * z.1) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro ell hell
            ring
        _ = _ := by
          rw [sigmaII_phase_sum_integral_eq_Z1_mul_Z2
            ellRange psi2 hM3 M2 T Ctau m2 m2' z.1 z.2]

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.integrable_sigmaIITripleKernel
#print axioms GuthMaynardJIteration.intervalIntegral_iterated_sigmaIIKernel_eq_prod
#print axioms GuthMaynardJIteration.integrable_intervalIntegral_sigmaIITripleKernel
#print axioms GuthMaynardJIteration.intervalIntegral_affine_fourierPair_eq_prod
#print axioms GuthMaynardJIteration.finite_affine_fourierPair_eq_integral_Z1_Z2
