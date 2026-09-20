import GuthMaynardJIterationSourceEllRestriction
import GuthMaynardJIterationMediumPairSmoothing

open scoped BigOperators Real FourierTransform ComplexConjugate ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-! The finite coefficient aggregation after the exact equation (9.11). -/

/-- The real part of the exact finite product formula is bounded by the sum of
the norms of its pair integrals.  This is the literal `m₂,m₂'` coefficient
assembly, before inserting retained/tail estimates. -/
theorem sigmaIIFinite_le_sum_norm_pairIntegrals
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) :
    sigmaIIFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ‖∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume‖ := by
  rw [sigmaIIFinite_eq_re_product f hf ellRange m2Range psi2
    hM3 hCtau M2 T]
  have hZ : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (fun z : ℝ × ℝ =>
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          sigmaIIZPairKernel ellRange psi2 f
            M2 T M3 Ctau m2 m2' z) (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact (integrable_sigmaIIZPairKernel f hf ellRange psi2
      hM3 hCtau M2 T m2 m2').const_mul _
  have hprod : sigmaIIProductComplexFinite ellRange m2Range psi2 f
        M2 T M3 Ctau =
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          (∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume) := by
    unfold sigmaIIProductComplexFinite
    change (∫ z : ℝ × ℝ,
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          sigmaIIZPairKernel ellRange psi2 f
            M2 T M3 Ctau m2 m2' z ∂volume.prod volume) = _
    rw [integral_finset_double_sum_complex
      (volume.prod volume) m2Range _ hZ]
    apply Finset.sum_congr rfl
    intro m2 hm2
    apply Finset.sum_congr rfl
    intro m2' hm2'
    rw [integral_const_mul]
  rw [hprod]
  calc
    (∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          (∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume)).re ≤
      ‖∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          (∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume)‖ := Complex.re_le_norm _
    _ ≤ ∑ m2 ∈ m2Range,
        ‖∑ m2' ∈ m2Range,
          (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
            (∫ z : ℝ × ℝ,
              sigmaIIZPairKernel ellRange psi2 f
                M2 T M3 Ctau m2 m2' z ∂volume.prod volume)‖ := norm_sum_le _ _
    _ ≤ ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        ‖(((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          (∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume)‖ := by
      apply Finset.sum_le_sum
      intro m2 hm2
      exact norm_sum_le _ _
    _ = ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ‖∫ z : ℝ × ℝ,
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z ∂volume.prod volume‖ := by
      apply Finset.sum_congr rfl
      intro m2 hm2
      apply Finset.sum_congr rfl
      intro m2' hm2'
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- Exact integration of the pointwise retained/full-Poisson split. -/
theorem integral_sigmaIIZPairKernel_eq_retained_add_tail
    (ellRange : Finset ℤ) (psi2 f : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    {K0 M2 T : ℝ} (hM2 : 0 < M2) (hT : 0 < T)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (M3 Ctau B : ℝ) (m2 m2' : ℤ)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0)
    (hret : Integrable (sigmaIIZPairRetainedKernel psi2 f
      M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (htail : Integrable (sigmaIIZPairTailKernel psi2 f
      M2 T M3 Ctau B m2 m2') (volume.prod volume)) :
    (∫ z : ℝ × ℝ,
        sigmaIIZPairKernel ellRange psi2 f
          M2 T M3 Ctau m2 m2' z ∂volume.prod volume) =
      (∫ z : ℝ × ℝ,
        sigmaIIZPairRetainedKernel psi2 f
          M2 T M3 Ctau B m2 m2' z ∂volume.prod volume) +
      ∫ z : ℝ × ℝ,
        sigmaIIZPairTailKernel psi2 f
          M2 T M3 Ctau B m2 m2' z ∂volume.prod volume := by
  calc
    (∫ z : ℝ × ℝ,
        sigmaIIZPairKernel ellRange psi2 f
          M2 T M3 Ctau m2 m2' z ∂volume.prod volume) =
      ∫ z : ℝ × ℝ,
        (sigmaIIZPairRetainedKernel psi2 f
          M2 T M3 Ctau B m2 m2' z +
        sigmaIIZPairTailKernel psi2 f
          M2 T M3 Ctau B m2 m2' z) ∂volume.prod volume := by
        apply integral_congr_ae
        filter_upwards with z
        exact sigmaIIZPairKernel_eq_retained_add_tail
          ellRange psi2 f hcompact hsmooth hM2 hT hdecay2
          M3 Ctau B m2 m2' z hsupport
    _ = _ := integral_add hret htail

/-- Insert the certified full/retained/tail split into every finite
`m₂,m₂'` pair.  The retained pair integrals remain literal; the discarded
second-Poisson contribution is uniformly `T⁻¹⁰⁰` with the exact `L¹(f)²`
mass and coefficient sum exposed. -/
theorem sigmaIIFinite_le_sum_retainedPairIntegral_add_time_neg100
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hsmooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
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
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0)
    (hy : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y)
    (hret : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (sigmaIIZPairRetainedKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (htail : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (sigmaIIZPairTailKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume)) :
    sigmaIIFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        |(m2 : ℝ) * (m2' : ℝ)| *
          (‖∫ z : ℝ × ℝ,
              sigmaIIZPairRetainedKernel psi2 f
                M2 T M3 Ctau B m2 m2' z ∂volume.prod volume‖ +
            (∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)) := by
  refine (sigmaIIFinite_le_sum_norm_pairIntegrals f hf ellRange m2Range
    psi2 hM3 hCtau M2 T).trans ?_
  apply Finset.sum_le_sum
  intro m2 hm2
  apply Finset.sum_le_sum
  intro m2' hm2'
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  rw [integral_sigmaIIZPairKernel_eq_retained_add_tail
    ellRange psi2 f hcompact hsmooth hM2 hT hdecay2 M3 Ctau B m2 m2'
    hsupport (hret m2 hm2 m2' hm2') (htail m2 hm2 m2' hm2')]
  refine (norm_add_le _ _).trans ?_
  gcongr
  simpa only [Measure.volume_eq_prod] using
    (norm_integral_sigmaIIZPairTailKernel_le_time_neg100
      psi2 f hf q hK hM2 hT hB hY hCtau hdecay hbudget m2 m2'
        (hy m2 hm2 m2' hm2'))

/-- The already-proved fiberwise retained-kernel smoothing estimate integrates
to the exact product-space pair bound needed in (9.11).  The only extra
requirements are the natural product integrability and integrability of the
displayed affine-smoothing majorant. -/
theorem norm_integral_sigmaIIZPairRetainedKernel_le_smoothingIntegral
    (psi2 psi f : ℝ → ℝ) {K M2 T M3 Ctau B Y : ℝ}
    (hK : 0 ≤ K) (hM2 : 0 < M2) (hT : 0 < T)
    (hCtau : 0 ≤ Ctau) (hB : 0 ≤ B) (hY : 0 ≤ Y)
    (hf : Integrable f) (hf0 : ∀ v, 0 ≤ f v)
    (hpsi0 : ∀ z, 0 ≤ psi z)
    (hF : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ K)
    (m2 m2' : ℤ) (hm2' : 0 < (m2' : ℝ))
    (hy : ∀ u u', f u * f u' ≠ 0 →
      |(m2' : ℝ) * u' - (m2 : ℝ) * u| ≤ Y)
    (hpsi_major : ∀ z, |z| ≤ (M2 / (m2' : ℝ)) * B → 1 ≤ psi z)
    (hlocal : ∀ u : ℝ, ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
      {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
        (M2 / T) * B})
    (hsmooth : ∀ u : ℝ, ∀ j : ℤ, Integrable
      (fun u' => T * psi (T *
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u'))
    (hsum : ∀ u : ℝ, Summable (fun j : ℤ =>
      affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)))
    (hret : Integrable (sigmaIIZPairRetainedKernel psi2 f
      M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (hmajor : Integrable (fun u : ℝ =>
      ((2 * Ctau * K) / M2) * f u *
        ∑' j : ℤ, affineSmoothing T psi f
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))) :
    ‖∫ z : ℝ × ℝ,
        sigmaIIZPairRetainedKernel psi2 f
          M2 T M3 Ctau B m2 m2' z‖ ≤
      ∫ u : ℝ,
        ((2 * Ctau * K) / M2) * f u *
          ∑' j : ℤ, affineSmoothing T psi f
            (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j) := by
  change ‖∫ z : ℝ × ℝ,
      sigmaIIZPairRetainedKernel psi2 f
        M2 T M3 Ctau B m2 m2' z ∂volume.prod volume‖ ≤ _
  rw [integral_prod _ hret]
  apply norm_integral_le_of_norm_le hmajor
  apply Filter.Eventually.of_forall
  intro u
  by_cases hfu : f u = 0
  · simp [sigmaIIZPairRetainedKernel, hfu]
  · refine (norm_integral_le_integral_norm _).trans ?_
    exact integral_norm_sigmaIIZPairRetainedKernel_le_smoothing
      psi2 psi f hK hM2 hT hCtau hB hY hf hf0 hpsi0 hF
      m2 m2' hm2' u (fun u' hfu' => hy u u' (mul_ne_zero hfu hfu'))
      hpsi_major (hlocal u) (hsmooth u) (hsum u)

/-- Complete finite `m₂,m₂'` assembly of the already-certified retained
smoothing and discarded second-Poisson estimates.  The output is the literal
affine sum which is subjected to Cauchy--Schwarz in (9.12); no `J` bound is
assumed here. -/
theorem sigmaIIFinite_le_pairSmoothing_add_time_neg100
    (f psi2 psi : ℝ → ℝ) (hf : Integrable f)
    (ellRange m2Range : Finset ℤ)
    (hcompact : HasCompactSupport (fun x : ℝ => (psi2 x : ℂ)))
    (hpsi2smooth : ContDiff ℝ ∞ (fun x : ℝ => (psi2 x : ℂ)))
    (q : ℕ) {K0 Kdec Ksup M2 T B Y C M3 Ctau : ℝ}
    (hKdec : 0 ≤ Kdec) (hKsup : 0 ≤ Ksup)
    (hM2 : 0 < M2) (hT : 0 < T) (hB : 0 < B)
    (hY : 0 ≤ Y) (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (hf0 : ∀ v, 0 ≤ f v) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hdecay2 : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        K0 / (1 + |xi|) ^ 2)
    (hdecay : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤
        Kdec / (1 + |xi|) ^ (q + 2))
    (hF : ∀ xi,
      ‖FourierTransform.fourier (fun x : ℝ => (psi2 x : ℂ)) xi‖ ≤ Ksup)
    (hbudget :
      (T / M2) * Kdec *
        ((1 + Y / (M2 / T)) ^ 2 * max 1 ((M2 / T) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hsupport : ∀ ell : ℤ,
      ell ∉ ellRange → psi2 (M2 * (ell : ℝ) / T) = 0)
    (hm2pos : ∀ m2 ∈ m2Range, 0 < (m2 : ℝ))
    (hy : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      ∀ z : ℝ × ℝ, f z.1 * f z.2 ≠ 0 →
        |(m2' : ℝ) * z.2 - (m2 : ℝ) * z.1| ≤ Y)
    (hpsi_major : ∀ m2' ∈ m2Range, ∀ z,
      |z| ≤ (M2 / (m2' : ℝ)) * B → 1 ≤ psi z)
    (hlocal : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      ∀ u : ℝ, ∀ j : ℤ, IntegrableOn (fun u' => T * f u')
        {u' | |(j : ℝ) - (m2' : ℝ) * u' + (m2 : ℝ) * u| ≤
          (M2 / T) * B})
    (haffineSmooth : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      ∀ u : ℝ, ∀ j : ℤ, Integrable
        (fun u' => T * psi (T *
          (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j - u')) * f u'))
    (hsum : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range, ∀ u : ℝ,
      Summable (fun j : ℤ => affineSmoothing T psi f
        (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)))
    (hret : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (sigmaIIZPairRetainedKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (htail : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (sigmaIIZPairTailKernel psi2 f
        M2 T M3 Ctau B m2 m2') (volume.prod volume))
    (hmajor : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (fun u : ℝ =>
        ((2 * Ctau * Ksup) / M2) * f u *
          ∑' j : ℤ, affineSmoothing T psi f
            (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j))) :
    sigmaIIFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau ≤
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        |(m2 : ℝ) * (m2' : ℝ)| *
          ((∫ u : ℝ,
            ((2 * Ctau * Ksup) / M2) * f u *
              ∑' j : ℤ, affineSmoothing T psi f
                (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) +
            (∫ u : ℝ, |f u|) ^ 2 * (2 * Ctau) * (C / T ^ 100)) := by
  refine (sigmaIIFinite_le_sum_retainedPairIntegral_add_time_neg100
    f hf ellRange m2Range psi2 hcompact hpsi2smooth q hKdec hM2 hT hB
    hY hM3 hCtau hdecay2 hdecay hbudget hsupport hy hret htail).trans ?_
  apply Finset.sum_le_sum
  intro m2 hm2
  apply Finset.sum_le_sum
  intro m2' hm2'
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  gcongr
  exact norm_integral_sigmaIIZPairRetainedKernel_le_smoothingIntegral
    psi2 psi f hKsup hM2 hT hCtau hB.le hY hf hf0 hpsi0 hF
    m2 m2' (hm2pos m2' hm2')
    (fun u u' huu' => hy m2 hm2 m2' hm2' (u, u') huu')
    (hpsi_major m2' hm2') (hlocal m2 hm2 m2' hm2')
    (haffineSmooth m2 hm2 m2' hm2') (hsum m2 hm2 m2' hm2')
    (hret m2 hm2 m2' hm2') (hmajor m2 hm2 m2' hm2')

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sigmaIIFinite_le_sum_norm_pairIntegrals
#print axioms GuthMaynardJIteration.integral_sigmaIIZPairKernel_eq_retained_add_tail
#print axioms GuthMaynardJIteration.sigmaIIFinite_le_sum_retainedPairIntegral_add_time_neg100
#print axioms GuthMaynardJIteration.norm_integral_sigmaIIZPairRetainedKernel_le_smoothingIntegral
#print axioms GuthMaynardJIteration.sigmaIIFinite_le_pairSmoothing_add_time_neg100
