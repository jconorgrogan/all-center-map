import GuthMaynardJIterationSigmaIIFubini

open scoped BigOperators Real FourierTransform ComplexConjugate
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

def sigmaIIComplexFinite (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ)
    (M2 T M3 Ctau : ℝ) : ℂ :=
  ∑ ell ∈ ellRange,
    (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
      ∫ tau in -Ctau..Ctau,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          sigmaIIFourierSummand M3 fhat ell m2 tau *
            conj (sigmaIIFourierSummand M3 fhat ell m2' tau)

def sigmaIIZPairKernel (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    (f : ℝ → ℝ) (M2 T M3 Ctau : ℝ) (m2 m2' : ℤ)
    (z : ℝ × ℝ) : ℂ :=
  ((f z.1 * f z.2 : ℝ) : ℂ) *
    (sigmaIIZ1 M3 Ctau (m2 : ℝ) (m2' : ℝ) z.1 z.2 *
      sigmaIIZ2Finite ellRange psi2 M2 T
        (m2 : ℝ) (m2' : ℝ) z.1 z.2)

def sigmaIIProductComplexFinite (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (f : ℝ → ℝ)
    (M2 T M3 Ctau : ℝ) : ℂ :=
  ∫ z : ℝ × ℝ,
    ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
      (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
        sigmaIIZPairKernel ellRange psi2 f M2 T M3 Ctau m2 m2' z

theorem continuous_fourier_of_integrable
    (f : ℝ → ℝ) (hf : Integrable f) :
    Continuous (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) := by
  exact VectorFourier.fourierIntegral_continuous
    Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf.ofReal

theorem sigmaIIFinite_eq_re_complexFinite
    (ellRange m2Range : Finset ℤ)
    (psi2 : ℝ → ℝ) (fhat : ℝ → ℂ) (hfhat : Continuous fhat)
    (M2 T M3 Ctau : ℝ) :
    sigmaIIFinite ellRange m2Range psi2 fhat M2 T M3 Ctau =
      (sigmaIIComplexFinite ellRange m2Range psi2 fhat
        M2 T M3 Ctau).re := by
  unfold sigmaIIFinite sigmaIIComplexFinite
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro ell hell
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1
  have hcont : Continuous (fun tau : ℝ =>
      ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        sigmaIIFourierSummand M3 fhat ell m2 tau *
          conj (sigmaIIFourierSummand M3 fhat ell m2' tau)) := by
    apply continuous_finsetSum
    intro m2 hm2
    apply continuous_finsetSum
    intro m2' hm2'
    unfold sigmaIIFourierSummand sigmaIIAffineFrequency
    fun_prop
  calc
    (∫ tau in -Ctau..Ctau,
      ‖∑ m2 ∈ m2Range,
        sigmaIIFourierSummand M3 fhat ell m2 tau‖ ^ 2) =
      ∫ tau in -Ctau..Ctau,
        (∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          sigmaIIFourierSummand M3 fhat ell m2 tau *
            conj (sigmaIIFourierSummand M3 fhat ell m2' tau)).re := by
        apply intervalIntegral.integral_congr
        intro tau htau
        exact norm_sq_finset_sum_eq_re_double_sum m2Range
          (fun m2 => sigmaIIFourierSummand M3 fhat ell m2 tau)
    _ = (∫ tau in -Ctau..Ctau,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          sigmaIIFourierSummand M3 fhat ell m2 tau *
            conj (sigmaIIFourierSummand M3 fhat ell m2' tau)).re := by
      exact Complex.reCLM.intervalIntegral_comp_comm
        (hcont.intervalIntegrable (-Ctau) Ctau)

theorem intervalIntegral_finset_double_sum_complex
    {ι : Type*} (s : Finset ι) (F : ι → ι → ℝ → ℂ)
    (hF : ∀ i ∈ s, ∀ j ∈ s, Continuous (F i j))
    (a b : ℝ) :
    (∫ x in a..b, ∑ i ∈ s, ∑ j ∈ s, F i j x) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ x in a..b, F i j x := by
  calc
    (∫ x in a..b, ∑ i ∈ s, ∑ j ∈ s, F i j x) =
        ∑ i ∈ s, ∫ x in a..b, ∑ j ∈ s, F i j x := by
      apply intervalIntegral.integral_finsetSum
      intro i hi
      apply Continuous.intervalIntegrable
      apply continuous_finsetSum
      intro j hj
      exact hF i hi j hj
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x in a..b, F i j x := by
      apply Finset.sum_congr rfl
      intro i hi
      apply intervalIntegral.integral_finsetSum
      intro j hj
      exact (hF i hi j hj).intervalIntegrable a b

theorem integrable_sigmaIIZPairKernel
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) (m2 m2' : ℤ) :
    Integrable (sigmaIIZPairKernel ellRange psi2 f
      M2 T M3 Ctau m2 m2') (volume.prod volume) := by
  let w : ℤ → ℂ := fun ell => (psi2 (M2 * (ell : ℝ) / T) : ℂ)
  let H : ℤ → (ℝ × ℝ) → ℂ := fun ell z =>
    w ell * ∫ tau in -Ctau..Ctau,
      sigmaIITripleKernel f M3 ell m2 m2' tau z
  have hH : ∀ ell ∈ ellRange, Integrable (H ell) (volume.prod volume) := by
    intro ell hell
    exact (integrable_intervalIntegral_sigmaIITripleKernel
      f hf M3 hCtau ell m2 m2').const_mul (w ell)
  have hsum : Integrable (fun z => ∑ ell ∈ ellRange, H ell z)
      (volume.prod volume) := integrable_finsetSum ellRange hH
  apply hsum.congr
  filter_upwards with z
  dsimp only [H, w]
  unfold sigmaIIZPairKernel sigmaIITripleKernel fourierPairKernel
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

theorem finite_affine_sigmaSummandPair_eq_integral_Z1_Z2
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) (m2 m2' : ℤ) :
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        ∫ tau in -Ctau..Ctau,
          sigmaIIFourierSummand M3
              (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
              ell m2 tau *
            conj (sigmaIIFourierSummand M3
              (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
              ell m2' tau)) =
      ∫ z : ℝ × ℝ,
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          sigmaIIZPairKernel ellRange psi2 f
            M2 T M3 Ctau m2 m2' z := by
  simp_rw [sigmaIIFourierSummand_mul_conj]
  simp_rw [intervalIntegral.integral_const_mul]
  calc
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        (((m2 : ℂ) * (m2' : ℂ)) *
          ∫ tau in -Ctau..Ctau,
            FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2 tau) *
              conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                (sigmaIIAffineFrequency M3 ell m2' tau)))) =
      ((m2 : ℂ) * (m2' : ℂ)) *
        ∑ ell ∈ ellRange,
          (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
            ∫ tau in -Ctau..Ctau,
              FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                  (sigmaIIAffineFrequency M3 ell m2 tau) *
                conj (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
                  (sigmaIIAffineFrequency M3 ell m2' tau)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ell hell
      ring
    _ = ((m2 : ℂ) * (m2' : ℂ)) *
        ∫ z : ℝ × ℝ,
          sigmaIIZPairKernel ellRange psi2 f
            M2 T M3 Ctau m2 m2' z := by
      rw [finite_affine_fourierPair_eq_integral_Z1_Z2
        f hf ellRange psi2 hM3 hCtau M2 T m2 m2']
      rfl
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      push_cast
      rfl

theorem integral_finset_double_sum_complex
    {alpha ι : Type*} [MeasurableSpace alpha]
    (mu : Measure alpha) (s : Finset ι) (F : ι → ι → alpha → ℂ)
    (hF : ∀ i ∈ s, ∀ j ∈ s, Integrable (F i j) mu) :
    (∫ x, ∑ i ∈ s, ∑ j ∈ s, F i j x ∂mu) =
      ∑ i ∈ s, ∑ j ∈ s, ∫ x, F i j x ∂mu := by
  calc
    (∫ x, ∑ i ∈ s, ∑ j ∈ s, F i j x ∂mu) =
      ∑ i ∈ s, ∫ x, ∑ j ∈ s, F i j x ∂mu := by
        apply integral_finsetSum
        intro i hi
        exact integrable_finsetSum s (fun j hj => hF i hi j hj)
    _ = ∑ i ∈ s, ∑ j ∈ s, ∫ x, F i j x ∂mu := by
      apply Finset.sum_congr rfl
      intro i hi
      exact integral_finsetSum s (fun j hj => hF i hi j hj)

theorem sigmaIIComplexFinite_eq_product
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) :
    sigmaIIComplexFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau =
      sigmaIIProductComplexFinite ellRange m2Range psi2 f
        M2 T M3 Ctau := by
  let fhat : ℝ → ℂ :=
    FourierTransform.fourier (fun u : ℝ => (f u : ℂ))
  let P : ℤ → ℤ → ℤ → ℝ → ℂ := fun ell m2 m2' tau =>
    sigmaIIFourierSummand M3 fhat ell m2 tau *
      conj (sigmaIIFourierSummand M3 fhat ell m2' tau)
  have hfhat : Continuous fhat := continuous_fourier_of_integrable f hf
  have hP : ∀ ell ∈ ellRange, ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Continuous (P ell m2 m2') := by
    intro ell hell m2 hm2 m2' hm2'
    dsimp only [P]
    unfold sigmaIIFourierSummand sigmaIIAffineFrequency
    fun_prop
  have hZ : ∀ m2 ∈ m2Range, ∀ m2' ∈ m2Range,
      Integrable (fun z : ℝ × ℝ =>
        (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
          sigmaIIZPairKernel ellRange psi2 f
            M2 T M3 Ctau m2 m2' z) (volume.prod volume) := by
    intro m2 hm2 m2' hm2'
    exact (integrable_sigmaIIZPairKernel f hf ellRange psi2
      hM3 hCtau M2 T m2 m2').const_mul _
  change (∑ ell ∈ ellRange,
    (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
      ∫ tau in -Ctau..Ctau,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range, P ell m2 m2' tau) = _
  calc
    (∑ ell ∈ ellRange,
      (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
        ∫ tau in -Ctau..Ctau,
          ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range, P ell m2 m2' tau) =
      ∑ ell ∈ ellRange,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
            ∫ tau in -Ctau..Ctau, P ell m2 m2' tau := by
      apply Finset.sum_congr rfl
      intro ell hell
      rw [intervalIntegral_finset_double_sum_complex m2Range
        (P ell) (hP ell hell) (-Ctau) Ctau]
      simp_rw [Finset.mul_sum]
    _ = ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        ∑ ell ∈ ellRange,
          (psi2 (M2 * (ell : ℝ) / T) : ℂ) *
            ∫ tau in -Ctau..Ctau, P ell m2 m2' tau := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro m2 hm2
      rw [Finset.sum_comm]
    _ = ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
        ∫ z : ℝ × ℝ,
          (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z := by
      apply Finset.sum_congr rfl
      intro m2 hm2
      apply Finset.sum_congr rfl
      intro m2' hm2'
      exact finite_affine_sigmaSummandPair_eq_integral_Z1_Z2
        f hf ellRange psi2 hM3 hCtau M2 T m2 m2'
    _ = ∫ z : ℝ × ℝ,
        ∑ m2 ∈ m2Range, ∑ m2' ∈ m2Range,
          (((m2 : ℝ) * (m2' : ℝ) : ℝ) : ℂ) *
            sigmaIIZPairKernel ellRange psi2 f
              M2 T M3 Ctau m2 m2' z := by
      exact (integral_finset_double_sum_complex
        (volume.prod volume) m2Range _ hZ).symm
    _ = _ := by rfl

theorem sigmaIIFinite_eq_re_product
    (f : ℝ → ℝ) (hf : Integrable f)
    (ellRange m2Range : Finset ℤ) (psi2 : ℝ → ℝ)
    {M3 Ctau : ℝ} (hM3 : M3 ≠ 0) (hCtau : 0 ≤ Ctau)
    (M2 T : ℝ) :
    sigmaIIFinite ellRange m2Range psi2
        (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)))
        M2 T M3 Ctau =
      (sigmaIIProductComplexFinite ellRange m2Range psi2 f
        M2 T M3 Ctau).re := by
  rw [sigmaIIFinite_eq_re_complexFinite ellRange m2Range psi2
    _ (continuous_fourier_of_integrable f hf) M2 T M3 Ctau]
  rw [sigmaIIComplexFinite_eq_product f hf ellRange m2Range psi2
    hM3 hCtau M2 T]

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.continuous_fourier_of_integrable
#print axioms GuthMaynardJIteration.sigmaIIFinite_eq_re_complexFinite
#print axioms GuthMaynardJIteration.intervalIntegral_finset_double_sum_complex
#print axioms GuthMaynardJIteration.integrable_sigmaIIZPairKernel
#print axioms GuthMaynardJIteration.finite_affine_sigmaSummandPair_eq_integral_Z1_Z2
#print axioms GuthMaynardJIteration.integral_finset_double_sum_complex
#print axioms GuthMaynardJIteration.sigmaIIComplexFinite_eq_product
#print axioms GuthMaynardJIteration.sigmaIIFinite_eq_re_product
