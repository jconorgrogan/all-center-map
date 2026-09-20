import GuthMaynardJIterationFirstPoissonFiniteRange

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Specialization of mathlib's additive-Haar translation theorem to the
real Fourier transform and the source phase convention. -/
theorem source_fourier_translate_right (f : ℝ → ℂ) (a xi : ℝ) :
    FourierTransform.fourier (fun u : ℝ => f (u + a)) xi =
      sourcePhase (a * xi) * FourierTransform.fourier f xi := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have h := Fourier.fourierIntegral_comp_add_right
    (E := ℂ) Real.fourierChar MeasureTheory.volume f a
  have hxi := congrFun h xi
  rw [Fourier.fourierIntegral_def, Fourier.fourierIntegral_def] at hxi
  simpa only [Function.comp_apply, Circle.smul_def, Real.fourierChar_apply,
    sourcePhase, smul_eq_mul] using hxi

/-- Fourier linearity for a complex scalar, in the concrete real-transform
normalization used by the source. -/
theorem source_fourier_const_mul (f : ℝ → ℂ) (c : ℂ) (xi : ℝ) :
    FourierTransform.fourier (fun u : ℝ => c * f u) xi =
      c * FourierTransform.fourier f xi := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  ring

/-- TeX 1537--1541: translation followed by Fourier dilation.  The answer
contains the positive phase from `u ↦ u + m₃/m₁` and the corrected absolute
Jacobian `|m₂/m₁|`. -/
theorem source_fourier_affine_shift
    (f : ℝ → ℂ) {m1 m2 : ℝ} (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0)
    (m3 xi : ℝ) :
    FourierTransform.fourier
        (fun u : ℝ => f ((m1 * u + m3) / m2)) xi =
      sourcePhase ((m3 / m1) * xi) *
        (((|m2 / m1| : ℝ) : ℂ) *
          FourierTransform.fourier f ((m2 / m1) * xi)) := by
  have hfun : (fun u : ℝ => f ((m1 * u + m3) / m2)) =
      fun u : ℝ => (fun v : ℝ => f (m1 * v / m2)) (u + m3 / m1) := by
    funext u
    congr 1
    field_simp [hm1, hm2]
  rw [hfun]
  calc
    FourierTransform.fourier
        (fun u : ℝ => (fun v : ℝ => f (m1 * v / m2))
          (u + m3 / m1)) xi =
      sourcePhase ((m3 / m1) * xi) *
        FourierTransform.fourier (fun v : ℝ => f (m1 * v / m2)) xi :=
      source_fourier_translate_right
        (fun v : ℝ => f (m1 * v / m2)) (m3 / m1) xi
    _ = _ := by
      rw [source_fourier_dilation f hm1 hm2 xi]
      change sourcePhase (m3 / m1 * xi) *
          (((|m2 / m1| : ℝ) : ℂ) *
            FourierTransform.fourier f (m2 / m1 * xi)) = _
      rfl

/-- The literal Fourier transform of one weighted `m₁,m₂,m₃` summand
in the definition of `g`. -/
theorem source_fourier_weighted_affine_shift
    (psi1 f : ℝ → ℂ) {M3 m1 m2 : ℝ}
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (m3 xi : ℝ) :
    FourierTransform.fourier
        (fun u : ℝ =>
          psi1 (m3 / M3) * f ((m1 * u + m3) / m2)) xi =
      psi1 (m3 / M3) * sourcePhase ((m3 / m1) * xi) *
        (((|m2 / m1| : ℝ) : ℂ) *
          FourierTransform.fourier f ((m2 / m1) * xi)) := by
  rw [source_fourier_const_mul,
    source_fourier_affine_shift f hm1 hm2 m3 xi]
  ring

def sourceFirstPoissonFiniteSum
    (m3Range : Finset ℤ) (psi1 : ℝ → ℂ) (M3 m1 xi : ℝ) : ℂ :=
  ∑ m3 ∈ m3Range,
    psi1 ((m3 : ℝ) / M3) *
      sourcePhase (((m3 : ℝ) / m1) * xi)

/-- Compact-support identification of the finite source `m₃` range with
the full first-Poisson integer series. -/
theorem sourceFirstPoissonFiniteSum_eq_full
    (m3Range : Finset ℤ) (psi1 : ℝ → ℂ) (M3 m1 xi : ℝ)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0) :
    sourceFirstPoissonFiniteSum m3Range psi1 M3 m1 xi =
      sourceFirstPoissonSum psi1 M3 m1 xi := by
  unfold sourceFirstPoissonFiniteSum sourceFirstPoissonSum
  rw [tsum_eq_sum (s := m3Range)]
  · apply Finset.sum_congr rfl
    intro m3 hm3
    congr 2
    ring
  · intro m3 hm3
    rw [hsupport m3 hm3]
    simp

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.source_fourier_translate_right
#print axioms GuthMaynardJIteration.source_fourier_const_mul
#print axioms GuthMaynardJIteration.source_fourier_affine_shift
#print axioms GuthMaynardJIteration.source_fourier_weighted_affine_shift
#print axioms GuthMaynardJIteration.sourceFirstPoissonFiniteSum_eq_full
