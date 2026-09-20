import GuthMaynardJIterationFirstPoissonGhat

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- The exact finite Fourier expansion factorizes into the `m₃` Poisson sum
and the corrected `m₂` Fourier inner for each `m₁`. -/
theorem fourier_sourceGFinite_eq_firstPoissonFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi =
      ∑ m1 ∈ m1Range,
        sourceFirstPoissonFiniteSum m3Range psi1 M3 (m1 : ℝ) xi *
          sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) m1 xi := by
  rw [fourier_sourceGFinite m1Range m2Range m3Range psi1 f hf M3 xi
    hm1 hm2]
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  unfold sourceFirstPoissonFiniteSum sourceCorrectedM2FourierInner
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

/-- With a literal cutoff-support hypothesis, the finite transform of `g`
is exactly a finite `m₁` sum of full first-Poisson integer series. -/
theorem fourier_sourceGFinite_eq_firstPoissonFull
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0) :
    FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi =
      ∑ m1 ∈ m1Range,
        sourceFirstPoissonSum psi1 M3 (m1 : ℝ) xi *
          sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) m1 xi := by
  rw [fourier_sourceGFinite_eq_firstPoissonFinite m1Range m2Range m3Range
    psi1 f hf M3 xi hm1 hm2]
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  rw [sourceFirstPoissonFiniteSum_eq_full m3Range psi1 M3 (m1 : ℝ) xi
    hsupport]

/-- Exact TeX 1545 formula, with the corrected absolute Fourier dilation. -/
theorem fourier_sourceGFinite_eq_firstPoissonContribution
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f)
    (hcompact : HasCompactSupport psi1) (hsmooth : ContDiff ℝ ∞ psi1)
    {M3 : ℝ} (hM3 : 0 < M3) (xi : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0) :
    FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi =
      sourceFirstPoissonFullFinite m1Range m2Range
        (FourierTransform.fourier psi1) (FourierTransform.fourier f) M3 xi := by
  rw [fourier_sourceGFinite_eq_firstPoissonFull m1Range m2Range m3Range
    psi1 f hf M3 xi hm1 hm2 hsupport]
  unfold sourceFirstPoissonFullFinite
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  unfold sourceFirstPoissonContribution
  rw [sourceFirstPoissonSum_eq_full psi1 hcompact hsmooth hM3
    (by exact_mod_cast hm1 m1 hm1mem) xi]

/-- Literal (9.7) truncation for the finite source `g`.  The retained
expression uses the exact strict Poisson condition and the error is the
explicit Schwartz-seminorm budget times the corrected Fourier inners. -/
theorem norm_fourier_sourceGFinite_sub_retained_le_time_neg100
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (q : ℕ)
    (hcompact : HasCompactSupport psi1) (hsmooth : ContDiff ℝ ∞ psi1)
    {K0 K M3 B Y C T : ℝ}
    (hK : 0 ≤ K) (hM3 : 0 < M3) (hB : 0 < B) (hY : 0 ≤ Y)
    (hT : 0 < T)
    (hdecay2 : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K0 / (1 + |z|) ^ 2)
    (hdecay : ∀ z,
      ‖FourierTransform.fourier psi1 z‖ ≤ K / (1 + |z|) ^ (q + 2))
    (hbudget :
      M3 * K *
        ((1 + Y / (1 / M3)) ^ 2 * max 1 ((1 / M3) ^ 2) *
          integerQuadraticMass) * T ^ 100 ≤ C * B ^ q)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hsupport : ∀ m3 : ℤ,
      m3 ∉ m3Range → psi1 ((m3 : ℝ) / M3) = 0)
    (xi : ℝ) (hxi : ∀ m1 ∈ m1Range, |xi / (m1 : ℝ)| ≤ Y) :
    ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi -
        sourceFirstPoissonRetainedFinite m1Range m2Range
          (FourierTransform.fourier psi1) (FourierTransform.fourier f)
          M3 B xi‖ ≤
      (C / T ^ 100) *
        ∑ m1 ∈ m1Range,
          ‖sourceCorrectedM2FourierInner m2Range
            (FourierTransform.fourier f) m1 xi‖ := by
  rw [fourier_sourceGFinite_eq_firstPoissonContribution
    m1Range m2Range m3Range psi1 f hf hcompact hsmooth hM3 xi hm1 hm2
      hsupport]
  exact norm_sourceFirstPoissonFullFinite_sub_retained_le_time_neg100
    m1Range m2Range (FourierTransform.fourier psi1)
      (FourierTransform.fourier f) q hK hM3 hB hY hT hdecay2 hdecay
      hbudget hm1 xi hxi

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.fourier_sourceGFinite_eq_firstPoissonFinite
#print axioms GuthMaynardJIteration.fourier_sourceGFinite_eq_firstPoissonFull
#print axioms GuthMaynardJIteration.fourier_sourceGFinite_eq_firstPoissonContribution
#print axioms GuthMaynardJIteration.norm_fourier_sourceGFinite_sub_retained_le_time_neg100
