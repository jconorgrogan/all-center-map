import GuthMaynardJIterationFirstPoissonFourierShift

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- Finite Fourier linearity with the necessary `L¹` hypotheses exposed. -/
theorem source_fourier_finsetSum
    {iota : Type*} (s : Finset iota) (F : iota → ℝ → ℂ)
    (hF : ∀ i ∈ s, Integrable (F i)) (xi : ℝ) :
    FourierTransform.fourier (fun u : ℝ => ∑ i ∈ s, F i u) xi =
      ∑ i ∈ s, FourierTransform.fourier (F i) xi := by
  rw [Real.fourier_real_eq]
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum s]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Real.fourier_real_eq]
  · intro i hi
    simpa [mul_comm] using
      (Real.fourierIntegral_convergent_iff xi).2 (hF i hi)

/-- The affine source summand is integrable whenever `f` is, for nonzero
`m₁,m₂`. -/
theorem integrable_source_affine_shift
    (f : ℝ → ℂ) (hf : Integrable f) {m1 m2 : ℝ}
    (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) (m3 : ℝ) :
    Integrable (fun u : ℝ => f ((m1 * u + m3) / m2)) := by
  have hscale : Integrable (fun u : ℝ => f ((m1 / m2) * u)) :=
    hf.comp_mul_left' (div_ne_zero hm1 hm2)
  have htranslate :=
    (measurePreserving_add_right volume (m3 / m1)).integrable_comp_of_integrable
      hscale
  apply htranslate.congr
  filter_upwards with u
  simp only [Function.comp_apply]
  congr 1
  field_simp [hm1, hm2]

def sourceGSummand
    (psi1 f : ℝ → ℂ) (M3 : ℝ) (m1 m2 m3 : ℤ) (u : ℝ) : ℂ :=
  psi1 ((m3 : ℝ) / M3) *
    f (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ))

/-- A literal finite-range version of the source's function `g`. -/
def sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (M3 : ℝ) (u : ℝ) : ℂ :=
  ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
    sourceGSummand psi1 f M3 m1 m2 m3 u

theorem integrable_sourceGSummand
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 : ℝ)
    (m1 m2 m3 : ℤ) (hm1 : m1 ≠ 0) (hm2 : m2 ≠ 0) :
    Integrable (sourceGSummand psi1 f M3 m1 m2 m3) := by
  unfold sourceGSummand
  exact (integrable_source_affine_shift f hf
    (by exact_mod_cast hm1) (by exact_mod_cast hm2) (m3 : ℝ)).const_mul _

/-- Exact transform of the finite source `g`, before the three finite sums
are factorized. -/
theorem fourier_sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 f : ℝ → ℂ) (hf : Integrable f) (M3 xi : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1 f M3) xi =
      ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
        psi1 ((m3 : ℝ) / M3) *
          sourcePhase (((m3 : ℝ) / (m1 : ℝ)) * xi) *
            (((|((m2 : ℝ) / (m1 : ℝ))| : ℝ) : ℂ) *
              FourierTransform.fourier f
                (((m2 : ℝ) / (m1 : ℝ)) * xi)) := by
  unfold sourceGFinite
  rw [source_fourier_finsetSum m1Range]
  · apply Finset.sum_congr rfl
    intro m1 hm1mem
    rw [source_fourier_finsetSum m2Range]
    · apply Finset.sum_congr rfl
      intro m2 hm2mem
      rw [source_fourier_finsetSum m3Range]
      · apply Finset.sum_congr rfl
        intro m3 hm3mem
        exact source_fourier_weighted_affine_shift psi1 f
          (by exact_mod_cast hm1 m1 hm1mem)
          (by exact_mod_cast hm2 m2 hm2mem) (m3 : ℝ) xi
      · intro m3 hm3mem
        exact integrable_sourceGSummand psi1 f hf M3 m1 m2 m3
          (hm1 m1 hm1mem) (hm2 m2 hm2mem)
    · intro m2 hm2mem
      apply integrable_finsetSum m3Range
      intro m3 hm3mem
      exact integrable_sourceGSummand psi1 f hf M3 m1 m2 m3
        (hm1 m1 hm1mem) (hm2 m2 hm2mem)
  · intro m1 hm1mem
    apply integrable_finsetSum m2Range
    intro m2 hm2mem
    apply integrable_finsetSum m3Range
    intro m3 hm3mem
    exact integrable_sourceGSummand psi1 f hf M3 m1 m2 m3
      (hm1 m1 hm1mem) (hm2 m2 hm2mem)

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.source_fourier_finsetSum
#print axioms GuthMaynardJIteration.integrable_source_affine_shift
#print axioms GuthMaynardJIteration.integrable_sourceGSummand
#print axioms GuthMaynardJIteration.fourier_sourceGFinite
