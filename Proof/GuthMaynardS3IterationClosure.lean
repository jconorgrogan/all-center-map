import GuthMaynardS3NormalizedBump
import GuthMaynardAffineSmoothingSubpower

open scoped BigOperators Real FourierTransform ContDiff
open MeasureTheory

noncomputable section
namespace GuthMaynardS3IterationClosure

open GuthMaynardJIteration

/-!
# One-step normalized smoothing closure

The literal Lemma 9.2 bump is kept at the source level, while this module
records the normalized kernel needed by the future J-iteration.  The kernel
has radius `2*B`, height at most one, and mass at most one.  Consequently the
profile height, Fourier rapid-decay seminorms, and the source L¹/L² masses do
not acquire an iteration loss; only the support collar grows by `2*B/T`.
-/

/-- A normalized literal bump preserves every field of the source-admissible
profile package in one smoothing step.  In particular, the rapid-decay
constant selected for each `(eta,j)` is inherited unchanged. -/
theorem normalizedAffineSmoothing_sourceAdmissibleProfile
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) :
    SourceAdmissibleProfile T S (F + (2 * B) / T)
      (affineSmoothing T (sourceBumpNormalized B hB) f) := by
  have hkernel : SourceSmoothingKernel (2 * B)
      (sourceBumpNormalized B hB) :=
    sourceBumpNormalized_sourceSmoothingKernel hB hB1
  convert sourceAdmissibleProfile_affineSmoothing hT
      (sourceBumpNormalized B hB) f hf hkernel using 1

/-- The height component of the closure, stated separately for source-facing
callers that do not need to destructure the whole profile package. -/
theorem normalizedAffineSmoothing_bounded
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (x : ℝ) :
    affineSmoothing T (sourceBumpNormalized B hB) f x ≤ S := by
  exact (normalizedAffineSmoothing_sourceAdmissibleProfile hT hB hB1 f hf).bounded x

/-- For a unit-height source profile, the smoothing height remains at most one. -/
theorem normalizedAffineSmoothing_unit_bounded
    {T F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T 1 F f) (x : ℝ) :
    affineSmoothing T (sourceBumpNormalized B hB) f x ≤ 1 := by
  exact normalizedAffineSmoothing_bounded hT hB hB1 f hf x

/-- The normalized smoothing is a pointwise Fourier contraction.  This is
stronger than an existential rapid-decay restatement and is the form needed
when a uniform constant has already been selected outside the `(T,f)` loop. -/
theorem normalizedAffineSmoothing_fourier_norm_le
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (z : ℝ) :
    ‖FourierTransform.fourier
      (fun x : ℝ =>
        (affineSmoothing T (sourceBumpNormalized B hB) f x : ℂ)) z‖ ≤
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ := by
  have hkernel : SourceSmoothingKernel (2 * B)
      (sourceBumpNormalized B hB) :=
    sourceBumpNormalized_sourceSmoothingKernel hB hB1
  exact norm_fourier_ofReal_affineSmoothing_le hT
    (sourceBumpNormalized B hB) f hkernel.nonneg hkernel.mass_le_one
    hkernel.integrable hf.integrable hkernel.continuous hf.continuous z

/-- A preselected Fourier-decay constant is preserved verbatim by one
smoothing step; no new existential quantifier is introduced. -/
theorem normalizedAffineSmoothing_fourier_bound_of_supplied_constant
    {T S F B C : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f)
    {eta : ℝ} (j : ℕ)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        C * T ^ eta * (T / |z|) ^ j * S)
    (z : ℝ) (hz : z ≠ 0) :
    ‖FourierTransform.fourier
      (fun x : ℝ =>
        (affineSmoothing T (sourceBumpNormalized B hB) f x : ℂ)) z‖ ≤
      C * T ^ eta * (T / |z|) ^ j * S := by
  exact (normalizedAffineSmoothing_fourier_norm_le hT hB hB1 f hf z).trans
    (hbound z hz)

/-- The rapid-decay witness is passed through unchanged: for every loss
exponent and order, the same constant selected for the input profile works
for the smoothed profile. -/
theorem normalizedAffineSmoothing_rapidDecay_same_witness
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f)
    {eta : ℝ} (heta : 0 < eta) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℝ, z ≠ 0 →
        ‖FourierTransform.fourier
          (fun x : ℝ =>
            (affineSmoothing T (sourceBumpNormalized B hB) f x : ℂ)) z‖ ≤
          C * T ^ eta * (T / |z|) ^ j * S := by
  have hkernel : SourceSmoothingKernel (2 * B)
      (sourceBumpNormalized B hB) :=
    sourceBumpNormalized_sourceSmoothingKernel hB hB1
  obtain ⟨C, hC, hbound⟩ := hf.rapidDecay eta heta j
  refine ⟨C, hC, ?_⟩
  intro z hz
  exact (norm_fourier_ofReal_affineSmoothing_le hT
    (sourceBumpNormalized B hB) f hkernel.nonneg hkernel.mass_le_one
    hkernel.integrable hf.integrable hkernel.continuous hf.continuous z).trans
      (hbound z hz)

/-- L¹ and squared-L² masses are nonincreasing under the normalized smoothing.
The two inequalities are bundled so the norm obligations used by the next J
step can be discharged from one source profile premise. -/
theorem normalizedAffineSmoothing_L1_L2_contractions
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) :
    (∫ x : ℝ, affineSmoothing T (sourceBumpNormalized B hB) f x) ≤
        ∫ u : ℝ, f u ∧
    (∫ x : ℝ, affineSmoothing T (sourceBumpNormalized B hB) f x ^ 2) ≤
        ∫ u : ℝ, f u ^ 2 := by
  have hkernel : SourceSmoothingKernel (2 * B)
      (sourceBumpNormalized B hB) :=
    sourceBumpNormalized_sourceSmoothingKernel hB hB1
  constructor
  · exact integral_affineSmoothing_le_of_integrable hT
      (sourceBumpNormalized B hB) f hf.nonneg hkernel.mass_le_one
      hkernel.integrable hf.integrable
  · exact integral_sq_affineSmoothing_le_one_of_integrable hT
      (sourceBumpNormalized B hB) f hkernel.nonneg hf.nonneg
      hkernel.mass_le_one hkernel.integrable hf.integrable hf.squareIntegrable

/-- Every finite iterate remains source-admissible.  The only accumulated
loss is the explicit support collar `n*(2B/T)`. -/
theorem normalizedAffineSmoothing_iterate_sourceAdmissibleProfile
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (n : ℕ) :
    SourceAdmissibleProfile T S (F + (n : ℝ) * ((2 * B) / T))
      (affineSmoothingIterate T (sourceBumpNormalized B hB) n f) := by
  have hkernel : SourceSmoothingKernel (2 * B)
      (sourceBumpNormalized B hB) :=
    sourceBumpNormalized_sourceSmoothingKernel hB hB1
  exact sourceAdmissibleProfile_affineSmoothingIterate hT
    (sourceBumpNormalized B hB) f hf hkernel n

/-- The Fourier contraction composes along every finite iterate with the same
`T` and normalized kernel. -/
theorem normalizedAffineSmoothing_iterate_fourier_norm_le
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (n : ℕ) (z : ℝ) :
    ‖FourierTransform.fourier
      (fun x : ℝ =>
        (affineSmoothingIterate T (sourceBumpNormalized B hB) n f x : ℂ)) z‖ ≤
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hprev := normalizedAffineSmoothing_iterate_sourceAdmissibleProfile
        hT hB hB1 f hf n
      have hone := normalizedAffineSmoothing_fourier_norm_le hT hB hB1
        (affineSmoothingIterate T (sourceBumpNormalized B hB) n f) hprev z
      simpa only [affineSmoothingIterate] using hone.trans ih

/-- A preselected decay constant remains valid after any finite iterate. -/
theorem normalizedAffineSmoothing_iterate_fourier_bound_of_supplied_constant
    {T S F B C : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (n : ℕ)
    {eta : ℝ} (j : ℕ)
    (hbound : ∀ z : ℝ, z ≠ 0 →
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ ≤
        C * T ^ eta * (T / |z|) ^ j * S)
    (z : ℝ) (hz : z ≠ 0) :
    ‖FourierTransform.fourier
      (fun x : ℝ =>
        (affineSmoothingIterate T (sourceBumpNormalized B hB) n f x : ℂ)) z‖ ≤
      C * T ^ eta * (T / |z|) ^ j * S := by
  exact (normalizedAffineSmoothing_iterate_fourier_norm_le hT hB hB1
    f hf n z).trans (hbound z hz)

/-- L¹ and squared-L² contraction compose along every finite iterate. -/
theorem normalizedAffineSmoothing_iterate_L1_L2_contractions
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B) (hB1 : 1 ≤ B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) (n : ℕ) :
    (∫ x : ℝ, affineSmoothingIterate T (sourceBumpNormalized B hB) n f x) ≤
        ∫ u : ℝ, f u ∧
    (∫ x : ℝ, affineSmoothingIterate T (sourceBumpNormalized B hB) n f x ^ 2) ≤
        ∫ u : ℝ, f u ^ 2 := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
      have hprev := normalizedAffineSmoothing_iterate_sourceAdmissibleProfile
        hT hB hB1 f hf n
      have hone := normalizedAffineSmoothing_L1_L2_contractions hT hB hB1
        (affineSmoothingIterate T (sourceBumpNormalized B hB) n f) hprev
      constructor
      · exact le_trans (by simpa only [affineSmoothingIterate] using hone.1) ih.1
      · exact le_trans (by simpa only [affineSmoothingIterate] using hone.2) ih.2

/-- The support collar is the literal `F+2B/T`, obtained from the pointwise
support theorem rather than from an informal convolution heuristic. -/
theorem normalizedAffineSmoothing_abs_support
    {T S F B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (f : ℝ → ℝ) (hf : SourceAdmissibleProfile T S F f) {x : ℝ}
    (hx : affineSmoothing T (sourceBumpNormalized B hB) f x ≠ 0) :
    |x| ≤ F + (2 * B) / T := by
  exact affineSmoothing_abs_support hT
    (sourceBumpNormalized B hB) f
    (fun z hz => sourceBumpNormalized_supported hB hz)
    hf.supported hx

end GuthMaynardS3IterationClosure

#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_sourceAdmissibleProfile
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_bounded
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_unit_bounded
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_fourier_norm_le
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_fourier_bound_of_supplied_constant
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_rapidDecay_same_witness
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_L1_L2_contractions
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_iterate_sourceAdmissibleProfile
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_iterate_fourier_norm_le
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_iterate_fourier_bound_of_supplied_constant
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_iterate_L1_L2_contractions
#print axioms GuthMaynardS3IterationClosure.normalizedAffineSmoothing_abs_support
