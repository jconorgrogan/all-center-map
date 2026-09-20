import GuthMaynardJIterationBumpWeld
import GuthMaynardJIterationPlancherel

open scoped BigOperators FourierTransform Real SchwartzMap
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# The exact `(9.2)` Plancherel weld

The existing development separately proves that the concrete plateau bump
turns the finite affine energy into the physical-space norm of the source
function `g`, and proves Plancherel for that same finite `g`.  This file joins
the two statements.  It is the literal source transition at the displayed
equation `(9.2)` (source text lines 1988--1994), including the real-to-complex
coercion which otherwise remains easy to hide in prose.

No estimate is assumed here.  The only compatibility hypothesis says that the
complex Schwartz representative is the complexification of the real source
profile.
-/

/-- The finite affine branch is exactly the Fourier energy of the concrete
source function `g` after the plateau and nonzero-denominator conditions are
inserted. -/
theorem sourceFiniteAffineEnergy_eq_fourierIntegral_sourceBump
    (m1Range m2Range m3Range : Finset ℤ)
    (f : ℝ → ℝ) (fSchwartz : 𝓢(ℝ, ℂ))
    {R M3 : ℝ} (hR : 0 < R)
    (hm3 : ∀ m3 ∈ m3Range, |(m3 : ℝ) / M3| ≤ R)
    (hf : ∀ u : ℝ, fSchwartz u = (f u : ℂ))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    sourceFiniteAffineEnergy m1Range m2Range m3Range f =
      ∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (fun u : ℝ => fSchwartz u) M3) xi‖ ^ 2 := by
  have hsource :
      sourceGFinite m1Range m2Range m3Range
          (fun x : ℝ => (sourceBump R hR x : ℂ))
          (fun u : ℝ => fSchwartz u) M3 =
        sourceGFinite m1Range m2Range m3Range
          (fun x : ℝ => (sourceBump R hR x : ℂ))
          (fun u : ℝ => (f u : ℂ)) M3 := by
    funext u
    unfold sourceGFinite sourceGSummand
    apply Finset.sum_congr rfl
    intro m1 hm1mem
    apply Finset.sum_congr rfl
    intro m2 hm2mem
    apply Finset.sum_congr rfl
    intro m3 hm3mem
    exact congrArg
      (fun z : ℂ =>
        (sourceBump R hR ((m3 : ℝ) / M3) : ℂ) * z)
      (hf (((m1 : ℝ) * u + (m3 : ℝ)) / (m2 : ℝ)))
  calc
    sourceFiniteAffineEnergy m1Range m2Range m3Range f =
        ∫ u : ℝ,
          ‖sourceGFinite m1Range m2Range m3Range
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (fun x : ℝ => (f x : ℂ)) M3 u‖ ^ 2 :=
      sourceFiniteAffineEnergy_eq_integral_norm_sourceGFinite_sourceBump
        m1Range m2Range m3Range f hR hm3
    _ = ∫ u : ℝ,
          ‖sourceGFinite m1Range m2Range m3Range
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (fun x : ℝ => fSchwartz x) M3 u‖ ^ 2 := by
      rw [hsource]
    _ = ∫ xi : ℝ,
          ‖FourierTransform.fourier
            (sourceGFinite m1Range m2Range m3Range
              (fun x : ℝ => (sourceBump R hR x : ℂ))
              (fun x : ℝ => fSchwartz x) M3) xi‖ ^ 2 :=
      (integral_norm_sq_fourier_sourceGFinite m1Range m2Range m3Range
        (fun x : ℝ => (sourceBump R hR x : ℂ)) fSchwartz M3 hm1 hm2).symm

/-- Any certified frequency-side estimate now transfers directly to the
literal finite affine energy.  This is the reusable upper-bound form of the
exact `(9.2)` identity. -/
theorem sourceFiniteAffineEnergy_le_of_sourceBump_fourierIntegral_le
    (m1Range m2Range m3Range : Finset ℤ)
    (f : ℝ → ℝ) (fSchwartz : 𝓢(ℝ, ℂ))
    {R M3 B : ℝ} (hR : 0 < R)
    (hm3 : ∀ m3 ∈ m3Range, |(m3 : ℝ) / M3| ≤ R)
    (hf : ∀ u : ℝ, fSchwartz u = (f u : ℂ))
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0)
    (hfrequency :
      (∫ xi : ℝ,
        ‖FourierTransform.fourier
          (sourceGFinite m1Range m2Range m3Range
            (fun x : ℝ => (sourceBump R hR x : ℂ))
            (fun u : ℝ => fSchwartz u) M3) xi‖ ^ 2) ≤ B) :
    sourceFiniteAffineEnergy m1Range m2Range m3Range f ≤ B := by
  rw [sourceFiniteAffineEnergy_eq_fourierIntegral_sourceBump
    m1Range m2Range m3Range f fSchwartz hR hm3 hf hm1 hm2]
  exact hfrequency

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_eq_fourierIntegral_sourceBump
#print axioms GuthMaynardJIteration.sourceFiniteAffineEnergy_le_of_sourceBump_fourierIntegral_le
