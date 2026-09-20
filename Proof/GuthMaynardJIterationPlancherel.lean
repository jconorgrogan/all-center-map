import GuthMaynardJIterationFrequencyComplete
import Mathlib.Analysis.Fourier.LpSpace

open scoped BigOperators FourierTransform Real SchwartzMap
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-- A Schwartz realization of `x ↦ f(a*x+b)`. -/
def sourceAffineSchwartz (f : 𝓢(ℝ, ℂ)) (a b : ℝ) : 𝓢(ℝ, ℂ) :=
  if ha : a = 0 then 0 else
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (ContinuousLinearEquiv.smulLeft (Units.mk0 a ha))
      (f.compSubConstCLM ℂ (-b))

@[simp] theorem sourceAffineSchwartz_apply
    (f : 𝓢(ℝ, ℂ)) (a b : ℝ) (ha : a ≠ 0) (x : ℝ) :
    sourceAffineSchwartz f a b x = f (a * x + b) := by
  simp [sourceAffineSchwartz, ha, Units.smul_def]

/-- The literal finite source `g` as a Schwartz map whenever `f` is Schwartz. -/
def sourceGSchwartzFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : 𝓢(ℝ, ℂ)) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) : 𝓢(ℝ, ℂ) :=
  ∑ m1 ∈ m1Range, ∑ m2 ∈ m2Range, ∑ m3 ∈ m3Range,
    psi1 ((m3 : ℝ) / M3) •
      sourceAffineSchwartz f ((m1 : ℝ) / (m2 : ℝ))
        ((m3 : ℝ) / (m2 : ℝ))

theorem sourceGSchwartzFinite_apply
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : 𝓢(ℝ, ℂ)) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) (u : ℝ) :
    sourceGSchwartzFinite m1Range m2Range m3Range psi1 f M3 hm1 hm2 u =
      sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3 u := by
  unfold sourceGSchwartzFinite sourceGFinite sourceGSummand
  simp only [SchwartzMap.sum_apply, SchwartzMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m1 hm1mem
  apply Finset.sum_congr rfl
  intro m2 hm2mem
  apply Finset.sum_congr rfl
  intro m3 hm3mem
  have hm1R : (m1 : ℝ) ≠ 0 := by exact_mod_cast hm1 m1 hm1mem
  have hm2R : (m2 : ℝ) ≠ 0 := by exact_mod_cast hm2 m2 hm2mem
  rw [sourceAffineSchwartz_apply _ _ _ (div_ne_zero hm1R hm2R)]
  congr 2
  field_simp [hm2R]

/-- The squared norm of a Schwartz map is integrable.  This small companion to
Plancherel supplies the `IntegrableOn` premise needed when the Fourier integral
is split into low, medium, and high regions. -/
theorem integrable_norm_sq_schwartzMap (H : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ => ‖H x‖ ^ 2) := by
  have hnorm : Integrable (fun x : ℝ => ‖H x‖) := H.integrable.norm
  have hmeas : AEStronglyMeasurable (fun x : ℝ => ‖H x‖) :=
    H.continuous.norm.aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂volume,
      ‖(‖H x‖ : ℝ)‖ ≤ (SchwartzMap.seminorm ℂ 0 0) H := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    simpa using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ H 0 x
  simpa [pow_two] using hnorm.bdd_mul hmeas hbound

/-- Integrability of the literal squared Fourier transform of the finite
source `g`, obtained from its exact Schwartz realization. -/
theorem integrable_norm_sq_fourier_sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : 𝓢(ℝ, ℂ)) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    Integrable (fun xi : ℝ =>
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun x => f x) M3) xi‖ ^ 2) := by
  let G : 𝓢(ℝ, ℂ) :=
    sourceGSchwartzFinite m1Range m2Range m3Range psi1 f M3 hm1 hm2
  have hG : (fun u : ℝ => G u) =
      sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3 := by
    funext u
    exact sourceGSchwartzFinite_apply
      m1Range m2Range m3Range psi1 f M3 hm1 hm2 u
  have hfourier : FourierTransform.fourier
      (sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3) =
        fun xi => FourierTransform.fourier G xi := by
    rw [← hG, ← SchwartzMap.fourier_coe]
  rw [hfourier]
  exact integrable_norm_sq_schwartzMap (FourierTransform.fourier G)

/-- Plancherel for the actual finite source `g`.  This uses the Schwartz
realization above, avoiding the currently absent general `L1 ∩ L2` bridge
between mathlib's pointwise Fourier integral and its abstract `Lp` transform. -/
theorem integral_norm_sq_fourier_sourceGFinite
    (m1Range m2Range m3Range : Finset ℤ)
    (psi1 : ℝ → ℂ) (f : 𝓢(ℝ, ℂ)) (M3 : ℝ)
    (hm1 : ∀ m1 ∈ m1Range, m1 ≠ 0)
    (hm2 : ∀ m2 ∈ m2Range, m2 ≠ 0) :
    (∫ xi : ℝ,
      ‖FourierTransform.fourier
        (sourceGFinite m1Range m2Range m3Range psi1
          (fun x => f x) M3) xi‖ ^ 2) =
      ∫ u : ℝ,
        ‖sourceGFinite m1Range m2Range m3Range psi1
          (fun x => f x) M3 u‖ ^ 2 := by
  let G : 𝓢(ℝ, ℂ) :=
    sourceGSchwartzFinite m1Range m2Range m3Range psi1 f M3 hm1 hm2
  have hG : (fun u : ℝ => G u) =
      sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3 := by
    funext u
    exact sourceGSchwartzFinite_apply
      m1Range m2Range m3Range psi1 f M3 hm1 hm2 u
  have hfourier : FourierTransform.fourier
      (sourceGFinite m1Range m2Range m3Range psi1 (fun x => f x) M3) =
        fun xi => FourierTransform.fourier G xi := by
    rw [← hG, ← SchwartzMap.fourier_coe]
  rw [hfourier, ← hG]
  exact SchwartzMap.integral_norm_sq_fourier G

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.sourceAffineSchwartz_apply
#print axioms GuthMaynardJIteration.sourceGSchwartzFinite_apply
#print axioms GuthMaynardJIteration.integrable_norm_sq_schwartzMap
#print axioms GuthMaynardJIteration.integrable_norm_sq_fourier_sourceGFinite
#print axioms GuthMaynardJIteration.integral_norm_sq_fourier_sourceGFinite
