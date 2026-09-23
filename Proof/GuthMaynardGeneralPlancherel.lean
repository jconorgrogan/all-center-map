import GuthMaynardJIterationFrequencyBounds
import Mathlib.Analysis.Fourier.Inversion

open scoped FourierTransform RealInnerProductSpace ComplexInnerProductSpace
  ComplexConjugate
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Pointwise Plancherel for the source profile class

The earlier finite-energy weld required a Schwartz representative of the
profile.  Proposition 9.1 assumes instead a continuous `L¹ ∩ L²` profile whose
pointwise Fourier transform decays rapidly.  Fourier inversion plus the
sesquilinear Fubini identity proves exactly the needed Plancherel formula under
those source hypotheses, without strengthening the profile to Schwartz.
-/

/-- Plancherel for a continuous integrable function whose pointwise Fourier
transform is integrable. -/
theorem integral_norm_sq_fourier_eq_of_integrable_fourier
    (f : ℝ → ℂ) (hf : Integrable f)
    (hfh : Integrable (FourierTransform.fourier f)) (hc : Continuous f) :
    (∫ x : ℝ, ‖FourierTransform.fourier f x‖ ^ 2) =
      ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hsesq :=
    (VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
      (innerSL ℂ) (L := innerₗ ℝ) Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hf hfh)
  have hneg :
      (fun x : ℝ => VectorFourier.fourierIntegral 𝐞 volume
        (-(innerₗ ℝ).flip) (FourierTransform.fourier f) x) =
        FourierTransform.fourierInv (FourierTransform.fourier f) := by
    funext x
    rw [Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with v
    congr 2
    simp
  have hnegPoint (x : ℝ) := congrFun hneg x
  simp_rw [hnegPoint] at hsesq
  have hsesq' :
      (∫ xi : ℝ, FourierTransform.fourier f xi *
        conj (FourierTransform.fourier f xi)) =
      ∫ x : ℝ, FourierTransform.fourierInv
        (FourierTransform.fourier f) x * conj (f x) := by
    simpa only [innerSL_apply_apply, RCLike.inner_apply, FourierTransform.fourier] using! hsesq
  have hinv : FourierTransform.fourierInv
      (FourierTransform.fourier f) = f :=
    hc.fourierInv_fourier_eq hf hfh
  rw [hinv] at hsesq'
  have hcomplex :
      (∫ xi : ℝ, ((‖FourierTransform.fourier f xi‖ ^ 2 : ℝ) : ℂ)) =
        ∫ x : ℝ, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq] using hsesq'
  norm_cast at hcomplex

/-- Fourth-order decay outside `[-1,1]` makes a continuous Fourier transform
integrable.  This is the exact bridge from the source rapid-decay quantifier
to Fourier inversion. -/
theorem integrable_of_continuous_fourier_decay_four
    (F : ℝ → ℂ) (hF : Continuous F) {K : ℝ}
    (hdecay : ∀ x, 1 ≤ |x| →
      ‖F x‖ ≤ K / (1 + |x|) ^ 4) :
    Integrable F := by
  let I : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hinside : IntegrableOn F I := hF.integrableOn_Icc
  have hmajor : Integrable
      (fun x : ℝ => K * quarticDecayEnvelope x) :=
    integrable_quarticDecayEnvelope.const_mul K
  have houtside : IntegrableOn F Iᶜ := by
    apply hmajor.integrableOn.mono'
      hF.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem (measurableSet_Icc.compl)] with x hx
    have habs : 1 ≤ |x| := by
      by_contra hnot
      apply hx
      rw [Set.mem_Icc, ← abs_le]
      exact le_of_not_ge hnot
    have h := hdecay x habs
    simpa [quarticDecayEnvelope, div_eq_mul_inv] using h
  have hunion := hinside.union houtside
  have hcover : I ∪ Iᶜ = Set.univ := Set.union_compl_self I
  rw [hcover] at hunion
  exact integrableOn_univ.mp hunion

/-- Source-ready Plancherel: continuity and `L¹`, plus one explicit
fourth-order pointwise Fourier envelope. -/
theorem integral_norm_sq_fourier_eq_of_decay_four
    (f : ℝ → ℂ) (hf : Integrable f) (hc : Continuous f)
    {K : ℝ}
    (hdecay : ∀ x, 1 ≤ |x| →
      ‖FourierTransform.fourier f x‖ ≤ K / (1 + |x|) ^ 4) :
    (∫ x : ℝ, ‖FourierTransform.fourier f x‖ ^ 2) =
      ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hF : Continuous (FourierTransform.fourier f) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  exact integral_norm_sq_fourier_eq_of_integrable_fourier f hf
    (integrable_of_continuous_fourier_decay_four
      (FourierTransform.fourier f) hF hdecay) hc

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.integral_norm_sq_fourier_eq_of_integrable_fourier
#print axioms GuthMaynardJIteration.integrable_of_continuous_fourier_decay_four
#print axioms GuthMaynardJIteration.integral_norm_sq_fourier_eq_of_decay_four
