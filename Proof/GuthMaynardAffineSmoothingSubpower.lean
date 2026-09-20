import GuthMaynardAffineSmoothingNorms

open scoped BigOperators Real FourierTransform
open MeasureTheory

noncomputable section
namespace GuthMaynardJIteration

/-!
# Smoothing with a subpower-mass kernel

The bump in Guth--Maynard Lemma 9.2 is one-bounded but may have support and
mass `T^δ`.  It is therefore not a unit-mass kernel.  The Proposition 9.1
iteration needs the exact resulting loss, rather than the unit-mass closure
proved in `GuthMaynardAffineSmoothingNorms`.
-/

/-- A positive kernel whose mass is at most `K` enlarges a pointwise source
bound by at most the same factor. -/
theorem affineSmoothing_le_mass_mul
    {T S K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hf0 : ∀ u, 0 ≤ f u) (hf_le : ∀ u, f u ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hfCont : Continuous f) (x : ℝ) :
    affineSmoothing T psi f x ≤ K * S := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk : Integrable k := by
    simpa only [k] using
      (integrable_affineSmoothing_kernel hT hpsi).comp_sub_left x
  have hk0 : ∀ u, 0 ≤ k u := fun u => mul_nonneg hT.le (hpsi0 _)
  have hleft : Integrable (fun u => k u * f u) := by
    have hbound : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ S := by
      filter_upwards with u
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨(neg_nonpos.mpr hS).trans (hf0 u), hf_le u⟩
    exact (hk.bdd_mul hfCont.aestronglyMeasurable hbound).congr
      (Filter.Eventually.of_forall fun u => by ring)
  have hright : Integrable (fun u => k u * S) := hk.mul_const S
  have hmono : (∫ u : ℝ, k u * f u) ≤ ∫ u : ℝ, k u * S := by
    apply integral_mono_ae hleft hright
    filter_upwards with u
    exact mul_le_mul_of_nonneg_left (hf_le u) (hk0 u)
  calc
    affineSmoothing T psi f x = ∫ u : ℝ, k u * f u := by rfl
    _ ≤ ∫ u : ℝ, k u * S := hmono
    _ = (∫ z : ℝ, psi z) * S := by
      rw [integral_mul_const, integral_affineSmoothing_kernel hT psi x]
    _ ≤ K * S := mul_le_mul_of_nonneg_right hmass hS

/-- The Fourier transform of a nonnegative kernel of mass at most `K` has
norm at most `K`. -/
theorem norm_fourier_ofReal_le_mass
    (psi : ℝ → ℝ) (hpsi0 : ∀ z, 0 ≤ psi z)
    {K : ℝ} (hmass : ∫ z : ℝ, psi z ≤ K) (xi : ℝ) :
    ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤ K := by
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ) (fun z : ℝ => (psi z : ℂ)) xi
  change ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤
    ∫ z : ℝ, ‖(psi z : ℂ)‖ at hraw
  have hnorm : (∫ z : ℝ, ‖(psi z : ℂ)‖) = ∫ z : ℝ, psi z := by
    apply integral_congr_ae
    filter_upwards with z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpsi0 z)]
  rw [hnorm] at hraw
  exact hraw.trans hmass

/-- Exact source-ready `L¹` loss for a kernel of mass at most `K`. -/
theorem integral_affineSmoothing_le_mass_of_integrable
    {T K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf0 : ∀ u, 0 ≤ f u)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hf : Integrable f) :
    (∫ x : ℝ, affineSmoothing T psi f x) ≤
      K * ∫ u : ℝ, f u := by
  rw [integral_affineSmoothing hT psi f
    (integrable_affineSmoothing_product hT hpsi hf)]
  exact mul_le_mul_of_nonneg_right hmass (integral_nonneg hf0)

/-- Exact source-ready squared-`L²` loss for a kernel of mass at most `K`. -/
theorem integral_sq_affineSmoothing_le_mass_of_integrable
    {T K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hf2 : Integrable (fun u : ℝ => f u ^ 2)) :
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
      K ^ 2 * ∫ u : ℝ, f u ^ 2 := by
  have hmain := integral_sq_affineSmoothing_le hT psi f hpsi0 hf0
    hf.aestronglyMeasurable
    (fun x => (integrable_affineSmoothing_kernel hT hpsi).comp_sub_left x)
    (integrable_affineSmoothing_product hT hpsi hf2)
    (integrable_sq_affineSmoothing hT psi f hpsi0 hf0 hpsi hf hf2)
  have hmass0 : 0 ≤ ∫ z : ℝ, psi z := integral_nonneg hpsi0
  have hf20 : 0 ≤ ∫ u : ℝ, f u ^ 2 :=
    integral_nonneg fun u => sq_nonneg _
  calc
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := hmain
    _ ≤ K ^ 2 * ∫ u : ℝ, f u ^ 2 := by
      gcongr

/-- Rapid Fourier decay survives smoothing with the exact multiplicative
mass loss exposed in the new sup-norm parameter `K*S`. -/
theorem sourceFourierRapidDecay_affineSmoothing_mass
    {T S K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ K)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f)
    (hdecay : SourceFourierRapidDecay
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) T S) :
    SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ))) T (K * S) := by
  intro eta heta j
  obtain ⟨C, hC, hbound⟩ := hdecay eta heta j
  refine ⟨C, hC, ?_⟩
  intro z hz
  rw [fourier_ofReal_affineSmoothing hT psi f hpsi hf hpsiCont hfCont z,
    norm_mul]
  have hk := norm_fourier_ofReal_le_mass psi hpsi0 hmass (z / T)
  have hfz := hbound z hz
  have hrhs0 : 0 ≤ C * T ^ eta * (T / |z|) ^ j * S := by
    positivity
  calc
    ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) z‖ *
        ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (z / T)‖ ≤
      (C * T ^ eta * (T / |z|) ^ j * S) * K := by
        exact mul_le_mul hfz hk (norm_nonneg _) hrhs0
    _ = C * T ^ eta * (T / |z|) ^ j * (K * S) := by ring

/-- Full admissible-profile closure for a one-bounded positive kernel of mass
at most `K`.  This is the source-faithful replacement for the unit-mass orbit
when the Lemma 9.2 cutoff is allowed subpower support. -/
theorem sourceAdmissibleProfile_affineSmoothing_mass
    {T S F R K : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi0 : ∀ z, 0 ≤ psi z)
    (hpsiBound : ∀ z, psi z ≤ 1)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hpsiInt : Integrable psi) (hpsiCont : Continuous psi)
    (hmass : ∫ z : ℝ, psi z ≤ K) :
    SourceAdmissibleProfile T (K * S) (F + R / T)
      (affineSmoothing T psi f) := by
  refine
    { nonneg := ?_
      bounded := ?_
      supported := ?_
      integrable := integrable_affineSmoothing hT hpsiInt hf.integrable
      squareIntegrable := integrable_sq_affineSmoothing hT psi f hpsi0
        hf.nonneg hpsiInt hf.integrable hf.squareIntegrable
      continuous := ?_
      rapidDecay := ?_ }
  · intro x
    unfold affineSmoothing
    apply integral_nonneg
    intro u
    exact mul_nonneg (mul_nonneg hT.le (hpsi0 _)) (hf.nonneg u)
  · intro x
    exact affineSmoothing_le_mass_mul hT psi f hpsi0 hf.bound_nonneg
      hf.nonneg hf.bounded hmass hpsiInt hf.continuous x
  · intro x hx
    exact affineSmoothing_abs_support hT psi f hpsiSupport hf.supported hx
  · apply continuous_affineSmoothing hT psi f
    · intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (hpsi0 z)]
      exact hpsiBound z
    · exact hpsiCont
    · exact hf.integrable
  · exact sourceFourierRapidDecay_affineSmoothing_mass hT psi f hpsi0
      hf.bound_nonneg hmass hpsiInt hf.integrable hpsiCont hf.continuous
      hf.rapidDecay

end GuthMaynardJIteration

#print axioms GuthMaynardJIteration.affineSmoothing_le_mass_mul
#print axioms GuthMaynardJIteration.norm_fourier_ofReal_le_mass
#print axioms GuthMaynardJIteration.integral_affineSmoothing_le_mass_of_integrable
#print axioms GuthMaynardJIteration.integral_sq_affineSmoothing_le_mass_of_integrable
#print axioms GuthMaynardJIteration.sourceFourierRapidDecay_affineSmoothing_mass
#print axioms GuthMaynardJIteration.sourceAdmissibleProfile_affineSmoothing_mass
