import GuthMaynardJIterationAffineEnergy
import GuthMaynardJIterationFirstPoissonFourierShift
import GuthMaynardJIterationMediumRegionIntegration
import GuthMaynardJIterationSourceFourierDecay
import Mathlib.Analysis.Fourier.Convolution

open MeasureTheory
open scoped BigOperators Real FourierTransform Convolution

noncomputable section
namespace GuthMaynardJIteration

/-!
# Norm control for the smoothing in Guth--Maynard Proposition 9.1

This file formalizes the two norm comparisons used immediately after applying
Lemma 9.2 in the downward epsilon iteration.  The kernel is the literal source
normalization `T * psi (T * (x-u))` from `affineSmoothing`.
-/

/-- The scaled translate of the smoothing kernel has exactly the same mass as
`psi`.  This is the Jacobian cancellation behind the source normalization. -/
theorem integral_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (x : ℝ) :
    (∫ u : ℝ, T * psi (T * (x - u))) = ∫ z : ℝ, psi z := by
  have hchange := integral_affine_change_real psi (-T) (T * x)
  have habs : |(-T)⁻¹| = T⁻¹ := by
    rw [inv_neg, abs_neg, abs_inv, abs_of_pos hT]
  calc
    (∫ u : ℝ, T * psi (T * (x - u))) =
        T * ∫ u : ℝ, psi (T * x + (-T) * u) := by
      rw [integral_const_mul]
      apply congrArg (fun y : ℝ => T * y)
      apply integral_congr_ae
      filter_upwards with u
      congr 2
      ring
    _ = T * (|(-T)⁻¹| * ∫ z : ℝ, psi z) := by rw [hchange]
    _ = ∫ z : ℝ, psi z := by
      rw [habs]
      field_simp [hT.ne']

/-- The same mass identity with the integration variable in the first slot.
This is the orientation needed after the Fubini swap. -/
theorem integral_affineSmoothing_kernel_right
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (u : ℝ) :
    (∫ x : ℝ, T * psi (T * (x - u))) = ∫ z : ℝ, psi z := by
  have hchange := integral_affine_change_real psi T (-T * u)
  have habs : |T⁻¹| = T⁻¹ := by rw [abs_inv, abs_of_pos hT]
  calc
    (∫ x : ℝ, T * psi (T * (x - u))) =
        T * ∫ x : ℝ, psi (-T * u + T * x) := by
      rw [integral_const_mul]
      apply congrArg (fun y : ℝ => T * y)
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    _ = T * (|T⁻¹| * ∫ z : ℝ, psi z) := by rw [hchange]
    _ = ∫ z : ℝ, psi z := by
      rw [habs]
      field_simp [hT.ne']

/-- Weighted Cauchy--Schwarz in the exact form used for a positive smoothing
kernel. -/
theorem integral_weighted_mul_sq_le
    (k f : ℝ → ℝ)
    (hk0 : ∀ u, 0 ≤ k u)
    (hf0 : ∀ u, 0 ≤ f u)
    (hkmeas : AEStronglyMeasurable k)
    (hfmeas : AEStronglyMeasurable f)
    (hk : Integrable k)
    (hkf2 : Integrable (fun u => k u * f u ^ 2)) :
    (∫ u : ℝ, k u * f u) ^ 2 ≤
      (∫ u : ℝ, k u) * (∫ u : ℝ, k u * f u ^ 2) := by
  let a : ℝ → ℝ := fun u => Real.sqrt (k u)
  let b : ℝ → ℝ := fun u => Real.sqrt (k u) * f u
  have hameas : AEStronglyMeasurable a := by
    exact Real.continuous_sqrt.aestronglyMeasurable.comp_aemeasurable
      hkmeas.aemeasurable
  have hbmeas : AEStronglyMeasurable b := hameas.mul hfmeas
  have ha2 : Integrable (fun u => a u ^ 2) := by
    convert hk using 1
    funext u
    dsimp only [a]
    exact Real.sq_sqrt (hk0 u)
  have hb2 : Integrable (fun u => b u ^ 2) := by
    convert hkf2 using 1
    funext u
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hk0 u)]
  have hcs := integral_mul_sq_le a b hameas hbmeas ha2 hb2
    (fun _ => Real.sqrt_nonneg _)
    (fun u => mul_nonneg (Real.sqrt_nonneg _) (hf0 u))
  have hprod : (fun u => a u * b u) = (fun u => k u * f u) := by
    funext u
    dsimp only [a, b]
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (hk0 u)]
  have hka : (fun u => a u ^ 2) = k := by
    funext u
    exact Real.sq_sqrt (hk0 u)
  have hkfb : (fun u => b u ^ 2) = (fun u => k u * f u ^ 2) := by
    funext u
    dsimp only [b]
    rw [mul_pow, Real.sq_sqrt (hk0 u)]
  simpa only [hprod, hka, hkfb] using hcs

/-- Integrability of the scaled smoothing kernel. -/
theorem integrable_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) {psi : ℝ → ℝ} (hpsi : Integrable psi) :
    Integrable (fun y : ℝ => T * psi (T * y)) := by
  exact (hpsi.comp_mul_left' hT.ne').const_mul T

/-- The literal two-variable smoothing integrand is integrable whenever both
one-variable factors are.  This is the Fubini package used by the source. -/
theorem integrable_affineSmoothing_product
    {T : ℝ} (hT : 0 < T) {psi f : ℝ → ℝ}
    (hpsi : Integrable psi) (hf : Integrable f) :
    Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u) (volume.prod volume) := by
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  have hk : Integrable k := integrable_affineSmoothing_kernel hT hpsi
  have hconv := hf.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) hk
  simpa only [k, mul_comm] using hconv

/-- The source smoothing is literally convolution with the scaled kernel. -/
theorem affineSmoothing_eq_convolution
    (T : ℝ) (psi f : ℝ → ℝ) :
    affineSmoothing T psi f = MeasureTheory.convolution f
      (fun y : ℝ => T * psi (T * y))
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  unfold affineSmoothing
  apply integral_congr_ae
  filter_upwards with u
  rw [ContinuousLinearMap.mul_apply']
  ring

/-- The smoothing orbit remains in `L¹`; this is the exact source profile
closure needed before Lemma 9.2 is iterated. -/
theorem integrable_affineSmoothing
    {T : ℝ} (hT : 0 < T) {psi f : ℝ → ℝ}
    (hpsi : Integrable psi) (hf : Integrable f) :
    Integrable (affineSmoothing T psi f) := by
  rw [affineSmoothing_eq_convolution]
  exact hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ)
    (integrable_affineSmoothing_kernel hT hpsi)

/-- Every fixed section of the literal smoothing kernel is integrable against
a bounded continuous profile.  This is the source-facing regularity premise
used inside each localized second-Poisson fiber. -/
theorem integrable_affineSmoothing_section
    {T S : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi : Integrable psi) (hfCont : Continuous f)
    (hS : 0 ≤ S) (hfBound : ∀ u, |f u| ≤ S) (x : ℝ) :
    Integrable (fun u => T * psi (T * (x - u)) * f u) := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk : Integrable k := by
    simpa only [k] using
      (integrable_affineSmoothing_kernel hT hpsi).comp_sub_left x
  have hbound : ∀ᵐ u : ℝ ∂volume, ‖f u‖ ≤ S := by
    filter_upwards with u
    simpa only [Real.norm_eq_abs] using hfBound u
  exact (hk.bdd_mul hfCont.aestronglyMeasurable hbound).congr
    (Filter.Eventually.of_forall fun u => by
      dsimp only [k]
      ring)

/-- A positive kernel of mass at most one preserves a pointwise upper bound.
This supplies the `sup f` normalization used at every iteration of
Proposition 9.1. -/
theorem affineSmoothing_le_of_le
    {T S : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hS : 0 ≤ S)
    (hf0 : ∀ u, 0 ≤ f u)
    (hf_le : ∀ u, f u ≤ S)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hpsi : Integrable psi) (hfCont : Continuous f) (x : ℝ) :
    affineSmoothing T psi f x ≤ S := by
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
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hmass hS
    _ = S := one_mul S

/-- Continuity of the smoothing orbit from an integrable source profile and a
continuous bounded kernel. -/
theorem continuous_affineSmoothing
    {T P : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiBound : ∀ z, ‖psi z‖ ≤ P)
    (hpsiCont : Continuous psi) (hf : Integrable f) :
    Continuous (affineSmoothing T psi f) := by
  rw [affineSmoothing_eq_convolution]
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  have hkCont : Continuous k := by
    exact continuous_const.mul
      (hpsiCont.comp (continuous_const.mul continuous_id))
  have hkbdd : BddAbove (Set.range fun y => ‖k y‖) := by
    refine ⟨T * P, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp only [k]
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left (hpsiBound (T * y)) hT.le
  exact hkbdd.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.mul ℝ ℝ) hf hkCont

/-- Complexification commutes with the source smoothing and turns it into the
complex convolution used by the Fourier convolution theorem. -/
theorem ofReal_affineSmoothing_eq_complexConvolution
    (T : ℝ) (psi f : ℝ → ℝ) :
    (fun x : ℝ => (affineSmoothing T psi f x : ℂ)) =
      MeasureTheory.convolution (fun u : ℝ => (f u : ℂ))
        (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ))
        (ContinuousLinearMap.mul ℂ ℂ) volume := by
  funext x
  rw [MeasureTheory.convolution_def]
  unfold affineSmoothing
  calc
    ((∫ u : ℝ, T * psi (T * (x - u)) * f u : ℝ) : ℂ) =
        ∫ u : ℝ, ((T * psi (T * (x - u)) * f u : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = ∫ t : ℝ, (ContinuousLinearMap.mul ℂ ℂ) (f t : ℂ)
          ((T * psi (T * (x - t)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [ContinuousLinearMap.mul_apply']
      push_cast
      ring

/-- The normalized scaled smoothing kernel has Fourier transform
`psiHat(xi/T)` with no residual Jacobian. -/
theorem fourier_scaled_affineSmoothing_kernel
    {T : ℝ} (hT : 0 < T) (psi : ℝ → ℝ) (xi : ℝ) :
    FourierTransform.fourier
        (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ)) xi =
      FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) := by
  have hfun : (fun y : ℝ => ((T * psi (T * y) : ℝ) : ℂ)) =
      (fun y : ℝ => (T : ℂ) * (psi (T * y) : ℂ)) := by
    funext y
    push_cast
    rfl
  rw [hfun, source_fourier_const_mul]
  rw [fourier_dilation (fun z : ℝ => (psi z : ℂ)) hT.ne' xi]
  have habs : |T⁻¹| = T⁻¹ := by rw [abs_inv, abs_of_pos hT]
  rw [habs]
  rw [Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hT.ne']
  norm_num

/-- Exact Fourier multiplier identity for the smoothing orbit used in the
Proposition 9.1 induction. -/
theorem fourier_ofReal_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f) (xi : ℝ) :
    FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ)) xi =
      FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi *
        FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) := by
  let kR : ℝ → ℝ := fun y => T * psi (T * y)
  let fC : ℝ → ℂ := fun u => (f u : ℂ)
  let kC : ℝ → ℂ := fun y => (kR y : ℂ)
  have hkR : Integrable kR := integrable_affineSmoothing_kernel hT hpsi
  have hfC : Integrable fC := hf.ofReal
  have hkC : Integrable kC := hkR.ofReal
  have hfCCont : Continuous fC := Complex.continuous_ofReal.comp hfCont
  have hkRCont : Continuous kR := by
    exact continuous_const.mul
      (hpsiCont.comp (continuous_const.mul continuous_id))
  have hkCCont : Continuous kC := Complex.continuous_ofReal.comp hkRCont
  rw [ofReal_affineSmoothing_eq_complexConvolution]
  rw [Real.fourier_mul_convolution_eq hfC hkC hfCCont hkCCont xi]
  change FourierTransform.fourier fC xi * FourierTransform.fourier kC xi = _
  rw [show FourierTransform.fourier kC xi =
      FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) (xi / T) by
    exact fourier_scaled_affineSmoothing_kernel hT psi xi]

/-- A nonnegative unit-mass kernel has Fourier transform bounded by one. -/
theorem norm_fourier_ofReal_le_one
    (psi : ℝ → ℝ) (hpsi0 : ∀ z, 0 ≤ psi z)
    (hmass : ∫ z : ℝ, psi z ≤ 1) (xi : ℝ) :
    ‖FourierTransform.fourier (fun z : ℝ => (psi z : ℂ)) xi‖ ≤ 1 := by
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

/-- Smoothing by a positive unit-mass kernel cannot enlarge any Fourier
coefficient.  Hence every rapid-decay envelope assumed in Proposition 9.1 is
inherited by the next smoothing iterate without a new constant. -/
theorem norm_fourier_ofReal_affineSmoothing_le
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f) (xi : ℝ) :
    ‖FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ)) xi‖ ≤
      ‖FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi‖ := by
  rw [fourier_ofReal_affineSmoothing hT psi f hpsi hf hpsiCont hfCont xi,
    norm_mul]
  have hk := norm_fourier_ofReal_le_one psi hpsi0 hmass (xi / T)
  nlinarith [norm_nonneg
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ)) xi)]

/-- The exact quantified rapid-decay class of Proposition 9.1 is closed under
the smoothing orbit.  The same seminorm constant works at every order and
loss exponent because the Fourier multiplier has norm at most one. -/
theorem sourceFourierRapidDecay_affineSmoothing
    {T S : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hpsiCont : Continuous psi) (hfCont : Continuous f)
    (hdecay : SourceFourierRapidDecay
      (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) T S) :
    SourceFourierRapidDecay
      (FourierTransform.fourier
        (fun x : ℝ => (affineSmoothing T psi f x : ℂ))) T S := by
  intro eta heta j
  obtain ⟨C, hC, hbound⟩ := hdecay eta heta j
  refine ⟨C, hC, ?_⟩
  intro z hz
  exact (norm_fourier_ofReal_affineSmoothing_le hT psi f hpsi0 hmass
    hpsi hf hpsiCont hfCont z).trans (hbound z hz)

/-- A compact support interval for `f` and a radius support for `psi` give the
exact left endpoint of the enlarged smoothing support. -/
theorem affineSmoothing_eq_zero_of_lt_support
    {T a b R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b)
    (hx : x < a - R / T) :
    affineSmoothing T psi f x = 0 := by
  unfold affineSmoothing
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hfu : f u = 0
  · simp [hfu]
  by_cases hpsi : psi (T * (x - u)) = 0
  · simp [hpsi]
  have hker := hpsiSupport (T * (x - u)) hpsi
  have habsT : T * |x - u| ≤ R := by
    simpa only [abs_mul, abs_of_pos hT] using hker
  have habs : |x - u| ≤ R / T := (le_div_iff₀ hT).2 (by
    simpa [mul_comm] using habsT)
  have hu := (hfSupport u hfu).1
  have hleft := neg_le_of_abs_le habs
  exfalso
  linarith

/-- The matching right endpoint of the enlarged smoothing support. -/
theorem affineSmoothing_eq_zero_of_support_lt
    {T a b R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b)
    (hx : b + R / T < x) :
    affineSmoothing T psi f x = 0 := by
  unfold affineSmoothing
  apply integral_eq_zero_of_ae
  filter_upwards with u
  by_cases hfu : f u = 0
  · simp [hfu]
  by_cases hpsi : psi (T * (x - u)) = 0
  · simp [hpsi]
  have hker := hpsiSupport (T * (x - u)) hpsi
  have habsT : T * |x - u| ≤ R := by
    simpa only [abs_mul, abs_of_pos hT] using hker
  have habs : |x - u| ≤ R / T := (le_div_iff₀ hT).2 (by
    simpa [mul_comm] using habsT)
  have hu := (hfSupport u hfu).2
  have hright := le_of_abs_le habs
  exfalso
  linarith

/-- Exact interval support enlargement for the affine smoothing. -/
theorem affineSmoothing_support_interval
    {T a b R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → a ≤ u ∧ u ≤ b)
    (hx : x ∉ Set.Icc (a - R / T) (b + R / T)) :
    affineSmoothing T psi f x = 0 := by
  rw [Set.mem_Icc, not_and_or] at hx
  rcases hx with hx | hx
  · exact affineSmoothing_eq_zero_of_lt_support hT psi f hpsiSupport
      hfSupport (lt_of_not_ge hx)
  · exact affineSmoothing_eq_zero_of_support_lt hT psi f hpsiSupport
      hfSupport (lt_of_not_ge hx)

/-- Symmetric support form used in the finite affine-range construction. -/
theorem affineSmoothing_abs_support
    {T F R x : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ u, f u ≠ 0 → |u| ≤ F)
    (hx : affineSmoothing T psi f x ≠ 0) :
    |x| ≤ F + R / T := by
  rw [abs_le]
  constructor
  · by_contra hleft
    apply hx
    apply affineSmoothing_eq_zero_of_lt_support hT psi f hpsiSupport
      (fun u hu => (abs_le.mp (hfSupport u hu)))
    have : x < -(F + R / T) := lt_of_not_ge hleft
    linarith
  · by_contra hright
    apply hx
    apply affineSmoothing_eq_zero_of_support_lt hT psi f hpsiSupport
      (fun u hu => (abs_le.mp (hfSupport u hu)))
    exact lt_of_not_ge hright

/-- The support-driven finite `j` window from `sourceAffineSupport_implies_j_mem_window`
applies directly to the next smoothing iterate with radius `F+R/T`. -/
theorem affineSmoothing_support_implies_j_mem_window
    {T F R U Mhi u : ℝ} (hT : 0 < T)
    (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ x, f x ≠ 0 → |x| ≤ F)
    (hMhi : 0 ≤ Mhi) (hu : |u| ≤ U)
    {m1 m2 j : ℤ} (hm2 : m2 ≠ 0)
    (hm1hi : |(m1 : ℝ)| ≤ Mhi) (hm2hi : |(m2 : ℝ)| ≤ Mhi)
    (hnonzero : affineSmoothing T psi f
      (((m1 : ℝ) * u + (j : ℝ)) / (m2 : ℝ)) ≠ 0) :
    j ∈ sourceIntegerWindow 0 (Mhi * (F + R / T + U)) := by
  apply sourceAffineSupport_implies_j_mem_window
    (affineSmoothing T psi f) hMhi hu hm2 hm1hi hm2hi
    (fun x hx => affineSmoothing_abs_support hT psi f hpsiSupport
      hfSupport hx)
    hnonzero

/-- The affine integer series occurring in `SigmaII` is automatically
summable once the smoothed profile has the certified compact support. -/
theorem summable_affineSmoothing_sourceAffineCenter
    {T F R : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsiSupport : ∀ z, psi z ≠ 0 → |z| ≤ R)
    (hfSupport : ∀ x, f x ≠ 0 → |x| ≤ F)
    {m2 m2' : ℤ} (hm2' : m2' ≠ 0) (u : ℝ) :
    Summable (fun j : ℤ => affineSmoothing T psi f
      (sourceAffineCenter (m2 : ℝ) (m2' : ℝ) u j)) := by
  let Mhi : ℝ := max |(m2 : ℝ)| |(m2' : ℝ)|
  let J : Finset ℤ := sourceIntegerWindow 0
    (Mhi * (F + R / T + |u|))
  apply summable_of_ne_finset_zero (s := J)
  intro j hj
  by_contra hnonzero
  apply hj
  have hjmem := affineSmoothing_support_implies_j_mem_window
    hT psi f hpsiSupport hfSupport (show 0 ≤ Mhi by
      exact (abs_nonneg (m2 : ℝ)).trans (le_max_left _ _))
    (show |u| ≤ |u| by rfl) hm2'
    (show |(m2 : ℝ)| ≤ Mhi by exact le_max_left _ _)
    (show |(m2' : ℝ)| ≤ Mhi by exact le_max_right _ _)
    (by simpa only [sourceAffineCenter] using hnonzero)
  exact hjmem

/-- Exact `L¹` mass of the smoothing, with the Fubini condition stated on the
literal two-variable kernel. -/
theorem integral_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hprod : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u) (volume.prod volume)) :
    (∫ x : ℝ, affineSmoothing T psi f x) =
      (∫ z : ℝ, psi z) * ∫ u : ℝ, f u := by
  unfold affineSmoothing
  calc
    (∫ x : ℝ, ∫ u : ℝ, T * psi (T * (x - u)) * f u) =
        ∫ u : ℝ, ∫ x : ℝ, T * psi (T * (x - u)) * f u :=
      integral_integral_swap hprod
    _ = ∫ u : ℝ, (∫ z : ℝ, psi z) * f u := by
      apply integral_congr_ae
      filter_upwards with u
      calc
        (∫ x : ℝ, T * psi (T * (x - u)) * f u) =
            (∫ x : ℝ, T * psi (T * (x - u))) * f u := by
          rw [integral_mul_const]
        _ = (∫ z : ℝ, psi z) * f u := by
          rw [integral_affineSmoothing_kernel_right hT psi u]
    _ = (∫ z : ℝ, psi z) * ∫ u : ℝ, f u := by
      rw [integral_const_mul]

/-- Unit-mass kernels do not increase the `L¹` mass of a nonnegative source. -/
theorem integral_affineSmoothing_le
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf0 : ∀ u, 0 ≤ f u)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hprod : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u) (volume.prod volume)) :
    (∫ x : ℝ, affineSmoothing T psi f x) ≤ ∫ u : ℝ, f u := by
  rw [integral_affineSmoothing hT psi f hprod]
  have hfintegral : 0 ≤ ∫ u : ℝ, f u :=
    integral_nonneg fun u => hf0 u
  nlinarith

/-- Source-ready `L¹` contraction: ordinary integrability of the profile and
kernel discharges the Fubini premise automatically. -/
theorem integral_affineSmoothing_le_of_integrable
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf0 : ∀ u, 0 ≤ f u)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hpsi : Integrable psi) (hf : Integrable f) :
    (∫ x : ℝ, affineSmoothing T psi f x) ≤ ∫ u : ℝ, f u := by
  exact integral_affineSmoothing_le hT psi f hf0 hmass
    (integrable_affineSmoothing_product hT hpsi hf)

/-- Pointwise weighted Cauchy--Schwarz for the literal affine smoothing. -/
theorem affineSmoothing_sq_le_kernelMass_mul
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hfmeas : AEStronglyMeasurable f)
    (x : ℝ)
    (hk : Integrable (fun u : ℝ => T * psi (T * (x - u))))
    (hkf2 : Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2)) :
    affineSmoothing T psi f x ^ 2 ≤
      (∫ z : ℝ, psi z) *
        ∫ u : ℝ, T * psi (T * (x - u)) * f u ^ 2 := by
  let k : ℝ → ℝ := fun u => T * psi (T * (x - u))
  have hk0 : ∀ u, 0 ≤ k u := fun u =>
    mul_nonneg hT.le (hpsi0 (T * (x - u)))
  have hweighted := integral_weighted_mul_sq_le k f hk0 hf0
    hk.aestronglyMeasurable hfmeas hk hkf2
  unfold affineSmoothing
  rw [integral_affineSmoothing_kernel hT psi x] at hweighted
  exact hweighted

/-- The `L²` contraction used in the Proposition 9.1 iteration.  The stated
integrability hypotheses are precisely the Fubini/Bochner obligations; the
inequality itself has no hidden constant. -/
theorem integral_sq_affineSmoothing_le
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hfmeas : AEStronglyMeasurable f)
    (hkernel : ∀ x, Integrable (fun u : ℝ =>
      T * psi (T * (x - u))))
    (hprodF2 : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) (volume.prod volume))
    (hsmooth2 : Integrable (fun x : ℝ =>
      affineSmoothing T psi f x ^ 2)) :
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
      (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := by
  let mass : ℝ := ∫ z : ℝ, psi z
  let F2 : ℝ → ℝ := fun u => f u ^ 2
  have hmass0 : 0 ≤ mass := integral_nonneg hpsi0
  have hinner : Integrable (fun x : ℝ =>
      ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) := by
    exact hprodF2.integral_prod_left
  have hrhs : Integrable (fun x : ℝ =>
      mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hinner.const_mul mass
  have hkernelF2 : ∀ᵐ x : ℝ, Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) := hprodF2.prod_right_ae
  have hmono :
      (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        ∫ x : ℝ, mass *
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := by
    apply integral_mono_ae hsmooth2 hrhs
    filter_upwards [hkernelF2] with x hx
    simpa only [mass, F2] using
      affineSmoothing_sq_le_kernelMass_mul hT psi f hpsi0 hf0 hfmeas x
        (hkernel x) hx
  have hmassF2 :
      (∫ x : ℝ, ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) =
        mass * ∫ u : ℝ, F2 u := by
    simpa only [mass, F2, affineSmoothing] using
      integral_affineSmoothing hT psi F2 hprodF2
  calc
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        ∫ x : ℝ, mass *
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := hmono
    _ = mass * (∫ x : ℝ,
          ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) := by
      rw [integral_const_mul]
    _ = mass * (mass * ∫ u : ℝ, F2 u) := by rw [hmassF2]
    _ = (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := by
      dsimp only [mass, F2]
      ring

/-- Unit-mass positive kernels do not increase the squared `L²` mass. -/
theorem integral_sq_affineSmoothing_le_one
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hfmeas : AEStronglyMeasurable f)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hkernel : ∀ x, Integrable (fun u : ℝ =>
      T * psi (T * (x - u))))
    (hprodF2 : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) (volume.prod volume))
    (hsmooth2 : Integrable (fun x : ℝ =>
      affineSmoothing T psi f x ^ 2)) :
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
      ∫ u : ℝ, f u ^ 2 := by
  have hmain := integral_sq_affineSmoothing_le hT psi f hpsi0 hf0 hfmeas
    hkernel hprodF2 hsmooth2
  have hm0 : 0 ≤ ∫ z : ℝ, psi z := integral_nonneg hpsi0
  have hf20 : 0 ≤ ∫ u : ℝ, f u ^ 2 :=
    integral_nonneg fun u => sq_nonneg (f u)
  calc
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
        (∫ z : ℝ, psi z) ^ 2 * ∫ u : ℝ, f u ^ 2 := hmain
    _ ≤ 1 * ∫ u : ℝ, f u ^ 2 := by
      gcongr
      nlinarith
    _ = ∫ u : ℝ, f u ^ 2 := one_mul _

/-- Ordinary `L¹/L²` integrability of the source and `L¹` integrability of the
positive kernel imply that the squared smoothing itself is integrable. -/
theorem integrable_sq_affineSmoothing
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hf2 : Integrable (fun u : ℝ => f u ^ 2)) :
    Integrable (fun x : ℝ => affineSmoothing T psi f x ^ 2) := by
  let k : ℝ → ℝ := fun y => T * psi (T * y)
  let mass : ℝ := ∫ z : ℝ, psi z
  let F2 : ℝ → ℝ := fun u => f u ^ 2
  have hk : Integrable k := integrable_affineSmoothing_kernel hT hpsi
  have hkernel : ∀ x, Integrable (fun u : ℝ =>
      T * psi (T * (x - u))) := by
    intro x
    simpa only [k] using hk.comp_sub_left x
  have hprodF2 : Integrable (Function.uncurry fun x u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) (volume.prod volume) :=
    integrable_affineSmoothing_product hT hpsi hf2
  have hinner : Integrable (fun x : ℝ =>
      ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hprodF2.integral_prod_left
  have hrhs : Integrable (fun x : ℝ =>
      mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u) :=
    hinner.const_mul mass
  have hkernelF2 : ∀ᵐ x : ℝ, Integrable (fun u : ℝ =>
      T * psi (T * (x - u)) * f u ^ 2) := hprodF2.prod_right_ae
  have hpoint : ∀ᵐ x : ℝ,
      affineSmoothing T psi f x ^ 2 ≤
        mass * ∫ u : ℝ, T * psi (T * (x - u)) * F2 u := by
    filter_upwards [hkernelF2] with x hx
    simpa only [mass, F2] using
      affineSmoothing_sq_le_kernelMass_mul hT psi f hpsi0 hf0
        hf.aestronglyMeasurable x (hkernel x) hx
  have hconv : Integrable (MeasureTheory.convolution f k
      (ContinuousLinearMap.mul ℝ ℝ) volume) :=
    hf.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hk
  have hsmoothMeas : AEStronglyMeasurable
      (fun x : ℝ => affineSmoothing T psi f x ^ 2) := by
    rw [affineSmoothing_eq_convolution T psi f]
    simpa only [k] using hconv.aestronglyMeasurable.pow 2
  apply hrhs.mono' hsmoothMeas
  filter_upwards [hpoint] with x hx
  have hlhs0 : 0 ≤ affineSmoothing T psi f x ^ 2 := sq_nonneg _
  have hinner0 : 0 ≤ ∫ u : ℝ,
      T * psi (T * (x - u)) * F2 u := by
    apply integral_nonneg
    intro u
    exact mul_nonneg (mul_nonneg hT.le (hpsi0 _)) (sq_nonneg _)
  have hrhs0 : 0 ≤ mass * ∫ u : ℝ,
      T * psi (T * (x - u)) * F2 u :=
    mul_nonneg (integral_nonneg hpsi0) hinner0
  simpa only [Real.norm_eq_abs, abs_of_nonneg hlhs0, abs_of_nonneg hrhs0] using hx

/-- Fully source-ready normalized squared-`L²` contraction. -/
theorem integral_sq_affineSmoothing_le_one_of_integrable
    {T : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hpsi0 : ∀ z, 0 ≤ psi z) (hf0 : ∀ u, 0 ≤ f u)
    (hmass : ∫ z : ℝ, psi z ≤ 1)
    (hpsi : Integrable psi) (hf : Integrable f)
    (hf2 : Integrable (fun u : ℝ => f u ^ 2)) :
    (∫ x : ℝ, affineSmoothing T psi f x ^ 2) ≤
      ∫ u : ℝ, f u ^ 2 := by
  apply integral_sq_affineSmoothing_le_one hT psi f hpsi0 hf0
    hf.aestronglyMeasurable hmass
  · intro x
    have hk := integrable_affineSmoothing_kernel hT hpsi
    exact hk.comp_sub_left x
  · exact integrable_affineSmoothing_product hT hpsi hf2
  · exact integrable_sq_affineSmoothing hT psi f hpsi0 hf0 hpsi hf hf2

/-! ## One-package closure of the Proposition 9.1 profile class -/

structure SourceAdmissibleProfile
    (T S F : ℝ) (f : ℝ → ℝ) : Prop where
  nonneg : ∀ u, 0 ≤ f u
  bounded : ∀ u, f u ≤ S
  supported : ∀ u, f u ≠ 0 → |u| ≤ F
  integrable : Integrable f
  squareIntegrable : Integrable (fun u => f u ^ 2)
  continuous : Continuous f
  rapidDecay : SourceFourierRapidDecay
    (FourierTransform.fourier (fun u : ℝ => (f u : ℂ))) T S

structure SourceSmoothingKernel (R : ℝ) (psi : ℝ → ℝ) : Prop where
  nonneg : ∀ z, 0 ≤ psi z
  bounded : ∀ z, psi z ≤ 1
  supported : ∀ z, psi z ≠ 0 → |z| ≤ R
  integrable : Integrable psi
  continuous : Continuous psi
  mass_le_one : ∫ z : ℝ, psi z ≤ 1

theorem SourceAdmissibleProfile.bound_nonneg
    {T S F : ℝ} {f : ℝ → ℝ} (hf : SourceAdmissibleProfile T S F f) :
    0 ≤ S :=
  (hf.nonneg 0).trans (hf.bounded 0)

/-- Every field of the source admissibility package survives one literal
smoothing step, with only the explicit support-radius enlargement `R/T`. -/
theorem sourceAdmissibleProfile_affineSmoothing
    {T S F R : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi) :
    SourceAdmissibleProfile T S (F + R / T)
      (affineSmoothing T psi f) := by
  refine
    { nonneg := ?_
      bounded := ?_
      supported := ?_
      integrable := integrable_affineSmoothing hT hpsi.integrable hf.integrable
      squareIntegrable := integrable_sq_affineSmoothing hT psi f hpsi.nonneg
        hf.nonneg hpsi.integrable hf.integrable hf.squareIntegrable
      continuous := ?_
      rapidDecay := ?_ }
  · intro x
    unfold affineSmoothing
    apply integral_nonneg
    intro u
    exact mul_nonneg (mul_nonneg hT.le (hpsi.nonneg _)) (hf.nonneg u)
  · intro x
    exact affineSmoothing_le_of_le hT psi f hpsi.nonneg
      (le_trans (hf.nonneg x) (hf.bounded x)) hf.nonneg hf.bounded
      hpsi.mass_le_one hpsi.integrable hf.continuous x
  · intro x hx
    exact affineSmoothing_abs_support hT psi f hpsi.supported hf.supported hx
  · apply continuous_affineSmoothing hT psi f
    · intro z
      rw [Real.norm_eq_abs, abs_of_nonneg (hpsi.nonneg z)]
      exact hpsi.bounded z
    · exact hpsi.continuous
    · exact hf.integrable
  · exact sourceFourierRapidDecay_affineSmoothing hT psi f hpsi.nonneg
      hpsi.mass_le_one hpsi.integrable hf.integrable hpsi.continuous
      hf.continuous hf.rapidDecay

def affineSmoothingIterate (T : ℝ) (psi : ℝ → ℝ) :
    ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => affineSmoothing T psi (affineSmoothingIterate T psi n f)

/-- The full finite smoothing orbit used by the downward-epsilon induction is
admissible uniformly at every depth.  Only the support radius accumulates,
linearly and explicitly. -/
theorem sourceAdmissibleProfile_affineSmoothingIterate
    {T S F R : ℝ} (hT : 0 < T) (psi f : ℝ → ℝ)
    (hf : SourceAdmissibleProfile T S F f)
    (hpsi : SourceSmoothingKernel R psi) (n : ℕ) :
    SourceAdmissibleProfile T S (F + (n : ℝ) * (R / T))
      (affineSmoothingIterate T psi n f) := by
  induction n with
  | zero => simpa [affineSmoothingIterate] using hf
  | succ n ih =>
      have hstep := sourceAdmissibleProfile_affineSmoothing hT psi
        (affineSmoothingIterate T psi n f) ih hpsi
      convert hstep using 1 <;> simp [affineSmoothingIterate] <;> ring

#print axioms GuthMaynardJIteration.integral_affineSmoothing_kernel
#print axioms GuthMaynardJIteration.integral_affineSmoothing_kernel_right
#print axioms GuthMaynardJIteration.integral_weighted_mul_sq_le
#print axioms GuthMaynardJIteration.integrable_affineSmoothing_kernel
#print axioms GuthMaynardJIteration.integrable_affineSmoothing_product
#print axioms GuthMaynardJIteration.affineSmoothing_eq_convolution
#print axioms GuthMaynardJIteration.integrable_affineSmoothing
#print axioms GuthMaynardJIteration.integrable_affineSmoothing_section
#print axioms GuthMaynardJIteration.affineSmoothing_le_of_le
#print axioms GuthMaynardJIteration.continuous_affineSmoothing
#print axioms GuthMaynardJIteration.ofReal_affineSmoothing_eq_complexConvolution
#print axioms GuthMaynardJIteration.fourier_scaled_affineSmoothing_kernel
#print axioms GuthMaynardJIteration.fourier_ofReal_affineSmoothing
#print axioms GuthMaynardJIteration.norm_fourier_ofReal_le_one
#print axioms GuthMaynardJIteration.norm_fourier_ofReal_affineSmoothing_le
#print axioms GuthMaynardJIteration.sourceFourierRapidDecay_affineSmoothing
#print axioms GuthMaynardJIteration.affineSmoothing_eq_zero_of_lt_support
#print axioms GuthMaynardJIteration.affineSmoothing_eq_zero_of_support_lt
#print axioms GuthMaynardJIteration.affineSmoothing_support_interval
#print axioms GuthMaynardJIteration.affineSmoothing_abs_support
#print axioms GuthMaynardJIteration.affineSmoothing_support_implies_j_mem_window
#print axioms GuthMaynardJIteration.summable_affineSmoothing_sourceAffineCenter
#print axioms GuthMaynardJIteration.integral_affineSmoothing
#print axioms GuthMaynardJIteration.integral_affineSmoothing_le
#print axioms GuthMaynardJIteration.integral_affineSmoothing_le_of_integrable
#print axioms GuthMaynardJIteration.affineSmoothing_sq_le_kernelMass_mul
#print axioms GuthMaynardJIteration.integral_sq_affineSmoothing_le
#print axioms GuthMaynardJIteration.integral_sq_affineSmoothing_le_one
#print axioms GuthMaynardJIteration.integrable_sq_affineSmoothing
#print axioms GuthMaynardJIteration.integral_sq_affineSmoothing_le_one_of_integrable
#print axioms GuthMaynardJIteration.sourceAdmissibleProfile_affineSmoothing
#print axioms GuthMaynardJIteration.sourceAdmissibleProfile_affineSmoothingIterate
#print axioms GuthMaynardJIteration.SourceAdmissibleProfile.bound_nonneg

end GuthMaynardJIteration
