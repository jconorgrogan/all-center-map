import ContinuousKernelOverlap
import DyadicTentFourier

namespace MAPDyadicTentAmplitudeBridge

open MeasureTheory Set
open scoped ComplexConjugate FourierTransform
open MAPContinuousOverlap MAPDyadicTentFourier

noncomputable section

/-- At nonzero frequency, the Fourier transform of the triangular overlap is
exactly the square norm of the dyadic interval amplitude. -/
theorem fourier_tent_eq_sq_norm_dyadicAmplitude
    {X β : ℝ} (hX : 0 ≤ X) (hβ : β ≠ 0) :
    FourierTransform.fourier (tent X) β =
      ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ) := by
  let k : ℂ := 2 * Real.pi * Complex.I * (β : ℂ)
  let A : ℂ := Complex.exp (k * (X : ℂ))
  have hk : k ≠ 0 := by
    dsimp [k]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr hβ)
  have hA : A ≠ 0 := Complex.exp_ne_zero _
  have hnorm :
      ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ) =
        dyadicAmplitude X β * dyadicAmplitude X (-β) := by
    rw [dyadicAmplitude_neg hX]
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj _).symm
  rw [fourier_tent_eq_formula hX hβ, hnorm,
    dyadicAmplitude_eq_quotient hβ,
    dyadicAmplitude_eq_quotient (neg_ne_zero.mpr hβ)]
  have hk2 : (2 * Real.pi * Complex.I * (β : ℂ)) = k := rfl
  have hnegk : (2 * Real.pi * Complex.I * ((-β : ℝ) : ℂ)) = -k := by
    dsimp [k]
    push_cast
    ring
  have h2 : Complex.exp (k * (2 * (X : ℂ))) = A ^ 2 := by
    rw [show k * (2 * (X : ℂ)) = k * (X : ℂ) + k * (X : ℂ) by ring,
      Complex.exp_add]
    simp [A, pow_two]
  have hn2 : Complex.exp ((-k) * (2 * (X : ℂ))) = A⁻¹ ^ 2 := by
    rw [show (-k) * (2 * (X : ℂ)) = -(k * (X : ℂ)) + -(k * (X : ℂ)) by
      ring, Complex.exp_add]
    simp only [Complex.exp_neg]
    simp [A, pow_two]
  have hnegX : Complex.exp ((-k) * (X : ℂ)) = A⁻¹ := by
    rw [show (-k) * (X : ℂ) = -(k * (X : ℂ)) by ring, Complex.exp_neg]
  have hfourierNeg :
      (-2 * Real.pi * Complex.I * (β : ℂ)) = -k := by
    dsimp [k]
    ring
  rw [hk2, hnegk]
  push_cast
  rw [h2, hn2, hnegX, hfourierNeg]
  rw [show Complex.exp (k * (X : ℂ)) = A by rfl]
  have hminusminus : Complex.exp ((-k) * (-(X : ℂ))) = A := by
    rw [show (-k) * (-(X : ℂ)) = k * (X : ℂ) by ring]
  rw [hminusminus]
  have hinv : Complex.exp (-(k * (X : ℂ))) = A⁻¹ := by
    rw [Complex.exp_neg]
  rw [hnegX]
  field_simp [hk, hA]
  ring

/-- The preceding identity holds almost everywhere; the single zero frequency
is null and therefore irrelevant for Fourier inversion and integrability. -/
theorem fourier_tent_ae_eq_sq_norm_dyadicAmplitude
    {X : ℝ} (hX : 0 ≤ X) :
    ∀ᵐ β : ℝ,
      FourierTransform.fourier (tent X) β =
        ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ) := by
  have hne : ∀ᵐ β : ℝ ∂volume, β ≠ 0 := by
    rw [ae_iff]
    simpa using (measure_singleton (0 : ℝ))
  filter_upwards [hne] with β hβ
  exact fourier_tent_eq_sq_norm_dyadicAmplitude hX hβ

/-- Unconditional full-line beta-kernel evaluation.  This closes the former
Wiener--Khinchin premise by an explicit tent transform and Mathlib's Fourier
inversion theorem. -/
theorem fullDyadicBetaKernel_eq_sub_abs
    {X h : ℝ} (hX : 0 ≤ X) (hh : |h| ≤ X) :
    fullDyadicBetaKernel X h = ((X - |h| : ℝ) : ℂ) := by
  have hae := fourier_tent_ae_eq_sq_norm_dyadicAmplitude hX
  have hsq : Integrable
      (fun β : ℝ => ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ)) :=
    (integrable_sq_norm_dyadicAmplitude hX).ofReal
  have hae' :
      (fun β : ℝ => ((‖dyadicAmplitude X β‖ ^ 2 : ℝ) : ℂ)) =ᵐ[volume]
        FourierTransform.fourier (tent X) := by
    filter_upwards [hae] with β hβ
    exact hβ.symm
  have hfourier : Integrable (FourierTransform.fourier (tent X)) :=
    hsq.congr hae'
  have hinversion :
      FourierTransformInv.fourierInv (FourierTransform.fourier (tent X)) (-h) =
        tent X (-h) :=
    (integrable_tent X hX).fourierInv_fourier_eq hfourier
      (continuous_tent X).continuousAt
  calc
    fullDyadicBetaKernel X h =
        ∫ β : ℝ, Real.fourierChar (β * (-h)) •
          FourierTransform.fourier (tent X) β := by
      unfold fullDyadicBetaKernel oscillatoryKernelIntegrand
      apply integral_congr_ae
      filter_upwards [hae] with β hβ
      rw [hβ, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
      rw [mul_comm]
      congr 1
      push_cast
      ring_nf
    _ = FourierTransformInv.fourierInv (FourierTransform.fourier (tent X)) (-h) := by
      rw [Real.fourierInv_eq]
      apply integral_congr_ae
      filter_upwards with β
      congr 2
      simp
      ring
    _ = tent X (-h) := hinversion
    _ = ((X - |h| : ℝ) : ℂ) := by
      unfold tent
      rw [abs_neg, max_eq_right (sub_nonneg.mpr hh)]

/-- The truncated beta kernel now has the exact overlap main term with no
external Fourier premise. -/
theorem truncatedDyadicBetaKernel_approximates_sub_abs
    {X R h : ℝ} (hX : 0 ≤ X) (hh : |h| ≤ X) (hR : 0 < R) :
    ‖truncatedDyadicBetaKernel X R h - ((X - |h| : ℝ) : ℂ)‖ ≤
      2 / (Real.pi ^ 2 * R) := by
  rw [← fullDyadicBetaKernel_eq_sub_abs hX hh, norm_sub_rev]
  exact norm_fullDyadicBetaKernel_sub_truncated_le hX hR

end

end MAPDyadicTentAmplitudeBridge
