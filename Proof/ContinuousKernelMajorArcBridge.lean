import MajorArcPrimePairWeld
import ContinuousKernelOverlap
import DyadicTentAmplitudeBridge

/-!
# Literal normalization bridge for the MAP continuous major-arc kernel

This module identifies the generic normalized-Haar kernel used in the finite
major-arc weld with the real-line beta kernel whose overlap and tails are
proved in `ContinuousKernelOverlap`.
-/

namespace MAPContinuousMajorArcBridge

open AddCircle MeasureTheory

noncomputable section

open MAPMajorArcWeld MAPContinuousOverlap
open MAPDyadicTentAmplitudeBridge

@[simp] theorem dyadicContinuousAmplitude_eq (X β : ℝ) :
    MAPMajorArcWeld.dyadicContinuousAmplitude X β = dyadicAmplitude X β := rfl

/-- Exact sign and normalization bridge: normalized-Haar `fourier (-h)` on
`ℝ/ℤ` is the real-line phase `exp(-2π i h β)`. -/
theorem fourier_neg_int_coe_eq_real_phase (h : ℤ) (β : ℝ) :
    fourier (-h) (β : UnitAddCircle) =
      Complex.exp (-2 * Real.pi * Complex.I * (((h : ℤ) : ℝ) * β)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The literal kernel in `MajorArcPrimePairWeld` is definitionally the
truncated dyadic beta kernel after the normalized-Haar phase is expanded. -/
theorem truncatedContinuousKernel_dyadic_eq
    (X R : ℝ) (h : ℤ) :
    MAPMajorArcWeld.truncatedContinuousKernel
        (MAPMajorArcWeld.dyadicContinuousAmplitude X) R h =
      truncatedDyadicBetaKernel X R (h : ℝ) := by
  unfold MAPMajorArcWeld.truncatedContinuousKernel truncatedDyadicBetaKernel
  apply intervalIntegral.integral_congr
  intro β hβ
  unfold oscillatoryKernelIntegrand
  unfold MAPMajorArcWeld.dyadicContinuousAmplitude dyadicAmplitude
  simp only [fourier_neg_int_coe_eq_real_phase]

/-- Direct theorem at the manuscript interface: the literal generic major-arc
continuous kernel has main term `X-|h|` and explicit beta-tail error. -/
theorem norm_truncatedContinuousKernel_dyadic_sub_overlap_le_of_wienerKhinchin
    (wienerKhinchin :
      ∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
        ∀ t : ℝ, spectralAutocorrelation f t = physicalAutocorrelation f t)
    {X R : ℝ} {h : ℤ} (hX : 0 ≤ X) (hh : |(h : ℝ)| ≤ X) (hR : 0 < R) :
    ‖MAPMajorArcWeld.truncatedContinuousKernel
        (MAPMajorArcWeld.dyadicContinuousAmplitude X) R h -
          ((X - |(h : ℝ)| : ℝ) : ℂ)‖ ≤
      2 / (Real.pi ^ 2 * R) := by
  rw [truncatedContinuousKernel_dyadic_eq]
  exact truncated_dyadic_beta_kernel_approximates_sub_abs_of_wienerKhinchin
    wienerKhinchin hX hh hR

/-- Final unconditional continuous-kernel theorem at the manuscript's literal
`MAPMajorArcWeld` interface. -/
theorem norm_truncatedContinuousKernel_dyadic_sub_overlap_le
    {X R : ℝ} {h : ℤ} (hX : 0 ≤ X) (hh : |(h : ℝ)| ≤ X) (hR : 0 < R) :
    ‖MAPMajorArcWeld.truncatedContinuousKernel
        (MAPMajorArcWeld.dyadicContinuousAmplitude X) R h -
          ((X - |(h : ℝ)| : ℝ) : ℂ)‖ ≤
      2 / (Real.pi ^ 2 * R) := by
  rw [truncatedContinuousKernel_dyadic_eq]
  exact truncatedDyadicBetaKernel_approximates_sub_abs hX hh hR

end

end MAPContinuousMajorArcBridge
