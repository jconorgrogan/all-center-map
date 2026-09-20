import MAPFinishP51LowIdentity
import MRTFaithfulSmoothCutoffBudgets

/-!
# Faithful-cutoff low projection identity

This instantiates the source's exact low-frequency Fubini/change-of-variables
identity with the same cutoff already used in equation (72).
-/

namespace MAPMRTFaithfulLowProjectionIdentity

open MeasureTheory Set
open MAPMRTProposition51HardBranch MAPMRTProposition51ProjectionLowAmplitude
open MAPMRTProposition51ProjectionLowIBP
open MAPMRTProposition51ProjectionLowBudgets
open MAPFinishP51LowIdentity MAPMRTFaithfulSmoothCutoff
open MAPMRTFaithfulSmoothCutoffBudgets

noncomputable section

theorem faithfulLowFrequencyProjection_logarithmicDualFunction_eq
    {X H beta eta u : ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Icc (X / 2) (4 * X) → g x = 0) :
    lowFrequencyProjection X beta eta faithfulCutoff
        (logarithmicDualFunction X H beta faithfulCutoff g) u =
      (((Real.sqrt X * (lowProjectionScale X beta eta /
          (2 * Real.pi)) : ℝ) : ℂ) *
        ∫ x : ℝ, g x *
          lowOscillatoryIntegral X H beta eta x u faithfulCutoff
            (cutoffFourierKernel faithfulCutoff)) := by
  apply lowFrequencyProjection_logarithmicDualFunction_eq
    hX hH hHquarter hbeta heta hgSupport
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
  exact lowProjectionSourceKernel_integrable
    hX hH hHquarter hbeta heta hg hgSupport
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
    abs_faithfulCutoff_le_one
    faithfulCutoff_continuous
    faithfulCutoffFourierKernel_integrable
    faithfulCutoffFourierKernel_continuous

/-- Localized one-IBP form retaining the translated Fourier kernel inside the
physical `w` window.  This is the source-faithful input to the later
`z = w - log n + log X` summation, unlike the coarser global L1 corollary. -/
theorem norm_faithfulLowOscillatoryIntegral_le_localized
    {X H beta eta x u : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) :
    ‖lowOscillatoryIntegral X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff)‖ ≤
      (1 / (|beta| * X / 4)) *
        (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
          ‖lowProjectionAmplitudeDeriv X H beta eta x u
            faithfulCutoff faithfulCutoffDeriv
            (cutoffFourierKernel faithfulCutoff)
            faithfulCutoffFourierDeriv w‖) +
      ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
        (∫ w : ℝ in (Real.log ((x - H) / X))..(Real.log ((x + H) / X)),
          ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
            (cutoffFourierKernel faithfulCutoff) w‖) := by
  exact norm_lowOscillatoryIntegral_le_localized
    hX hH hHquarter hxLower hxUpper hbeta
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
    faithfulCutoff_hasDerivAt faithfulCutoffDeriv_continuous
    faithfulCutoffFourierKernel_hasDerivAt
    faithfulCutoffFourierDeriv_continuous

/-- Literal quadratic Schwartz envelope for the faithful low amplitude. -/
theorem norm_faithfulLowProjectionAmplitude_le_decay
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 ≤ H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x) :
    ‖lowProjectionAmplitude X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff) w‖ ≤
      3 * faithfulCutoffFourierDecayConstant 2 /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2 := by
  have hamp := norm_lowProjectionAmplitude_le_kernel
    (beta := beta) (eta := eta) (u := u)
    (kernel := cutoffFourierKernel faithfulCutoff)
    hX hH hHquarter hxLower hxUpper hw abs_faithfulCutoff_le_one
  have hk := norm_faithfulCutoffFourierKernel_le_decay
    2 (lowKernelArgument X beta eta u w)
  calc
    _ ≤ 3 * ‖cutoffFourierKernel faithfulCutoff
        (lowKernelArgument X beta eta u w)‖ := hamp
    _ ≤ 3 * (faithfulCutoffFourierDecayConstant 2 /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2) := by
      gcongr
    _ = _ := by ring

/-- Literal quadratic Schwartz envelope for the derivative amplitude. -/
theorem norm_faithfulLowProjectionAmplitudeDeriv_le_decay
    {X H beta eta x u w : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hw : w ∈ sourcePacketWindow X H x) :
    ‖lowProjectionAmplitudeDeriv X H beta eta x u
        faithfulCutoff faithfulCutoffDeriv
        (cutoffFourierKernel faithfulCutoff)
        faithfulCutoffFourierDeriv w‖ ≤
      ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          faithfulCutoffFourierDecayConstant 2 +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          faithfulCutoffFourierDerivDecayConstant 2) /
        (1 + |lowKernelArgument X beta eta u w|) ^ 2 := by
  have hamp := norm_lowProjectionAmplitudeDeriv_le_kernel
    (beta := beta) (eta := eta) (u := u)
    (kernel := cutoffFourierKernel faithfulCutoff)
    (kernel' := faithfulCutoffFourierDeriv)
    hX hH hHquarter hxLower hxUpper hw abs_faithfulCutoff_le_one
    abs_faithfulCutoffDeriv_le faithfulCutoffDerivBudget_nonneg
  have hk := norm_faithfulCutoffFourierKernel_le_decay
    2 (lowKernelArgument X beta eta u w)
  have hk' := norm_faithfulCutoffFourierDeriv_le_decay
    2 (lowKernelArgument X beta eta u w)
  have hC0 : 0 ≤ 3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H) := by
    apply add_nonneg (by norm_num)
    apply div_nonneg
    · exact mul_nonneg
        (mul_nonneg (by norm_num) faithfulCutoffDerivBudget_nonneg) hX.le
    · positivity
  have hC1 : 0 ≤ 3 * |lowProjectionScale X beta eta / (2 * Real.pi)| := by
    positivity
  calc
    _ ≤ (3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          ‖cutoffFourierKernel faithfulCutoff
            (lowKernelArgument X beta eta u w)‖ +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          ‖faithfulCutoffFourierDeriv
            (lowKernelArgument X beta eta u w)‖ := hamp
    _ ≤ (3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
          (faithfulCutoffFourierDecayConstant 2 /
            (1 + |lowKernelArgument X beta eta u w|) ^ 2) +
        3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
          (faithfulCutoffFourierDerivDecayConstant 2 /
            (1 + |lowKernelArgument X beta eta u w|) ^ 2) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hk hC0)
        (mul_le_mul_of_nonneg_left hk' hC1)
    _ = _ := by ring

/-- The already-proved one-IBP estimate specialized to the faithful cutoff
and its concrete derivative/Fourier budgets. -/
theorem norm_faithfulLowOscillatoryIntegral_le
    {X H beta eta x u : ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x) (hxUpper : x ≤ 4 * X)
    (hbeta : beta ≠ 0) (heta : 0 < eta) :
    ‖lowOscillatoryIntegral X H beta eta x u faithfulCutoff
        (cutoffFourierKernel faithfulCutoff)‖ ≤
      (1 / (|beta| * X / 4)) *
        ((3 / 2 + 51 * faithfulCutoffDerivBudget * X / (4 * H)) *
            (2 * Real.pi / lowProjectionScale X beta eta) *
              (∫ v : ℝ, ‖cutoffFourierKernel faithfulCutoff v‖) +
          3 * |lowProjectionScale X beta eta / (2 * Real.pi)| *
            (2 * Real.pi / lowProjectionScale X beta eta) *
              (∫ v : ℝ, ‖faithfulCutoffFourierDeriv v‖)) +
      ((17 * |beta| * X / 4) / (|beta| * X / 4) ^ 2) *
        (3 * (2 * Real.pi / lowProjectionScale X beta eta) *
          ∫ v : ℝ, ‖cutoffFourierKernel faithfulCutoff v‖) := by
  exact norm_lowOscillatoryIntegral_le
    hX hH hHquarter hxLower hxUpper hbeta heta
    (fun y hy ↦ faithfulCutoff_zero_of_one_le hy)
    abs_faithfulCutoff_le_one abs_faithfulCutoffDeriv_le
    faithfulCutoffDerivBudget_nonneg faithfulCutoff_hasDerivAt
    faithfulCutoffDeriv_continuous
    faithfulCutoffFourierKernel_hasDerivAt
    faithfulCutoffFourierDeriv_continuous
    faithfulCutoffFourierKernel_integrable
    faithfulCutoffFourierDeriv_integrable

#print axioms faithfulLowFrequencyProjection_logarithmicDualFunction_eq
#print axioms norm_faithfulLowOscillatoryIntegral_le_localized
#print axioms norm_faithfulLowProjectionAmplitude_le_decay
#print axioms norm_faithfulLowProjectionAmplitudeDeriv_le_decay
#print axioms norm_faithfulLowOscillatoryIntegral_le

end
end MAPMRTFaithfulLowProjectionIdentity
