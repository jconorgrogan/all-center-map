import FordCoshSqFourierCertified
import KhaleAppendixBTrigPolynomialCertified
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Certified algebraic kernel in Khale Lemma 5.1

After expanding the Euler product, every prime-power contribution is a
nonnegative scalar multiple of a Fourier coefficient `U(y)` and the
trigonometric polynomial from (5.1).  This file certifies the exact signed
kernel step.  Ford's identity (5.4), formerly the first analytic leaf, is
now discharged from Mathlib's change-of-variables and Beta/Gamma machinery.
-/

namespace MAPKhaleAppendixBLemma51KernelCertified

open MeasureTheory

noncomputable section

/-- Ford's Fourier kernel, in the normalization quoted by Khale. -/
def coshSqFourier (y : ℝ) : ℝ :=
  ∫ u : ℝ, Real.cos (y * u) / (Real.cosh u) ^ 2 ∂volume

/-- The exact Ford (5.4) source leaf. -/
abbrev FordCoshSqFourierIdentity : Prop :=
  ∀ y : ℝ,
    coshSqFourier y =
      if y = 0 then 2 else Real.pi * y / Real.sinh (Real.pi * y / 2)

/-- Ford's exact transform, discharged from Mathlib's change-of-variables and
Beta/Gamma/reflection machinery. -/
theorem fordCoshSqFourierIdentity : FordCoshSqFourierIdentity := by
  intro y
  simpa only [coshSqFourier] using
    MAPFordCoshSqFourierCertified.fordCoshSqFourierIdentity y

/-- Only the positivity and height-two bound of Ford's transform are consumed
by Khale Lemma 5.1. -/
abbrev CoshSqFourierPosBound : Prop :=
  ∀ y : ℝ, 0 ≤ coshSqFourier y ∧ coshSqFourier y ≤ 2

/-- Ford's exact transform formula implies precisely the positivity and
height-two bounds consumed in Lemma 5.1. -/
theorem coshSqFourierPosBound_of_identity
    (hFord : FordCoshSqFourierIdentity) :
    CoshSqFourierPosBound := by
  intro y
  rw [hFord y]
  by_cases hy : y = 0
  · simp [hy]
  rw [if_neg hy]
  let x : ℝ := Real.pi * y / 2
  have hx : x ≠ 0 := by
    dsimp [x]
    exact div_ne_zero (mul_ne_zero Real.pi_ne_zero hy) (by norm_num)
  have hnum : Real.pi * y = 2 * x := by dsimp [x]; ring
  rw [hnum]
  have htwo : 2 * x / 2 = x := by ring
  rw [htwo]
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hsinhNeg : Real.sinh x < 0 := Real.sinh_neg_iff.mpr hxneg
    constructor
    · exact div_nonneg_iff.mpr (Or.inr ⟨by linarith, hsinhNeg.le⟩)
    · rw [div_le_iff_of_neg hsinhNeg]
      have hs := Real.sinh_le_self_iff.mpr hxneg.le
      nlinarith
  · have hsinhPos : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hxpos
    constructor
    · positivity
    · rw [div_le_iff₀ hsinhPos]
      have hs := Real.self_le_sinh_iff.mpr hxpos.le
      nlinarith

/-- The positivity/height bound with Ford's source leaf discharged. -/
theorem coshSqFourierPosBound : CoshSqFourierPosBound :=
  coshSqFourierPosBound_of_identity fordCoshSqFourierIdentity

/-- Exact prime-power kernel inequality.  This is the sign-sensitive heart of
Lemma 5.1 after the Fourier transform has been evaluated. -/
theorem weighted_cosine_kernel_lower
    {U theta : ℝ} (hU0 : 0 ≤ U) (hU2 : U ≤ 2) :
    -2 * 10.01055 ≤
      U * (17.145 * Real.cos theta +
        10.6825 * Real.cos (2 * theta) +
        4.5 * Real.cos (3 * theta) +
        Real.cos (4 * theta)) := by
  have htrig :=
    MAPKhaleAppendixBTrigPolynomialCertified.appendixB_trigonometric_nonneg theta
  have hsum : -10.01055 ≤
      17.145 * Real.cos theta +
        10.6825 * Real.cos (2 * theta) +
        4.5 * Real.cos (3 * theta) +
        Real.cos (4 * theta) := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hsum hU0
  nlinarith

/-- A nonnegative prime-power weight preserves the exact kernel lower bound. -/
theorem weighted_prime_power_kernel_lower
    {w U theta : ℝ} (hw : 0 ≤ w) (hU0 : 0 ≤ U) (hU2 : U ≤ 2) :
    -2 * 10.01055 * w ≤
      w * U * (17.145 * Real.cos theta +
        10.6825 * Real.cos (2 * theta) +
        4.5 * Real.cos (3 * theta) +
        Real.cos (4 * theta)) := by
  have h := mul_le_mul_of_nonneg_left
    (weighted_cosine_kernel_lower (theta := theta) hU0 hU2) hw
  nlinarith

end
end MAPKhaleAppendixBLemma51KernelCertified

#print axioms MAPKhaleAppendixBLemma51KernelCertified.weighted_cosine_kernel_lower
#print axioms MAPKhaleAppendixBLemma51KernelCertified.weighted_prime_power_kernel_lower
#print axioms MAPKhaleAppendixBLemma51KernelCertified.coshSqFourierPosBound_of_identity

#print axioms MAPKhaleAppendixBLemma51KernelCertified.fordCoshSqFourierIdentity
#print axioms MAPKhaleAppendixBLemma51KernelCertified.coshSqFourierPosBound
