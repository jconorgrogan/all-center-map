import MRTProposition51ProjectionLowIBP
import MAPLiteralCutoffDual

/-!
# Proposition 5.1: exact low-projection source identity

This file supplies the missing measure-theoretic seam between the literal
low-frequency projection in (76) and the localized oscillatory integral (78).
All scale factors are retained.  The only analytic assumption in the main
identity is absolute integrability of the two-variable source kernel needed by
Fubini.
-/

namespace MAPFinishP51LowIdentity

open MeasureTheory Set
open MAPMRTCorollary53Source
open MAPMRTProposition51HardBranch
open MAPMRTProposition51ProjectionLowAmplitude
open MAPMRTProposition51ProjectionLowBudgets
open MAPMRTProposition51ProjectionLowIBP
open MAPAllCenterApertureTransfer
open MAPMRTVanDerCorputProof

noncomputable section

/-- The literal `(w,x)` integrand obtained after opening the logarithmic dual
function in the low projection. -/
def lowProjectionSourceKernel
    (X H beta eta u : ℝ) (cutoff : ℝ → ℝ) (g : ℝ → ℂ)
    (w x : ℝ) : ℂ :=
  g x * (additivePhase (beta * X * Real.exp w) *
    lowProjectionAmplitude X H beta eta x u cutoff
      (cutoffFourierKernel cutoff) w)

private theorem lowProjectionAmplitude_eq_zero_outside_window
    {X H beta eta x u w : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : w ∉ Set.Ioc (Real.log ((x - H) / X))
      (Real.log ((x + H) / X))) :
    lowProjectionAmplitude X H beta eta x u cutoff kernel w = 0 := by
  have hxMinusLower : X / 4 ≤ x - H := by linarith
  have hxMinus : 0 < x - H :=
    lt_of_lt_of_le (by positivity : 0 < X / 4) hxMinusLower
  have hxPlus : 0 < x + H := by linarith
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hb : 0 < (x + H) / X := div_pos hxPlus hX
  simp only [Set.mem_Ioc, not_and_or, not_le] at hw
  apply lowProjectionAmplitude_eq_zero_of_physical_outside hH hcutoffSupport
  rcases hw with hwLeft | hwRight
  · have hexp : Real.exp w ≤ (x - H) / X := by
      rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr (le_of_not_gt hwLeft)
    have hnum : X * Real.exp w - x ≤ -H := by
      have := (le_div_iff₀ hX).mp hexp
      nlinarith
    rw [abs_of_nonpos (hnum.trans (by linarith))]
    linarith
  · have hexp : (x + H) / X < Real.exp w := by
      rw [← Real.exp_log hb]
      exact Real.exp_lt_exp.mpr hwRight
    have hnum : H < X * Real.exp w - x := by
      have := (div_lt_iff₀ hX).mp hexp
      nlinarith
    rw [abs_of_pos (lt_trans hH hnum)]
    exact hnum.le

/-- Absolute integrability of the sole Fubini kernel follows from the literal
physical support and an `L¹` Fourier kernel.  This removes the abstract
`hFubini` seam for every concrete Schwartz cutoff. -/
theorem lowProjectionSourceKernel_integrable
    {X H beta eta u : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hcutoffBound : ∀ y, |cutoff y| ≤ 1)
    (hcutoffCont : Continuous cutoff)
    (hkernel : Integrable kernel) (hkernelCont : Continuous kernel) :
    Integrable (Function.uncurry fun w x ↦
      g x * (additivePhase (beta * X * Real.exp w) *
        lowProjectionAmplitude X H beta eta x u cutoff kernel w))
      (volume.prod volume) := by
  have hscaled : Integrable (fun w : ℝ ↦
      ‖kernel (lowKernelArgument X beta eta u w)‖) :=
    integrable_norm_lowKernelArgument hX hbeta heta u hkernel
  have hmajor : Integrable (fun z : ℝ × ℝ ↦
      3 * (‖kernel (lowKernelArgument X beta eta u z.1)‖ * ‖g z.2‖)) :=
    (hscaled.mul_prod hg.norm).const_mul 3
  have hadd : Continuous additivePhase :=
    by
      unfold additivePhase
      fun_prop
  have hamp : Continuous (fun z : ℝ × ℝ ↦
      lowProjectionAmplitude X H beta eta z.2 u cutoff kernel z.1) := by
    unfold lowProjectionAmplitude lowKernelArgument
    fun_prop
  have hmeas : AEStronglyMeasurable (Function.uncurry fun w x ↦
      g x * (additivePhase (beta * X * Real.exp w) *
        lowProjectionAmplitude X H beta eta x u cutoff kernel w))
      (volume.prod volume) := by
    exact hg.aestronglyMeasurable.comp_snd.mul
      ((hadd.comp (by fun_prop)).mul hamp).aestronglyMeasurable
  apply Integrable.mono' hmajor hmeas
  filter_upwards with z
  rcases z with ⟨w, x⟩
  by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
  · by_cases hw : w ∈ sourcePacketWindow X H x
    · have hampBound := norm_lowProjectionAmplitude_le_kernel
        (beta := beta) (eta := eta) (u := u) (kernel := kernel)
        hX hH.le hHquarter hx.1 hx.2 hw hcutoffBound
      simp only [Function.uncurry_apply_pair, norm_mul, norm_additivePhase,
        one_mul]
      nlinarith [norm_nonneg (g x),
        norm_nonneg (kernel (lowKernelArgument X beta eta u w))]
    · have hwIoc : w ∉ Set.Ioc (Real.log ((x - H) / X))
          (Real.log ((x + H) / X)) := by
        intro hw'
        exact hw ⟨hw'.1.le, hw'.2⟩
      have hz := lowProjectionAmplitude_eq_zero_outside_window
        (beta := beta) (eta := eta) (u := u) (kernel := kernel)
        hX hH hHquarter hx.1 hcutoffSupport hwIoc
      simp only [Function.uncurry_apply_pair, norm_mul, hz, norm_zero,
        mul_zero]
      positivity
  · have hgzero := hgSupport x hx
    simp only [Function.uncurry_apply_pair, hgzero, norm_zero, zero_mul]
    positivity

/-- The affine substitution `w = u - 2πv/T`, including its Jacobian.
This whole-line identity does not require an integrability hypothesis: it is
the standard Haar-measure scaling identity for the Bochner integral. -/
theorem rescaledProjection_eq_affine_kernel
    {T u : ℝ} (hT : 0 < T) (kernel : ℝ → ℂ) (G : ℝ → ℂ) :
    rescaledProjection kernel T G u =
      ((T / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ w : ℝ, G w * kernel (T / (2 * Real.pi) * (u - w)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  let a : ℝ := 2 * Real.pi / T
  have ha : 0 < a := div_pos (by positivity) hT
  let r : ℝ → ℂ := fun w ↦ G w * kernel (a⁻¹ * (u - w))
  have htranslate : (∫ z : ℝ, r (u - z)) = ∫ w : ℝ, r w :=
    MeasureTheory.integral_sub_left_eq_self r volume u
  have hpoint (v : ℝ) : G (u - 2 * Real.pi * v / T) * kernel v =
      r (u - a * v) := by
    unfold r a
    congr 2
    · ring
    · have ha0 : (2 * Real.pi / T) ≠ 0 := ne_of_gt ha
      field_simp [ha0, hT.ne', hpi.ne'] <;> ring
  have hscale := Measure.integral_comp_mul_left (fun z : ℝ ↦ r (u - z)) a
  unfold rescaledProjection
  calc
    (∫ v : ℝ, G (u - 2 * Real.pi * v / T) * kernel v) =
        ∫ v : ℝ, r (u - a * v) := by
          apply integral_congr_ae
          filter_upwards with v
          exact hpoint v
    _ = |a⁻¹| • ∫ z : ℝ, r (u - z) := hscale
    _ = |a⁻¹| • ∫ w : ℝ, r w := by rw [htranslate]
    _ = ((T / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ w : ℝ, G w * kernel (T / (2 * Real.pi) * (u - w)) := by
      change ((|a⁻¹| : ℝ) : ℂ) * (∫ w : ℝ, r w) = _
      have habsa : |a⁻¹| = T / (2 * Real.pi) := by
        rw [abs_of_pos (inv_pos.mpr ha)]
        unfold a
        field_simp [hT.ne', hpi.ne']
      rw [habsa]
      apply congrArg (((T / (2 * Real.pi) : ℝ) : ℂ) * ·)
      apply integral_congr_ae
      filter_upwards with w
      unfold r
      congr 2
      have ha0 : (2 * Real.pi / T) ≠ 0 := ne_of_gt ha
      unfold a
      field_simp [ha0, hT.ne', hpi.ne'] <;> ring

/-- The low amplitude vanishes off the precise logarithmic physical window.
The half-open endpoint convention matches `intervalIntegral`. -/
theorem lowProjectionAmplitude_eq_zero_of_not_mem_Ioc
    {X H beta eta x u w : ℝ} {cutoff : ℝ → ℝ} {kernel : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hw : w ∉ Set.Ioc (Real.log ((x - H) / X))
      (Real.log ((x + H) / X))) :
    lowProjectionAmplitude X H beta eta x u cutoff kernel w = 0 := by
  have hxMinusLower : X / 4 ≤ x - H := by linarith
  have hxMinus : 0 < x - H :=
    lt_of_lt_of_le (by positivity : 0 < X / 4) hxMinusLower
  have hxPlus : 0 < x + H := by linarith
  have ha : 0 < (x - H) / X := div_pos hxMinus hX
  have hb : 0 < (x + H) / X := div_pos hxPlus hX
  simp only [Set.mem_Ioc, not_and_or, not_le] at hw
  apply lowProjectionAmplitude_eq_zero_of_physical_outside hH hcutoffSupport
  rcases hw with hwLeft | hwRight
  · have hexp : Real.exp w ≤ (x - H) / X := by
      rw [← Real.exp_log ha]
      exact Real.exp_le_exp.mpr (le_of_not_gt hwLeft)
    have hnum : X * Real.exp w - x ≤ -H := by
      have := (le_div_iff₀ hX).mp hexp
      nlinarith
    rw [abs_of_nonpos (hnum.trans (by linarith))]
    linarith
  · have hexp : (x + H) / X < Real.exp w := by
      rw [← Real.exp_log hb]
      exact Real.exp_lt_exp.mpr hwRight
    have hnum : H < X * Real.exp w - x := by
      have := (div_lt_iff₀ hX).mp hexp
      nlinarith
    rw [abs_of_pos (lt_trans hH hnum)]
    exact hnum.le

/-- The whole-line inner source integral is exactly the localized (78)
interval integral. -/
theorem integral_eq_lowOscillatoryIntegral
    {X H beta eta x u : ℝ} {cutoff : ℝ → ℝ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hxLower : X / 2 ≤ x)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0) :
    (∫ w : ℝ, additivePhase (beta * X * Real.exp w) *
        lowProjectionAmplitude X H beta eta x u cutoff
          (cutoffFourierKernel cutoff) w) =
      lowOscillatoryIntegral X H beta eta x u cutoff
        (cutoffFourierKernel cutoff) := by
  let a := Real.log ((x - H) / X)
  let b := Real.log ((x + H) / X)
  let F : ℝ → ℂ := fun w ↦ additivePhase (beta * X * Real.exp w) *
    lowProjectionAmplitude X H beta eta x u cutoff
      (cutoffFourierKernel cutoff) w
  have hab : a ≤ b := sourcePacketWindow_order hX hH hHquarter hxLower
  have hindicator : F = Set.indicator (Set.Ioc a b) F := by
    funext w
    by_cases hw : w ∈ Set.Ioc a b
    · simp [hw]
    · have hz := lowProjectionAmplitude_eq_zero_of_not_mem_Ioc
          (beta := beta) (eta := eta) (u := u)
          (kernel := cutoffFourierKernel cutoff)
          hX hH hHquarter hxLower hcutoffSupport (by simpa [a, b] using hw)
      simp [F, hw, hz]
  unfold lowOscillatoryIntegral
  change (∫ w : ℝ, F w) = ∫ w : ℝ in a..b, F w
  calc
    (∫ w : ℝ, F w) = ∫ w : ℝ in Set.Ioc a b, F w := by
      conv_lhs => rw [hindicator]
      rw [MeasureTheory.integral_indicator measurableSet_Ioc]
    _ = ∫ w : ℝ in a..b, F w :=
      (intervalIntegral.integral_of_le hab).symm

/-- Exact source-faithful low-projection identity.  The support hypotheses are
used only to replace the whole-line `w` integral by its physical interval;
`hFubini` is precisely the absolute-integrability condition for the sole
interchange of the `w` and `x` integrals. -/
theorem lowFrequencyProjection_logarithmicDualFunction_eq
    {X H beta eta u : ℝ} {cutoff : ℝ → ℝ} {g : ℝ → ℂ}
    (hX : 0 < X) (hH : 0 < H) (hHquarter : H ≤ X / 4)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0)
    (hcutoffSupport : ∀ y, 1 ≤ |y| → cutoff y = 0)
    (hFubini : Integrable
      (Function.uncurry
        (lowProjectionSourceKernel X H beta eta u cutoff g))
      (volume.prod volume)) :
    lowFrequencyProjection X beta eta cutoff
        (logarithmicDualFunction X H beta cutoff g) u =
      (((Real.sqrt X * (lowProjectionScale X beta eta /
          (2 * Real.pi)) : ℝ) : ℂ) *
        ∫ x : ℝ, g x *
          lowOscillatoryIntegral X H beta eta x u cutoff
            (cutoffFourierKernel cutoff)) := by
  have hscale : 0 < lowProjectionScale X beta eta := by
    unfold lowProjectionScale
    positivity
  rw [show lowFrequencyProjection X beta eta cutoff
      (logarithmicDualFunction X H beta cutoff g) u =
      rescaledProjection (cutoffFourierKernel cutoff)
        (lowProjectionScale X beta eta)
        (logarithmicDualFunction X H beta cutoff g) u by rfl]
  rw [rescaledProjection_eq_affine_kernel hscale]
  have hswap := MeasureTheory.integral_integral_swap hFubini
  have hopen (w : ℝ) :
      logarithmicDualFunction X H beta cutoff g w *
          cutoffFourierKernel cutoff
            (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) =
        (Real.sqrt X : ℂ) *
          ∫ x : ℝ, lowProjectionSourceKernel
            X H beta eta u cutoff g w x := by
    unfold logarithmicDualFunction lowProjectionSourceKernel
    rw [show (∫ x : ℝ, (cutoff ((X * Real.exp w - x) / H) : ℂ) * g x) =
        ∫ x : ℝ, g x * (cutoff ((X * Real.exp w - x) / H) : ℂ) by
      apply integral_congr_ae
      filter_upwards with x
      ring]
    rw [show (Real.sqrt X : ℂ) * (Real.exp (w / 2) : ℂ) *
          additivePhase (beta * X * Real.exp w) *
          (∫ x : ℝ, g x * (cutoff ((X * Real.exp w - x) / H) : ℂ)) *
          cutoffFourierKernel cutoff
            (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) =
        (Real.sqrt X : ℂ) *
          ((Real.exp (w / 2) : ℂ) *
            additivePhase (beta * X * Real.exp w) *
            cutoffFourierKernel cutoff
              (lowProjectionScale X beta eta / (2 * Real.pi) * (u - w)) *
            (∫ x : ℝ, g x *
              (cutoff ((X * Real.exp w - x) / H) : ℂ))) by ring]
    rw [← MeasureTheory.integral_const_mul]
    apply congrArg ((Real.sqrt X : ℂ) * ·)
    apply integral_congr_ae
    filter_upwards with x
    unfold lowProjectionAmplitude lowKernelArgument
    ring
  simp_rw [hopen]
  rw [MeasureTheory.integral_const_mul]
  change ((lowProjectionScale X beta eta / (2 * Real.pi) : ℝ) : ℂ) *
      ((Real.sqrt X : ℂ) *
        ∫ w : ℝ, ∫ x : ℝ,
          lowProjectionSourceKernel X H beta eta u cutoff g w x) = _
  rw [hswap]
  have hinner (x : ℝ) :
      (∫ w : ℝ, lowProjectionSourceKernel
          X H beta eta u cutoff g w x) =
        g x * lowOscillatoryIntegral X H beta eta x u cutoff
          (cutoffFourierKernel cutoff) := by
    unfold lowProjectionSourceKernel
    rw [MeasureTheory.integral_const_mul]
    by_cases hx : x ∈ Set.Icc (X / 2) (4 * X)
    · rw [integral_eq_lowOscillatoryIntegral hX hH hHquarter hx.1
          hcutoffSupport]
    · rw [hgSupport x hx]
      simp
  simp_rw [hinner]
  push_cast
  ring

/-- Premise-free Fubini specialization for the literal compactly supported
Schwartz cutoff.  The only remaining inputs concern the arithmetic function
`g` itself and the genuine aperture inequality. -/
theorem literalLowFrequencyProjection_logarithmicDualFunction_eq
    {ε X beta eta u : ℝ} {g : ℝ → ℂ}
    (hX : 4 ≤ X)
    (hbeta : beta ≠ 0) (heta : 0 < eta)
    (hg : Integrable g)
    (hgSupport : ∀ x, x ∉ Set.Icc (X / 2) (4 * X) → g x = 0) :
    lowFrequencyProjection X beta eta MAPLiteralCutoffDual.literalCutoff
        (logarithmicDualFunction X (baseAperture ε X) beta
          MAPLiteralCutoffDual.literalCutoff g) u =
      (((Real.sqrt X * (lowProjectionScale X beta eta /
          (2 * Real.pi)) : ℝ) : ℂ) *
        ∫ x : ℝ, g x *
          lowOscillatoryIntegral X (baseAperture ε X) beta eta x u
            MAPLiteralCutoffDual.literalCutoff
            (cutoffFourierKernel MAPLiteralCutoffDual.literalCutoff)) := by
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hH := baseAperture_pos (ε := ε) hXpos
  have hHquarter : baseAperture ε X ≤ X / 4 := by
    have hXone : 1 ≤ X := by linarith
    have hreserve : apertureReserve ε ≤ 1 / 1200 := by
      unfold apertureReserve
      exact min_le_right _ _
    have hexponent : 2 / 15 + apertureReserve ε ≤ 1 / 2 := by linarith
    have hpow : Real.rpow X (2 / 15 + apertureReserve ε) ≤
        Real.rpow X (1 / 2) :=
      Real.rpow_le_rpow_of_exponent_le hXone hexponent
    have hsqrt : Real.sqrt X ≤ X / 2 := by
      rw [Real.sqrt_le_iff]
      exact ⟨by linarith, by nlinarith⟩
    rw [show Real.rpow X (1 / 2) = Real.sqrt X from
      (Real.sqrt_eq_rpow X).symm] at hpow
    unfold baseAperture
    nlinarith
  apply lowFrequencyProjection_logarithmicDualFunction_eq
    (cutoff := MAPLiteralCutoffDual.literalCutoff) (g := g)
    hXpos hH hHquarter hbeta heta hgSupport
    (fun y hy ↦ MAPLiteralCutoffDual.literalCutoff_zero hy)
  exact lowProjectionSourceKernel_integrable hXpos hH hHquarter hbeta heta hg
    hgSupport (fun y hy ↦ MAPLiteralCutoffDual.literalCutoff_zero hy)
    MAPLiteralCutoffDual.abs_literalCutoff_le_one
    MAPLiteralCutoffDual.literalCutoff_continuous
    MAPLiteralCutoffDual.literalCutoffFourierKernel_integrable
    MAPLiteralCutoffDual.literalCutoffFourierKernel_continuous

end
end MAPFinishP51LowIdentity

#print axioms MAPFinishP51LowIdentity.rescaledProjection_eq_affine_kernel
#print axioms MAPFinishP51LowIdentity.integral_eq_lowOscillatoryIntegral
#print axioms MAPFinishP51LowIdentity.lowFrequencyProjection_logarithmicDualFunction_eq
#print axioms MAPFinishP51LowIdentity.literalLowFrequencyProjection_logarithmicDualFunction_eq
