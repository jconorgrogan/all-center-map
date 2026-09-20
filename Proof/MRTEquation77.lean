import MRTProposition51HardBranch

/-!
# MRT Proposition 5.1, equation (77)

This staging module proves the exact fundamental-theorem-of-calculus identity
behind equation (77).  The normalization is the manuscript normalization:
the high-frequency projection has scale `|β|X/η`, hence translation
`2πηv/(|β|X)`.
-/

namespace MAPMRTEquation77

open MeasureTheory Set
open MAPMRTProposition51HardBranch

noncomputable section

/-- Pointwise fundamental-theorem-of-calculus identity used in (77). -/
theorem sub_translate_eq_intervalIntegral_deriv
    {G G' : ℝ → ℂ} (hderiv : ∀ y, HasDerivAt G (G' y) y)
    (u s : ℝ)
    (hint : IntervalIntegrable
      (fun a : ℝ ↦ (s : ℂ) * G' (u - a * s)) volume 0 1) :
    G u - G (u - s) =
      ∫ a : ℝ in 0..1, (s : ℂ) * G' (u - a * s) := by
  have hcomp : ∀ a : ℝ,
      HasDerivAt (fun z : ℝ ↦ G (u - z * s))
        (-((s : ℂ) * G' (u - a * s))) a := by
    intro a
    have hinner : HasDerivAt (fun z : ℝ ↦ u - z * s) (-s) a := by
      simpa using (hasDerivAt_const a u).sub ((hasDerivAt_id a).mul_const s)
    simpa [Function.comp_def, mul_comm] using
      HasDerivAt.scomp a (hderiv (u - a * s)) hinner
  have hnegint : IntervalIntegrable
      (fun a : ℝ ↦ -((s : ℂ) * G' (u - a * s))) volume 0 1 := hint.neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun a _ha ↦ hcomp a) hnegint
  have hftc' :
      (∫ a : ℝ in 0..1, -((s : ℂ) * G' (u - a * s))) =
        G (u - s) - G u := by simpa using hftc
  calc
    G u - G (u - s) = -(G (u - s) - G u) := by abel
    _ = -(∫ a : ℝ in 0..1, -((s : ℂ) * G' (u - a * s))) := by rw [hftc']
    _ = ∫ a : ℝ in 0..1, (s : ℂ) * G' (u - a * s) := by
      rw [intervalIntegral.integral_neg]
      simp

/-- Equation (77) before interchanging the `a` and `v` integrals.  This is the
exact identity obtained from `∫ kernel = 1` and the fundamental theorem of
calculus, with no Fubini hypothesis hidden in the statement. -/
theorem highFrequencyProjection_eq_integral_intervalIntegral
    {X beta eta u : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0)
    (cutoff : ℝ → ℝ) {G G' : ℝ → ℂ}
    (hderiv : ∀ y, HasDerivAt G (G' y) y)
    (hkernel : Integrable (cutoffFourierKernel cutoff))
    (hkernelMass : ∫ v : ℝ, cutoffFourierKernel cutoff v = 1)
    (hline : ∀ v : ℝ, IntervalIntegrable
      (fun a : ℝ ↦ ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
        G' (u - a * (2 * Real.pi * eta * v / (|beta| * X)))) volume 0 1)
    (htranslated : Integrable (fun v : ℝ ↦
      G (u - 2 * Real.pi * eta * v / (|beta| * X)) *
        cutoffFourierKernel cutoff v)) :
    highFrequencyProjection X beta eta cutoff G u =
      ∫ v : ℝ, (∫ a : ℝ in 0..1,
        ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
          G' (u - a * (2 * Real.pi * eta * v / (|beta| * X)))) *
            cutoffFourierKernel cutoff v := by
  have hden : |beta| * X ≠ 0 := mul_ne_zero (abs_ne_zero.mpr hbeta) hX.ne'
  unfold highFrequencyProjection mediumOrLowProjection rescaledProjection
  by_cases heta : eta = 0
  · subst eta
    simp only [mul_zero, zero_mul, zero_div, div_zero, sub_zero]
    rw [integral_const_mul, hkernelMass]
    simp
  · have hT : |beta| * X / eta ≠ 0 := div_ne_zero hden heta
    have hshift : ∀ v : ℝ,
        2 * Real.pi * v / (|beta| * X / eta) =
          2 * Real.pi * eta * v / (|beta| * X) := by
      intro v
      field_simp
    simp_rw [hshift]
    calc
      G u - ∫ v : ℝ,
          G (u - 2 * Real.pi * eta * v / (|beta| * X)) *
            cutoffFourierKernel cutoff v =
          ∫ v : ℝ, (G u - G (u - 2 * Real.pi * eta * v / (|beta| * X))) *
            cutoffFourierKernel cutoff v := by
        rw [show (fun v : ℝ ↦
            (G u - G (u - 2 * Real.pi * eta * v / (|beta| * X))) *
              cutoffFourierKernel cutoff v) =
            (fun v : ℝ ↦ G u * cutoffFourierKernel cutoff v -
              G (u - 2 * Real.pi * eta * v / (|beta| * X)) *
                cutoffFourierKernel cutoff v) by
          funext v
          ring]
        rw [integral_sub (hkernel.const_mul (G u)) htranslated]
        rw [integral_const_mul, hkernelMass]
        simp
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with v
        rw [sub_translate_eq_intervalIntegral_deriv hderiv _ _ (hline v)]

/-- The literal iterated-integral form of manuscript equation (77).  The final
hypothesis is exactly the absolute-integrability condition needed for the one
Fubini interchange made in the paper; it is a regularity obligation, not an
analytic estimate. -/
theorem highFrequencyProjection_equation77
    {X beta eta u : ℝ} (hX : 0 < X) (hbeta : beta ≠ 0)
    (cutoff : ℝ → ℝ) {G G' : ℝ → ℂ}
    (hderiv : ∀ y, HasDerivAt G (G' y) y)
    (hkernel : Integrable (cutoffFourierKernel cutoff))
    (hkernelMass : ∫ v : ℝ, cutoffFourierKernel cutoff v = 1)
    (hline : ∀ v : ℝ, IntervalIntegrable
      (fun a : ℝ ↦ ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
        G' (u - a * (2 * Real.pi * eta * v / (|beta| * X)))) volume 0 1)
    (htranslated : Integrable (fun v : ℝ ↦
      G (u - 2 * Real.pi * eta * v / (|beta| * X)) *
        cutoffFourierKernel cutoff v))
    (hfubini : Integrable (Function.uncurry (fun a v : ℝ ↦
      ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
        G' (u - a * (2 * Real.pi * eta * v / (|beta| * X))) *
          cutoffFourierKernel cutoff v))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume)) :
    highFrequencyProjection X beta eta cutoff G u =
      ((2 * Real.pi * eta / (|beta| * X) : ℝ) : ℂ) *
        ∫ a : ℝ in 0..1, ∫ v : ℝ,
          (v : ℂ) * G' (u - a * (2 * Real.pi * eta * v / (|beta| * X))) *
            cutoffFourierKernel cutoff v := by
  rw [highFrequencyProjection_eq_integral_intervalIntegral hX hbeta cutoff
    hderiv hkernel hkernelMass hline htranslated]
  calc
    (∫ v : ℝ, (∫ a : ℝ in 0..1,
        ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
          G' (u - a * (2 * Real.pi * eta * v / (|beta| * X)))) *
            cutoffFourierKernel cutoff v) =
      ∫ v : ℝ, ∫ a : ℝ in 0..1,
        ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
          G' (u - a * (2 * Real.pi * eta * v / (|beta| * X))) *
            cutoffFourierKernel cutoff v := by
        apply integral_congr_ae
        filter_upwards with v
        rw [intervalIntegral.integral_mul_const]
    _ = ∫ a : ℝ in 0..1, ∫ v : ℝ,
        ((2 * Real.pi * eta * v / (|beta| * X) : ℝ) : ℂ) *
          G' (u - a * (2 * Real.pi * eta * v / (|beta| * X))) *
            cutoffFourierKernel cutoff v :=
      (MeasureTheory.intervalIntegral_integral_swap hfubini).symm
    _ = ((2 * Real.pi * eta / (|beta| * X) : ℝ) : ℂ) *
        ∫ a : ℝ in 0..1, ∫ v : ℝ,
          (v : ℂ) * G' (u - a * (2 * Real.pi * eta * v / (|beta| * X))) *
            cutoffFourierKernel cutoff v := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro a _ha
      dsimp only
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with v
      push_cast
      field_simp [mul_ne_zero (abs_ne_zero.mpr hbeta) hX.ne']

end
end MAPMRTEquation77

#print axioms MAPMRTEquation77.sub_translate_eq_intervalIntegral_deriv
#print axioms MAPMRTEquation77.highFrequencyProjection_eq_integral_intervalIntegral
#print axioms MAPMRTEquation77.highFrequencyProjection_equation77
