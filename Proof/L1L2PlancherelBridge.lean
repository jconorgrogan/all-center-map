import Mathlib.Analysis.Fourier.LpSpace

namespace MAPGallagherPlancherel

open MeasureTheory SchwartzMap
open scoped FourierTransform ENNReal
noncomputable section

/-- Self-adjointness of the classical Fourier integral when only the first
function is integrable and the test function is Schwartz.  Mathlib's public
Schwartz theorem unnecessarily presents both inputs as Schwartz, while its
underlying Fubini theorem already proves this exact form. -/
theorem integral_fourier_mul_schwartz
    {f : ℝ → ℂ} (hf : Integrable f) (g : 𝓢(ℝ, ℂ)) :
    (∫ xi : ℝ, (𝓕 f) xi * g xi) =
      ∫ x : ℝ, f x * (𝓕 g) x := by
  simpa using!
    VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner
      hf g.integrable

/-- Compatibility of Mathlib's `L²` Fourier extension with the classical
Fourier integral for an `L¹ ∩ L²` function whose classical transform is also
in `L²`.  This is the missing bridge needed to apply `Lp.norm_fourier_eq` to
compact sliding fields. -/
theorem fourier_toLp_eq_toLp_classical
    {f F : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2)
    (hF2 : MemLp F 2)
    (hF : ∀ xi : ℝ, F xi = (𝓕 f) xi) :
    𝓕 (hf2.toLp f) = hF2.toLp F := by
  let T := MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
  have hTker : T.toLinearMap.ker = ⊥ :=
    MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
  have hTinj : Function.Injective T := LinearMap.ker_eq_bot.mp hTker
  apply hTinj
  have hcompat :
      𝓕 (T (hf2.toLp f)) = T (𝓕 (hf2.toLp f)) := by
    simpa [T] using
      (MeasureTheory.Lp.fourier_toTemperedDistribution_eq (hf2.toLp f))
  rw [← hcompat]
  ext g
  rw [TemperedDistribution.fourier_apply]
  simp only [T, MeasureTheory.Lp.toTemperedDistributionCLM_apply,
    MeasureTheory.Lp.toTemperedDistribution_apply]
  have hleft :
      (∫ x : ℝ, (𝓕 g) x • ((hf2.toLp f : Lp ℂ 2) : ℝ → ℂ) x) =
        ∫ x : ℝ, (𝓕 g) x * f x := by
    apply integral_congr_ae
    filter_upwards [hf2.coeFn_toLp] with x hx
    simp [hx]
  have hright :
      (∫ xi : ℝ, g xi • ((hF2.toLp F : Lp ℂ 2) : ℝ → ℂ) xi) =
        ∫ xi : ℝ, g xi * (𝓕 f) xi := by
    apply integral_congr_ae
    filter_upwards [hF2.coeFn_toLp] with xi hxi
    simp [hxi, hF xi]
  rw [hleft, hright]
  simpa [mul_comm] using (integral_fourier_mul_schwartz hf1 g).symm

/-- Plancherel in ordinary integral notation for a classical `L¹ ∩ L²`
Fourier pair. -/
theorem integral_norm_sq_fourier_pair
    {f F : ℝ → ℂ}
    (hf1 : Integrable f) (hf2 : MemLp f 2)
    (hF2 : MemLp F 2)
    (hF : ∀ xi : ℝ, F xi = (𝓕 f) xi) :
    (∫ xi : ℝ, ‖F xi‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have heq := fourier_toLp_eq_toLp_classical hf1 hf2 hF2 hF
  have hnorm := MeasureTheory.Lp.norm_fourier_eq (hf2.toLp f)
  rw [heq] at hnorm
  have hFnorm := hF2.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  have hfnorm := hf2.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  rw [Lp.norm_toLp, Lp.norm_toLp, hFnorm, hfnorm] at hnorm
  norm_num at hnorm
  let IF : ℝ := ∫ xi : ℝ, ‖F xi‖ ^ 2
  let If : ℝ := ∫ x : ℝ, ‖f x‖ ^ 2
  have hIF0 : 0 ≤ IF := MeasureTheory.integral_nonneg (fun xi => sq_nonneg ‖F xi‖)
  have hIf0 : 0 ≤ If := MeasureTheory.integral_nonneg (fun x => sq_nonneg ‖f x‖)
  have hrootF : 0 ≤ IF ^ (1 / 2 : ℝ) := Real.rpow_nonneg hIF0 _
  have hrootf : 0 ≤ If ^ (1 / 2 : ℝ) := Real.rpow_nonneg hIf0 _
  change (ENNReal.ofReal (IF ^ (1 / 2 : ℝ))).toReal =
    (ENNReal.ofReal (If ^ (1 / 2 : ℝ))).toReal at hnorm
  rw [ENNReal.toReal_ofReal hrootF, ENNReal.toReal_ofReal hrootf,
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hnorm
  change IF = If
  calc
    IF = (Real.sqrt IF) ^ 2 := (Real.sq_sqrt hIF0).symm
    _ = (Real.sqrt If) ^ 2 := by rw [hnorm]
    _ = If := Real.sq_sqrt hIf0

end
end MAPGallagherPlancherel
