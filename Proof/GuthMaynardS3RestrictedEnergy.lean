import GuthMaynardS3InversionIntegral

open MeasureTheory Set
noncomputable section
namespace GuthMaynardS3RestrictedEnergy

theorem restricted_cauchy_sq
    (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (1/2 : ℝ) 2))
    (hg : ContinuousOn g (Icc (1/2 : ℝ) 2))
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) :
    (∫ x in Icc (1/2 : ℝ) 2, f x * g x)^2 ≤
      (∫ x in Icc (1/2 : ℝ) 2, f x^2) *
        (∫ x in Icc (1/2 : ℝ) 2, g x^2) := by
  let μ : Measure ℝ := volume.restrict (Icc (1/2 : ℝ) 2)
  have hfm : MemLp f 2 μ :=
    (memLp_two_iff_integrable_sq (hf.aestronglyMeasurable measurableSet_Icc)).2
      ((hf.pow 2).integrableOn_compact isCompact_Icc)
  have hgm : MemLp g 2 μ :=
    (memLp_two_iff_integrable_sq (hg.aestronglyMeasurable measurableSet_Icc)).2
      ((hg.pow 2).integrableOn_compact isCompact_Icc)
  have hpq : Real.HolderConjugate 2 2 := by rw [Real.holderConjugate_iff]; norm_num
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ:=μ) (f:=f) (g:=g) hpq
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0)
    (by simpa using hfm) (by simpa using hgm)
  have hh' : (∫ x, f x * g x ∂μ) ≤
      Real.sqrt (∫ x, f x^2 ∂μ) * Real.sqrt (∫ x, g x^2 ∂μ) := by
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh
  have ha : 0 ≤ ∫ x, f x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hb : 0 ≤ ∫ x, g x^2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have hc : 0 ≤ ∫ x, f x*g x ∂μ := integral_nonneg (fun x => mul_nonneg (hf0 x) (hg0 x))
  have hs := pow_le_pow_left₀ hc hh' 2
  rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb] at hs
  exact hs

/-- The paired inversion energy is bounded without a finite-range cardinality loss. -/
theorem integral_product_inversion_le_two
    (F : ℝ → ℝ) (hF : Continuous F) (hF0 : ∀ v, 0 ≤ F v)
    (hF2 : Integrable (fun v => F v^2)) :
    (∫ v in Icc (1/2 : ℝ) 2, F v⁻¹ * F v) ≤
      2 * ∫ v : ℝ, F v^2 := by
  have hi : ContinuousOn (fun v : ℝ => v⁻¹) (Icc (1/2 : ℝ) 2) := by
    apply continuousOn_id.inv₀
    intro v hv
    change v ≠ 0
    linarith [hv.1]
  have hFi := hF.comp_continuousOn hi
  have hs := restricted_cauchy_sq (fun v => F v⁻¹) F hFi hF.continuousOn
    (fun v => hF0 _) hF0
  have hinv := GuthMaynardS3InversionIntegral.integral_inversion_le_four
    (fun v => F v^2) (hF.pow 2) (fun v => sq_nonneg _)
  have hB0 : 0 ≤ ∫ v in Icc (1/2 : ℝ) 2, F v^2 := integral_nonneg (fun v => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_right hinv hB0
  have hP0 : 0 ≤ ∫ v in Icc (1/2 : ℝ) 2, F v⁻¹*F v :=
    integral_nonneg (fun v => mul_nonneg (hF0 _) (hF0 _))
  have hp : (∫ v in Icc (1/2 : ℝ) 2, F v⁻¹*F v) ≤
      2*(∫ v in Icc (1/2 : ℝ) 2, F v^2) := by
    nlinarith [hs,hm]
  have hrest : (∫ v in Icc (1/2 : ℝ) 2, F v^2) ≤ ∫ v : ℝ, F v^2 :=
    setIntegral_le_integral hF2 (Filter.Eventually.of_forall (fun v => sq_nonneg _))
  exact hp.trans (mul_le_mul_of_nonneg_left hrest (by norm_num))
end GuthMaynardS3RestrictedEnergy
#print axioms GuthMaynardS3RestrictedEnergy.restricted_cauchy_sq
#print axioms GuthMaynardS3RestrictedEnergy.integral_product_inversion_le_two
