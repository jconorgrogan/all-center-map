import RamachandraWeightedCauchy

/-!
# Almost-everywhere weighted Cauchy on the Mellin line

The sharp functional-factor envelope excludes the single ordinate
`t+v=0`.  This AE version is the exact consumer needed by the contour
assembly; it prevents a null diagonal from being promoted into a false
pointwise premise.
-/

namespace RamachandraWeightedCauchyAE

open Complex MeasureTheory

noncomputable section

/-- For each external ordinate, the sharp functional-factor estimate fails
only at one null Mellin ordinate. -/
theorem eventually_t_add_ne_zero (t : ℝ) : ∀ᵐ v : ℝ, t + v ≠ 0 := by
  have hne : ∀ᵐ v : ℝ, v ≠ -t := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with v hv
  intro hzero
  apply hv
  linarith

theorem norm_integral_sq_le_integral_mul_integral_ae
    (f : ℝ → ℂ) (w g : ℝ → ℝ)
    (hf : Integrable f)
    (hw : Integrable w) (hg : Integrable g)
    (hw0 : ∀ x, 0 ≤ w x) (hg0 : ∀ x, 0 ≤ g x)
    (hfg : ∀ᵐ x, ‖f x‖ ≤ Real.sqrt (w x) * Real.sqrt (g x)) :
    ‖∫ x, f x‖ ^ 2 ≤ (∫ x, w x) * ∫ x, g x := by
  let sw : ℝ → ℝ := fun x => Real.sqrt (w x)
  let sg : ℝ → ℝ := fun x => Real.sqrt (g x)
  have hswMeas : AEStronglyMeasurable sw :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hw.1
  have hsgMeas : AEStronglyMeasurable sg :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hg.1
  have hsw2 : MemLp sw 2 := by
    rw [memLp_two_iff_integrable_sq hswMeas]
    have heq : (fun x => sw x ^ 2) = w := by
      funext x
      exact Real.sq_sqrt (hw0 x)
    rwa [heq]
  have hsg2 : MemLp sg 2 := by
    rw [memLp_two_iff_integrable_sq hsgMeas]
    have heq : (fun x => sg x ^ 2) = g := by
      funext x
      exact Real.sq_sqrt (hg0 x)
    rwa [heq]
  have hsw2' : MemLp sw (ENNReal.ofReal (2 : ℝ)) := by
    norm_num
    exact hsw2
  have hsg2' : MemLp sg (ENNReal.ofReal (2 : ℝ)) := by
    norm_num
    exact hsg2
  have hprodInt : Integrable (sw * sg) := hsw2.integrable_mul hsg2
  have hnorm : ‖∫ x, f x‖ ≤ ∫ x, sw x * sg x := by
    calc
      ‖∫ x, f x‖ ≤ ∫ x, ‖f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, sw x * sg x := by
        apply integral_mono_ae hf.norm hprodInt
        simpa [sw, sg, Pi.mul_def] using! hfg
  have hholder := integral_mul_norm_le_Lp_mul_Lq
    (μ := volume) (f := sw) (g := sg)
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two hsw2' hsg2'
  have hsw0 (x : ℝ) : 0 ≤ sw x := Real.sqrt_nonneg _
  have hsg0 (x : ℝ) : 0 ≤ sg x := Real.sqrt_nonneg _
  have hleft : (∫ x, ‖sw x‖ * ‖sg x‖) = ∫ x, sw x * sg x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hsw0 x), Real.norm_of_nonneg (hsg0 x)]
  rw [hleft] at hholder
  have hwInt0 : 0 ≤ ∫ x, w x := integral_nonneg (fun x => hw0 x)
  have hgInt0 : 0 ≤ ∫ x, g x := integral_nonneg (fun x => hg0 x)
  have hswInt : (∫ x, ‖sw x‖ ^ (2 : ℝ)) = ∫ x, w x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hsw0 x)]
    norm_num [sw, Real.sq_sqrt (hw0 x)]
  have hsgInt : (∫ x, ‖sg x‖ ^ (2 : ℝ)) = ∫ x, g x := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (hsg0 x)]
    norm_num [sg, Real.sq_sqrt (hg0 x)]
  rw [hswInt, hsgInt] at hholder
  norm_num at hholder
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hholder
  have hchain : ‖∫ x, f x‖ ≤
      Real.sqrt (∫ x, w x) * Real.sqrt (∫ x, g x) := hnorm.trans hholder
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hchain
  calc
    ‖∫ x, f x‖ ^ 2 ≤
        (Real.sqrt (∫ x, w x) * Real.sqrt (∫ x, g x)) ^ 2 := hsquare
    _ = (∫ x, w x) * ∫ x, g x := by
      rw [mul_pow, Real.sq_sqrt hwInt0, Real.sq_sqrt hgInt0]

end
end RamachandraWeightedCauchyAE

#print axioms RamachandraWeightedCauchyAE.norm_integral_sq_le_integral_mul_integral_ae
#print axioms RamachandraWeightedCauchyAE.eventually_t_add_ne_zero
