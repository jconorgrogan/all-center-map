import MRTProposition51ProjectionHighGeometry

/-!
# Cauchy step for the p.47 rescaled arithmetic window

The page-47 low-frequency argument eventually produces the same rescaled
centered coefficient window already used on p.46.  This module proves the
normalized dual-function Cauchy estimate uniformly on the full constant
quarter range needed there.
-/

namespace MAPMRTFaithfulLowWindowCauchy

open MeasureTheory
open MAPMRTCorollary53Source MAPMRTProposition51ProjectionHighGeometry

noncomputable section

theorem aestronglyMeasurable_scaledCenteredWindowSum
    (X H lambda : ℝ) (f : ℕ → ℂ) :
    AEStronglyMeasurable (scaledCenteredWindowSum X H lambda f) := by
  have hsquare := integrable_sq_scaledCenteredWindowSum X H lambda f
  have hmeas : AEStronglyMeasurable (fun x : ℝ ↦
      Real.sqrt (scaledCenteredWindowSum X H lambda f x ^ 2)) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hsquare.aestronglyMeasurable
  apply hmeas.congr
  filter_upwards with x
  rw [Real.sqrt_sq (scaledCenteredWindowSum_nonneg X H lambda f x)]

theorem memLp_two_scaledCenteredWindowSum
    (X H lambda : ℝ) (f : ℕ → ℂ) :
    MemLp (scaledCenteredWindowSum X H lambda f) 2 := by
  have hm := aestronglyMeasurable_scaledCenteredWindowSum X H lambda f
  rw [memLp_two_iff_integrable_sq_norm hm]
  have hi := integrable_sq_scaledCenteredWindowSum X H lambda f
  apply hi.congr
  filter_upwards with x
  rw [Real.norm_eq_abs,
    abs_of_nonneg (scaledCenteredWindowSum_nonneg X H lambda f x)]

/-- Squared Cauchy estimate for an L2-normalized dual function and the
rescaled arithmetic window. -/
theorem integral_norm_mul_scaledWindow_sq_le
    {X H lambda : ℝ} {f : ℕ → ℂ} {g : ℝ → ℂ}
    (hg : MemLp g 2) (hgNorm : (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1)
    (hH : 0 ≤ H) (hlambda : 1 / 8 ≤ lambda)
    (hlambda' : lambda ≤ 17 / 4) :
    (∫ x : ℝ, ‖g x‖ * scaledCenteredWindowSum X H lambda f x) ^ 2 ≤
      1088 * ordinarySlidingMass X H f := by
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr (by norm_num)
  have hgNormFn : MemLp (fun x : ℝ ↦ ‖g x‖) (ENNReal.ofReal (2 : ℝ)) := by
    simpa using hg.norm
  have hwLp : MemLp (scaledCenteredWindowSum X H lambda f)
      (ENNReal.ofReal (2 : ℝ)) := by
    simpa using memLp_two_scaledCenteredWindowSum X H lambda f
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (g x))
    (Filter.Eventually.of_forall fun x ↦
      scaledCenteredWindowSum_nonneg X H lambda f x)
    hgNormFn hwLp
  have hwindow := integral_sq_scaledCenteredWindowSum_quarter_range
    (X := X) (f := f) hH hlambda hlambda'
  have hleft0 : 0 ≤ ∫ x : ℝ,
      ‖g x‖ * scaledCenteredWindowSum X H lambda f x := by
    exact integral_nonneg fun x ↦ mul_nonneg (norm_nonneg _)
      (scaledCenteredWindowSum_nonneg X H lambda f x)
  have hgEnergy0 : 0 ≤ ∫ x : ℝ, ‖g x‖ ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hwEnergy0 : 0 ≤ ∫ x : ℝ,
      scaledCenteredWindowSum X H lambda f x ^ 2 :=
    integral_nonneg fun x ↦ sq_nonneg _
  have hholder' :
      (∫ x : ℝ, ‖g x‖ * scaledCenteredWindowSum X H lambda f x) ≤
        Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ,
            scaledCenteredWindowSum X H lambda f x ^ 2) := by
    simpa [Real.sqrt_eq_rpow] using hholder
  have hsqrtG : Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact hgNorm
  have hnonnegMass : 0 ≤ ordinarySlidingMass X H f := by
    unfold ordinarySlidingMass
    positivity
  have hnormBound :
      (∫ x : ℝ, ‖g x‖ * scaledCenteredWindowSum X H lambda f x) ≤
        Real.sqrt (1088 * ordinarySlidingMass X H f) := by
    calc
      _ ≤ Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) *
          Real.sqrt (∫ x : ℝ,
            scaledCenteredWindowSum X H lambda f x ^ 2) := hholder'
      _ ≤ 1 * Real.sqrt (∫ x : ℝ,
            scaledCenteredWindowSum X H lambda f x ^ 2) := by
        gcongr
      _ ≤ Real.sqrt (1088 * ordinarySlidingMass X H f) := by
        simpa using Real.sqrt_le_sqrt hwindow
  have hsquare := pow_le_pow_left₀ hleft0 hnormBound 2
  calc
    _ ≤ (Real.sqrt (1088 * ordinarySlidingMass X H f)) ^ 2 := hsquare
    _ = 1088 * ordinarySlidingMass X H f :=
      Real.sq_sqrt (mul_nonneg (by norm_num) hnonnegMass)

#print axioms integral_norm_mul_scaledWindow_sq_le

end
end MAPMRTFaithfulLowWindowCauchy
