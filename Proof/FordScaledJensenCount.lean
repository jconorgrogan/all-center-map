import Mathlib.Analysis.Complex.JensenFormula

open scoped BigOperators
noncomputable section
namespace FordScaledJensenCount

open Complex Set Filter Metric

/-- The natural analytic zero multiplicity at a point. -/
def analyticMultiplicity (f : ℂ → ℂ) (z : ℂ) : ℕ :=
  analyticOrderNatAt f z

/-- A generic Jensen count with the literal outer radius `6a` and inner
radius `3a`.  The finite-set formulation is enough for later zero sums. -/
theorem finite_analyticMultiplicity_le
    {a : ℝ} (ha : 0 < a) {c : ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall c (6 * a)))
    (hfc : f c ≠ 0) {G : ℝ} (hG : 0 < G)
    (hbound : ∀ z ∈ closedBall c (6 * a), ‖f z‖ ≤ G)
    (S : Finset ℂ)
    (hS : ∀ z ∈ S, z ∈ closedBall c (3 * a)) :
    (∑ z ∈ S, (analyticMultiplicity f z : ℝ)) ≤
      (Real.log G - Real.log ‖f c‖) / Real.log 2 := by
  let F : ℂ → ℂ := fun z ↦ f z / f c
  let U : Set ℂ := closedBall c |3 * a|
  let V : Set ℂ := closedBall c |6 * a|
  have ha3 : 0 < 3 * a := by positivity
  have ha6 : 0 < 6 * a := by positivity
  have hUeq : U = closedBall c (3 * a) := by
    dsimp [U]
    rw [abs_of_pos ha3]
  have hVeq : V = closedBall c (6 * a) := by
    dsimp [V]
    rw [abs_of_pos ha6]
  have hfV : AnalyticOnNhd ℂ f V := by
    simpa [hVeq] using hf
  have hFan : AnalyticOnNhd ℂ F V := by
    dsimp [F]
    simpa using hfV.div_const
  have hUV : U ⊆ V := by
    simpa [U, V, abs_of_pos ha3, abs_of_pos ha6] using
      (closedBall_subset_closedBall (by linarith : (3 : ℝ) * a ≤ 6 * a))
  have hFanU : AnalyticOnNhd ℂ F U := hFan.mono hUV
  have hfcpos : 0 < ‖f c‖ := norm_pos_iff.mpr hfc
  have hM : 1 ≤ G / ‖f c‖ := by
    apply (le_div_iff₀ hfcpos).2
    have hcball : c ∈ closedBall c (6 * a) := mem_closedBall_self (by positivity)
    simpa using hbound c hcball
  have hFc : F c ≠ 0 := by
    dsimp [F]
    exact div_ne_zero hfc hfc
  have hcircle : ∀ z ∈ sphere c |6 * a|, ‖F z‖ ≤ G / ‖f c‖ := by
    intro z hz
    have hzV : z ∈ V := by
      exact sphere_subset_closedBall hz
    have hzball : z ∈ closedBall c (6 * a) := by
      simpa [hVeq] using hzV
    have hzf := hbound z hzball
    dsimp [F]
    rw [norm_div]
    exact div_le_div_of_nonneg_right hzf hfcpos.le
  have hJensen := AnalyticOnNhd.sum_divisor_le
    (f := F) (c := c) (r := 3 * a) (R := 6 * a)
    (M := G / ‖f c‖)
    (by rw [abs_of_pos ha3]; positivity)
    (by rw [abs_of_pos ha3, abs_of_pos ha6]; nlinarith)
    hM hFan hFc hcircle
  have hJensen' :
      (↑(∑ᶠ z : ℂ, MeromorphicOn.divisor F U z) : ℝ) ≤
        (Real.log G - Real.log ‖f c‖) / Real.log 2 := by
    have hratio : (6 * a) / (3 * a) = (2 : ℝ) := by
      field_simp
      norm_num
    have hlogratio : Real.log ((G / ‖f c‖) / ‖F c‖) =
        Real.log G - Real.log ‖f c‖ := by
      rw [show ‖F c‖ = 1 by simp [F, hfc], div_one,
        Real.log_div (ne_of_gt hG) hfcpos.ne']
    simpa [U, V, hratio, hlogratio, abs_of_pos ha3, abs_of_pos ha6] using hJensen
  let D : ℂ → ℤ := MeromorphicOn.divisor F U
  have hDfinite : D.support.Finite := by
    dsimp [D]
    exact (MeromorphicOn.divisor F U).finiteSupport (isCompact_closedBall _ _)
  have hmult (z : ℂ) (hz : z ∈ S) :
      (analyticMultiplicity f z : ℤ) = D z := by
    have hzinner : z ∈ U := by simpa [U, hUeq] using hS z hz
    have hzouter : z ∈ V := by
      have hdist : dist z c ≤ 3 * a := mem_closedBall.mp (hS z hz)
      have hz6 : z ∈ closedBall c (6 * a) := by
        rw [mem_closedBall]
        exact hdist.trans (by linarith)
      simpa [V, abs_of_pos ha6] using hz6
    have hdiv := MeromorphicOn.AnalyticOnNhd.divisor_apply hFanU hzinner
    have hconstAnalytic :
        AnalyticAt ℂ (fun _ : ℂ ↦ (f c)⁻¹) z := by fun_prop
    have hFeq : F = fun w ↦ f w * (f c)⁻¹ := by
      funext w
      simp [F, div_eq_mul_inv]
    by_cases htop : analyticOrderAt f z = ⊤
    · have hFtop : analyticOrderAt F z = ⊤ := by
        rw [hFeq]
        exact analyticOrderAt_mul_eq_top_of_left htop
      dsimp [analyticMultiplicity, D]
      rw [hdiv, hFtop]
      simp [analyticOrderNatAt, htop]
    · have hmul := analyticOrderAt_mul (hfV z hzouter) hconstAnalytic
      have hconst : analyticOrderAt (fun _ : ℂ ↦ (f c)⁻¹) z = 0 := by
        apply hconstAnalytic.analyticOrderAt_eq_zero.mpr
        simp [hfc]
      have horder : analyticOrderAt F z = analyticOrderAt f z := by
        have hmul' :
            analyticOrderAt (fun w ↦ f w * (f c)⁻¹) z = analyticOrderAt f z := by
          simpa only [Pi.mul_apply] using hmul.trans (by rw [hconst, add_zero])
        rw [hFeq, hmul']
      have hnat := Nat.cast_analyticOrderNatAt htop
      dsimp [analyticMultiplicity, D]
      rw [hdiv, horder, ← hnat]
      simp
  let T : Finset ℂ := hDfinite.toFinset
  let W : Finset ℂ := S ∪ T
  have hWnonneg : ∀ z ∈ W, 0 ≤ (D z : ℝ) := by
    intro z hz
    have hdivnonneg : 0 ≤ D z := by
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hFanU z
    exact_mod_cast hdivnonneg
  have hDsupport : Function.support D ⊆ W := by
    intro z hz
    have hzD : D z ≠ 0 := by
      intro hzero
      apply hz
      simp [hzero]
    exact Finset.mem_union_right S
      ((Set.Finite.mem_toFinset hDfinite).mpr hzD)
  have hDsum :
      (∑ᶠ z : ℂ, D z) = ∑ z ∈ W, D z := by
    rw [finsum_eq_sum_of_support_subset _ hDsupport]
  calc
    (∑ z ∈ S, (analyticMultiplicity f z : ℝ)) =
        ∑ z ∈ S, (D z : ℝ) := by
      apply Finset.sum_congr rfl
      intro z hz
      exact_mod_cast hmult z hz
    _ ≤ ∑ z ∈ W, (D z : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_union_left)
      intro z hzW hznot
      exact hWnonneg z hzW
    _ = (↑(∑ᶠ z : ℂ, D z) : ℝ) := by
      rw [hDsum]
      simp
    _ ≤ (Real.log G - Real.log ‖f c‖) / Real.log 2 := by
      simpa [D, U] using hJensen'

end FordScaledJensenCount

#print axioms FordScaledJensenCount.finite_analyticMultiplicity_le
