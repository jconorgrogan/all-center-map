import FordScaledDiskGrowth

noncomputable section
namespace FordScaledDiskEvaluation
open FordScaledDiskGrowth

theorem diskScale_antitone {t u : ℝ} (ht : 3 ≤ t) (htu : t ≤ u) :
    diskScale u ≤ diskScale t := by
  have hlog := (disk_geometry ht).1
  unfold diskScale FordGrowthWidth.widthEta
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ FordAllLambdaOffsetBound.savingCoeff_pos.le
  exact Real.rpow_le_rpow_of_nonpos (by linarith)
    (Real.log_le_log (by linarith) (by linarith)) (by norm_num)

/-- The evaluation point just right of one lies strictly inside the thin disk. -/
theorem evaluation_mem_ball {t δ : ℝ} (ht : 3 ≤ t) (hδ : 0 < δ)
    (hδa : δ ≤ diskScale t) :
    ((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ) ∈
      Metric.ball (diskCenter t) (diskScale t) := by
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ)) - diskCenter t =
      ((δ - diskScale t : ℝ) : ℂ) := by
    unfold diskCenter
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hδa)]
  linarith

/-- A zero at the evaluation ordinate and within one scale of the line one
belongs to the strict three-scale support. -/
theorem zero_mem_inner_ball {t : ℝ} {ρ : ℂ} (ht : 3 ≤ t)
    (him : ρ.im = t) (hβ : ρ.re ≤ 1) (hgap : 1 - ρ.re ≤ diskScale t) :
    ρ ∈ Metric.ball (diskCenter t) (3 * diskScale t) := by
  have ha := (disk_geometry ht).2.1
  rw [Metric.mem_ball, dist_eq_norm]
  have heq : ρ - diskCenter t = ((ρ.re - 1 - diskScale t : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [diskCenter, him] <;> ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonpos (by linarith : ρ.re - 1 - diskScale t ≤ 0)]
  linarith

end FordScaledDiskEvaluation
#print axioms FordScaledDiskEvaluation.diskScale_antitone
#print axioms FordScaledDiskEvaluation.evaluation_mem_ball
#print axioms FordScaledDiskEvaluation.zero_mem_inner_ball
