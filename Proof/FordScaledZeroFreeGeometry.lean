import FordScaledDiskEvaluation

noncomputable section
namespace FordScaledZeroFreeGeometry
open FordScaledDiskGrowth FordScaledDiskEvaluation

def derivativeConstant : ℝ := 20 + 1 / (2 * Real.log 2)
def remainderConstant : ℝ := 5 * derivativeConstant + 9375 * Real.log 2
def logBudget (D : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  1 + D + 3 * Real.log (N : ℝ) + 2 * Real.log (Real.log (t + 3))

theorem derivativeConstant_pos : 0 < derivativeConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold derivativeConstant
  positivity

theorem one_le_remainderConstant : 1 ≤ remainderConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : 0 < 1 / (2 * Real.log 2) := by positivity
  unfold remainderConstant derivativeConstant
  nlinarith

theorem one_le_logBudget {D t : ℝ} (hD : 0 < D) (N : ℕ) [NeZero N]
    (ht : 3 ≤ t) : 1 ≤ logBudget D N t := by
  have hN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NeZero.one_le : 1 ≤ N))
  have hT : 0 ≤ Real.log (Real.log (t + 3)) := Real.log_nonneg (disk_geometry ht).1
  unfold logBudget
  linarith

theorem logBudget_mono (D : ℝ) (N : ℕ) {t u : ℝ} (ht : 3 ≤ t)
    (htu : t ≤ u) : logBudget D N t ≤ logBudget D N u := by
  have hlog := (disk_geometry ht).1
  have h1 : Real.log (t + 3) ≤ Real.log (u + 3) :=
    Real.log_le_log (by linarith) (by linarith)
  have h2 := Real.log_le_log (by linarith : 0 < Real.log (t + 3)) h1
  unfold logBudget
  linarith

theorem budget_over_scale_mono {D t u : ℝ} (hD : 0 < D) (N : ℕ) [NeZero N]
    (ht : 3 ≤ t) (htu : t ≤ u) :
    logBudget D N t / diskScale t ≤ logBudget D N u / diskScale u := by
  have ha := (disk_geometry ht).2.1
  have hau := (disk_geometry (ht.trans htu)).2.1
  have hB := one_le_logBudget hD N ht
  calc
    logBudget D N t / diskScale t ≤ logBudget D N t / diskScale u :=
      div_le_div_of_nonneg_left (by linarith) hau (diskScale_antitone ht htu)
    _ ≤ logBudget D N u / diskScale u :=
      div_le_div_of_nonneg_right (logBudget_mono D N ht htu) hau.le

/-- Absorb the zeta error into the same thin-disk scale as both L remainders. -/
theorem total_error_le {D t : ℝ} (hD : 0 < D) (N : ℕ) [NeZero N]
    (ht : 3 ≤ t) :
    4 * (derivativeConstant * logBudget D N t / diskScale t) +
        derivativeConstant * logBudget D N (2 * t) / diskScale (2 * t) +
        300000 * Real.log 2 ≤
      remainderConstant * logBudget D N (2 * t) / diskScale (2 * t) := by
  have ht2 : 3 ≤ 2 * t := by linarith
  have ha := (disk_geometry ht2).2.1
  have hah := (disk_geometry ht2).2.2.1
  have hB := one_le_logBudget hD N ht2
  have hratio : 32 ≤ logBudget D N (2 * t) / diskScale (2 * t) := by
    apply (le_div_iff₀ ha).2
    linarith
  have hmono := mul_le_mul_of_nonneg_left
    (budget_over_scale_mono hD N ht (by linarith : t ≤ 2 * t))
    derivativeConstant_pos.le
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have habsorb := mul_le_mul_of_nonneg_left hratio
    (by positivity : 0 ≤ 9375 * Real.log 2)
  simp only [← mul_div_assoc] at hmono habsorb
  unfold remainderConstant
  calc
    _ ≤ 5 * derivativeConstant * logBudget D N (2 * t) / diskScale (2 * t) +
        9375 * Real.log 2 * logBudget D N (2 * t) / diskScale (2 * t) := by
      ring_nf at hmono habsorb ⊢
      linarith
    _ = _ := by ring

end FordScaledZeroFreeGeometry
#print axioms FordScaledZeroFreeGeometry.total_error_le
#print axioms FordScaledZeroFreeGeometry.budget_over_scale_mono
