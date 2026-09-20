import GuthMaynardLengthComparison

open scoped BigOperators

namespace GuthMaynardEnergy119GCDWeights

noncomputable section

/-- The reciprocal-square tail is bounded by the first omitted reciprocal;
`Icc (D+1) H` is converted exactly to `Ioc D H` before telescoping. -/
theorem sum_inv_sq_tail_le
    {D H : ℕ} (hD : 1 ≤ D) :
    (∑ d ∈ Finset.Icc (D + 1) H, (((d : ℝ) ^ 2)⁻¹)) ≤ (D : ℝ)⁻¹ := by
  by_cases hDH : H < D
  · have hempty : Finset.Icc (D + 1) H = ∅ := by
      apply Finset.Icc_eq_empty
      omega
    rw [hempty]
    simp
  · have hDH' : D ≤ H := Nat.le_of_not_gt hDH
    have hset : Finset.Icc (D + 1) H = Finset.Ioc D H := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    have htail := sum_Ioc_inv_sq_le_sub (α := ℝ)
      (k := D) (n := H) (by omega) hDH'
    calc
      (∑ d ∈ Finset.Ioc D H, (((d : ℝ) ^ 2)⁻¹)) ≤
          (D : ℝ)⁻¹ - (H : ℝ)⁻¹ := htail
      _ ≤ (D : ℝ)⁻¹ := by
        have hnon : 0 ≤ (H : ℝ)⁻¹ := inv_nonneg.mpr (by positivity)
        linarith

/-- The finite reciprocal sum over `[1,H]` is controlled by the harmonic
number and hence by `1 + log(max 1 H)`, including the empty `H=0` case. -/
theorem sum_inv_le_one_add_log_max
    (H : ℕ) :
    (∑ d ∈ Finset.Icc 1 H, (1 / (d : ℝ))) ≤
      1 + Real.log (max 1 (H : ℝ)) := by
  by_cases hH : H = 0
  · subst H
    simp
  · have hH1 : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr hH
    have hsum :
        (∑ d ∈ Finset.Icc 1 H, (1 / (d : ℝ))) = (harmonic H : ℝ) := by
      rw [harmonic_eq_sum_Icc, Rat.cast_sum]
      simp
    rw [hsum]
    have hharm := harmonic_le_one_add_log H
    have hmax : max 1 (H : ℝ) = (H : ℝ) := by
      exact max_eq_right (by exact_mod_cast hH1)
    rw [hmax]
    exact hharm

end
end GuthMaynardEnergy119GCDWeights

#print axioms GuthMaynardEnergy119GCDWeights.sum_inv_sq_tail_le
#print axioms GuthMaynardEnergy119GCDWeights.sum_inv_le_one_add_log_max
