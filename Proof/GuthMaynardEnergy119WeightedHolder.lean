import GuthMaynardEnergy119GCDWeights

open scoped BigOperators

namespace GuthMaynardEnergy119WeightedHolder

open GuthMaynardEnergy119GCDWeights

noncomputable section

/-- Finite Holder after separating the reciprocal-square and reciprocal GCD
weights.  The carrier remains the literal closed tail `Icc (D+1) H`. -/
theorem weighted_holder_tail_le
    {D H : ℕ} (hD : 1 ≤ D)
    {A B C F : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hF : 0 ≤ F) :
    (∑ d ∈ Finset.Icc (D + 1) H,
      Real.sqrt (A / (d : ℝ) ^ 2 + B / (d : ℝ)) *
        Real.sqrt (C / (d : ℝ) ^ 2 + F / (d : ℝ))) ≤
      Real.sqrt (A / (D : ℝ) + B *
        (1 + Real.log (max 1 (H : ℝ)))) *
        Real.sqrt (C / (D : ℝ) + F *
          (1 + Real.log (max 1 (H : ℝ)))) := by
  let S : Finset ℕ := Finset.Icc (D + 1) H
  let X : ℕ → ℝ := fun d => A / (d : ℝ) ^ 2 + B / (d : ℝ)
  let Y : ℕ → ℝ := fun d => C / (d : ℝ) ^ 2 + F / (d : ℝ)
  have hX : ∀ d, 0 ≤ X d := by
    intro d
    dsimp [X]
    exact add_nonneg (div_nonneg hA (sq_nonneg _))
      (div_nonneg hB (by positivity))
  have hY : ∀ d, 0 ≤ Y d := by
    intro d
    dsimp [Y]
    exact add_nonneg (div_nonneg hC (sq_nonneg _))
      (div_nonneg hF (by positivity))
  have hcs :
      (∑ d ∈ S, Real.sqrt (X d) * Real.sqrt (Y d)) ≤
        Real.sqrt (∑ d ∈ S, X d) * Real.sqrt (∑ d ∈ S, Y d) :=
    Real.sum_sqrt_mul_sqrt_le S hX hY
  have hsumX :
      (∑ d ∈ S, X d) =
        A * (∑ d ∈ S, (((d : ℝ) ^ 2)⁻¹)) +
          B * (∑ d ∈ S, (1 / (d : ℝ))) := by
    dsimp [X]
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [one_mul]
  have hsumY :
      (∑ d ∈ S, Y d) =
        C * (∑ d ∈ S, (((d : ℝ) ^ 2)⁻¹)) +
          F * (∑ d ∈ S, (1 / (d : ℝ))) := by
    dsimp [Y]
    simp_rw [div_eq_mul_inv]
    rw [Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [one_mul]
  have hsq :
      (∑ d ∈ S, (((d : ℝ) ^ 2)⁻¹)) ≤ (D : ℝ)⁻¹ := by
    exact sum_inv_sq_tail_le hD
  have hrec :
      (∑ d ∈ S, (1 / (d : ℝ))) ≤
        1 + Real.log (max 1 (H : ℝ)) := by
    have hsubset : S ⊆ Finset.Icc 1 H := by
      intro d hd
      rcases Finset.mem_Icc.mp hd with ⟨hdlo, hdhi⟩
      apply Finset.mem_Icc.mpr
      omega
    have hsubsum :
        (∑ d ∈ S, (1 / (d : ℝ))) ≤
          ∑ d ∈ Finset.Icc 1 H, (1 / (d : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro d hd hnot
      positivity
    exact hsubsum.trans (sum_inv_le_one_add_log_max H)
  have hXbound :
      (∑ d ∈ S, X d) ≤
        A / (D : ℝ) + B * (1 + Real.log (max 1 (H : ℝ))) := by
    rw [hsumX]
    have hAterm := mul_le_mul_of_nonneg_left hsq hA
    have hBterm := mul_le_mul_of_nonneg_left hrec hB
    have hDform : A * (D : ℝ)⁻¹ = A / (D : ℝ) := by
      simp [div_eq_mul_inv]
    calc
      A * (∑ d ∈ S, (((d : ℝ) ^ 2)⁻¹)) +
          B * (∑ d ∈ S, (1 / (d : ℝ))) ≤
          A * (D : ℝ)⁻¹ + B * (1 + Real.log (max 1 (H : ℝ))) :=
        add_le_add hAterm hBterm
      _ = A / (D : ℝ) + B * (1 + Real.log (max 1 (H : ℝ))) := by
        rw [hDform]
  have hYbound :
      (∑ d ∈ S, Y d) ≤
        C / (D : ℝ) + F * (1 + Real.log (max 1 (H : ℝ))) := by
    rw [hsumY]
    have hCterm := mul_le_mul_of_nonneg_left hsq hC
    have hFterm := mul_le_mul_of_nonneg_left hrec hF
    have hDform : C * (D : ℝ)⁻¹ = C / (D : ℝ) := by
      simp [div_eq_mul_inv]
    calc
      C * (∑ d ∈ S, (((d : ℝ) ^ 2)⁻¹)) +
          F * (∑ d ∈ S, (1 / (d : ℝ))) ≤
          C * (D : ℝ)⁻¹ + F * (1 + Real.log (max 1 (H : ℝ))) :=
        add_le_add hCterm hFterm
      _ = C / (D : ℝ) + F * (1 + Real.log (max 1 (H : ℝ))) := by
        rw [hDform]
  have hrootX := Real.sqrt_le_sqrt hXbound
  have hrootY := Real.sqrt_le_sqrt hYbound
  have hprod := mul_le_mul hrootX hrootY
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact hcs.trans hprod

end
end GuthMaynardEnergy119WeightedHolder

#print axioms GuthMaynardEnergy119WeightedHolder.weighted_holder_tail_le
