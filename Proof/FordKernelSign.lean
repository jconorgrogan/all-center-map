import FordDirichletKernelSum

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordKernelSign
open FordDirichletPointwise

lemma dirichlet_neg (L : ℕ) (x : ℝ) :
    dirichletSum L (-x) = conj (dirichletSum L x) := by
  unfold dirichletSum
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

lemma norm_dirichlet_neg (L : ℕ) (x : ℝ) :
    ‖dirichletSum L (-x)‖ = ‖dirichletSum L x‖ := by
  rw [dirichlet_neg, Complex.norm_conj]

lemma norm_dirichlet_mul_abs (L : ℕ) (d gamma : ℝ) :
    ‖dirichletSum L (d * gamma)‖ = ‖dirichletSum L (d * |gamma|)‖ := by
  by_cases hg : 0 ≤ gamma
  · rw [abs_of_nonneg hg]
  · rw [abs_of_neg (lt_of_not_ge hg), mul_neg, norm_dirichlet_neg]

/-- The literal capped kernel bound for either sign of a nonzero coefficient. -/
theorem kernel_sum_le_abs_min {K L q : ℕ} {gamma : ℝ}
    (hK : 2 ≤ K) (hL : 2 ≤ L) (hq : L < 2 ^ q) (hg : gamma ≠ 0) :
    (∑ d ∈ FordDirichletShells.diffSet K, ‖dirichletSum L ((d : ℝ) * gamma)‖) ≤
      (L : ℝ) * min (2 * (K : ℝ))
        (6 + (4 * (q : ℝ) + 2) * (K : ℝ) / L +
          6 * (K : ℝ) * |gamma| + (4 * (q : ℝ) + 2) / ((L : ℝ) * |gamma|)) := by
  simp_rw [norm_dirichlet_mul_abs L _ gamma]
  exact FordDirichletKernelSum.unnormalized_sum_le_mul_min hK hL hq (abs_pos.mpr hg)

end FordKernelSign
#print axioms FordKernelSign.dirichlet_neg
#print axioms FordKernelSign.kernel_sum_le_abs_min
