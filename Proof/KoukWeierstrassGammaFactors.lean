import KoukGaussSeriesToRightHalfPlane
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

/-!
# Normal convergence of the Weierstrass Gamma factors

This is the locally uniform product input for Gauss' digamma series.  The
quadratic cancellation in `(1+u) exp(-u)` is kept explicitly.
-/

namespace KoukWeierstrassGammaFactors

set_option maxHeartbeats 800000

open Complex Filter Function
open scoped BigOperators Topology

noncomputable section

def u (n : ℕ) (z : ℂ) : ℂ := z / ((n + 1 : ℕ) : ℂ)

def gammaFactor (n : ℕ) (z : ℂ) : ℂ :=
  (1 + u n z) * Complex.exp (-u n z)

private def gammaFactorError (n : ℕ) (z : ℂ) : ℂ :=
  gammaFactor n z - 1

private theorem gammaFactor_eq_one_add_error (n : ℕ) (z : ℂ) :
    gammaFactor n z = 1 + gammaFactorError n z := by
  simp [gammaFactorError]

/-- Quadratic cancellation in a single canonical Weierstrass factor. -/
theorem norm_gammaFactorError_le_three_sq
    {n : ℕ} {z : ℂ} (hz : ‖u n z‖ ≤ 1) :
    ‖gammaFactorError n z‖ ≤ 3 * ‖u n z‖ ^ 2 := by
  have hneg : ‖-u n z‖ ≤ 1 := by simpa
  have hquad := Complex.norm_exp_sub_one_sub_id_le hneg
  have hlin := Complex.norm_exp_sub_one_le hneg
  have hid : gammaFactorError n z =
      (Complex.exp (-u n z) - 1 + u n z) +
        u n z * (Complex.exp (-u n z) - 1) := by
    simp [gammaFactorError, gammaFactor]
    ring
  rw [hid]
  calc
    ‖(Complex.exp (-u n z) - 1 + u n z) +
        u n z * (Complex.exp (-u n z) - 1)‖ ≤
      ‖Complex.exp (-u n z) - 1 + u n z‖ +
        ‖u n z * (Complex.exp (-u n z) - 1)‖ := norm_add_le _ _
    _ ≤ ‖u n z‖ ^ 2 + ‖u n z‖ * (2 * ‖u n z‖) := by
      apply add_le_add
      · simpa [sub_eq_add_neg, add_assoc] using hquad
      · rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (by simpa using hlin) (norm_nonneg _)
    _ = 3 * ‖u n z‖ ^ 2 := by ring

private theorem norm_u_le_div (n : ℕ) (z : ℂ) :
    ‖u n z‖ = ‖z‖ / ((n + 1 : ℕ) : ℝ) := by
  rw [u, norm_div]
  congr 1
  exact Complex.norm_natCast (n + 1)

private theorem continuous_gammaFactorError (n : ℕ) :
    Continuous (gammaFactorError n) := by
  unfold gammaFactorError gammaFactor u
  fun_prop

private theorem summable_three_mul_inv_succ_sq :
    Summable (fun n : ℕ => (3 : ℝ) * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
    simpa using ((summable_nat_add_iff 1).2 hbase)
  simpa [div_eq_mul_inv] using hs.mul_left 3

/-- The canonical factors converge locally uniformly on the whole plane. -/
theorem hasProdLocallyUniformlyOn_gammaFactor :
    HasProdLocallyUniformlyOn gammaFactor
      (fun z => ∏' n : ℕ, gammaFactor n z) Set.univ := by
  apply hasProdLocallyUniformlyOn_of_forall_compact isOpen_univ
  intro K hKuniv hKcompact
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z ∈ K, ‖z‖ ≤ R := by
    have hbdd : Bornology.IsBounded K := hKcompact.isBounded
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hbdd
    refine ⟨R, ?_⟩
    intro z hz
    have := hR hz
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  let majorant : ℕ → ℝ := fun n =>
    3 * R ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hmajorant : Summable majorant := by
    dsimp [majorant]
    refine (summable_three_mul_inv_succ_sq.mul_left (R ^ 2)).congr ?_
    intro n
    ring
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ z ∈ K,
      ‖gammaFactorError n z‖ ≤ majorant n := by
    filter_upwards [eventually_ge_atTop ⌈max 0 R⌉₊] with n hn z hzK
    have hRnonneg : 0 ≤ max 0 R := le_max_left _ _
    have hceil : max 0 R ≤ (⌈max 0 R⌉₊ : ℝ) := Nat.le_ceil _
    have hnreal : R ≤ ((n + 1 : ℕ) : ℝ) := by
      have hncast : (⌈max 0 R⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      have hRmax : R ≤ max 0 R := le_max_right _ _
      push_cast
      linarith
    have hdenpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have huNorm : ‖u n z‖ ≤ 1 := by
      rw [norm_u_le_div]
      apply (div_le_one hdenpos).2
      exact (hR z hzK).trans hnreal
    have hquad := norm_gammaFactorError_le_three_sq huNorm
    calc
      ‖gammaFactorError n z‖ ≤ 3 * ‖u n z‖ ^ 2 := hquad
      _ = 3 * (‖z‖ ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
        rw [norm_u_le_div]
        field_simp
      _ ≤ 3 * (R ^ 2 * (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right
        · exact (sq_le_sq₀ (norm_nonneg z)
            ((norm_nonneg z).trans (hR z hzK))).2 (hR z hzK)
        · exact inv_nonneg.mpr (sq_nonneg _)
      _ = majorant n := by simp [majorant, mul_assoc]
  have hprod := Summable.hasProdUniformlyOn_nat_one_add
    hKcompact hmajorant hevent
      (fun n => (continuous_gammaFactorError n).continuousOn)
  convert hprod using 1 <;>
    simp [gammaFactorError]

/-- The factor family is locally uniformly multipliable. -/
theorem multipliableLocallyUniformlyOn_gammaFactor :
    MultipliableLocallyUniformlyOn gammaFactor Set.univ :=
  hasProdLocallyUniformlyOn_gammaFactor.multipliableLocallyUniformlyOn

end
end KoukWeierstrassGammaFactors

#print axioms KoukWeierstrassGammaFactors.norm_gammaFactorError_le_three_sq
#print axioms KoukWeierstrassGammaFactors.hasProdLocallyUniformlyOn_gammaFactor
