import FordScaledLLogDerivativeUpper
import FordScaledZeroFreeGeometry
import FordThreeFourOneGap
import KoukTheorem12ThreePrimitive

noncomputable section
namespace FordScaledZeroFree
open FordScaledDiskGrowth FordScaledDiskEvaluation FordScaledZeroFreeGeometry

/-- Uniform zero exclusion from the actual thin-disk L-function estimate.
The modulus and height losses are retained explicitly. -/
theorem actual_zero_gap :
    ∃ D : ℝ, 0 < D ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (t : ℝ), 3 ≤ t → ∀ ρ : ℂ,
      DirichletCharacter.LFunction χ ρ = 0 → ρ.im = t →
      diskScale (2 * t) /
        (200 * remainderConstant * logBudget D N (2 * t)) ≤ 1 - ρ.re := by
  obtain ⟨D, hD, hu⟩ :=
    FordScaledLLogDerivativeUpper.exists_uniform_actual_negLogDeriv_upper
  refine ⟨D, hD, ?_⟩
  intro N hN χ t ht ρ hzero him
  have ht2 : 3 ≤ 2 * t := by linarith
  have ha := (disk_geometry ht2).2.1
  have ha32 := (disk_geometry ht2).2.2.1
  have ha21 := diskScale_antitone ht (by linarith : t ≤ 2 * t)
  have hB := one_le_logBudget hD N ht2
  have hC := one_le_remainderConstant
  have hBp : 0 < logBudget D N (2 * t) := by linarith
  have hCp : 0 < remainderConstant := by linarith
  let δ : ℝ := diskScale (2 * t) /
    (2 * remainderConstant * logBudget D N (2 * t))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hden : 1 ≤ 2 * remainderConstant * logBudget D N (2 * t) := by
    nlinarith
  have hδa2 : δ ≤ diskScale (2 * t) := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hδa1 : δ ≤ diskScale t := hδa2.trans ha21
  have hδ1 : δ ≤ 1 := by linarith
  have hδR : δ * (remainderConstant * logBudget D N (2 * t) /
      diskScale (2 * t)) ≤ (1 : ℝ) / 2 := by
    dsimp [δ]
    apply le_of_eq
    field_simp
  have hδ100 : δ / 100 = diskScale (2 * t) /
      (200 * remainderConstant * logBudget D N (2 * t)) := by
    dsimp [δ]
    ring
  rw [← hδ100]
  have hβ := FordScaledLZeroReal.LFunction_eq_zero_re_le_one χ hzero
  by_cases hnear : 1 - ρ.re ≤ diskScale t
  · have h1 := (hu N χ t ht δ hδ hδa1).2 ρ hzero him hnear
    have h2 := (hu N (χ ^ 2) (2 * t) ht2 δ hδ hδa2).1
    have hz := MAPKoukTheorem12ThreePrimitive.neg_logDeriv_riemannZeta_re_le
      (show 1 < 1 + δ by linarith) (show 1 + δ ≤ 2 by linarith)
    have h341 := MAPZeroFreeSiegelSpine.threeCharacter_neg_logDeriv_re_nonneg
      χ (show 1 < 1 + δ by linarith) t
    have herr := total_error_le hD N ht
    change (-logDeriv (DirichletCharacter.LFunction χ)
      (((1 + δ : ℝ) : ℂ) + Complex.I * (t : ℂ))).re ≤
      derivativeConstant * logBudget D N t / diskScale t -
        1 / (δ + (1 - ρ.re)) at h1
    change (-logDeriv (DirichletCharacter.LFunction (χ ^ 2))
      (((1 + δ : ℝ) : ℂ) + Complex.I * ((2 * t : ℝ) : ℂ))).re ≤
      derivativeConstant * logBudget D N (2 * t) / diskScale (2 * t) at h2
    have hineq : 4 / (δ + (1 - ρ.re)) ≤ 3 / δ +
        remainderConstant * logBudget D N (2 * t) / diskScale (2 * t) := by
      simp only [add_sub_cancel_left] at hz
      push_cast at h341 hz h1 h2
      ring_nf at h341 hz h1 h2 herr ⊢
      linarith only [h341, hz, h1, h2, herr]
    exact FordThreeFourOneGap.delta_div_100_le_epsilon hδ (by linarith) hδR hineq
  · linarith

end FordScaledZeroFree
#print axioms FordScaledZeroFree.actual_zero_gap
