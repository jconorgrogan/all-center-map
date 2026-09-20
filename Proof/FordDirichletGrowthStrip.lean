import FordHurwitzGrowthStrip
import FordHurwitzLFunctionTransfer

noncomputable section
namespace FordDirichletGrowthStrip
open FordFiniteGrowthBound

/-- Growth of the actual continued Dirichlet L-function, uniform in the
character and throughout a strip crossing the line of absolute convergence. -/
theorem dirichlet_growth_strip :
    ∃ R : ℝ, 2 ≤ R ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
      (t eta sigma : ℝ),
      2 ≤ t → 0 ≤ eta → eta ≤ (1 : ℝ) / 2 → 1 - eta ≤ sigma → sigma ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
        (N : ℝ) * ((N : ℝ) ^ 2 +
          (6 * Real.log t * commonEnvelope R t eta + 14)) := by
  obtain ⟨R, hR, hH⟩ := FordHurwitzGrowthStrip.hurwitz_growth_strip
  refine ⟨R, hR, ?_⟩
  intro N hN χ t eta sigma ht heta heta1 hsigma hsigma2
  have hsigma0 : 0 ≤ sigma := by linarith
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hC : 0 ≤ commonEnvelope R t eta := by
    unfold commonEnvelope
    positivity
  apply FordHurwitzLFunctionTransfer.norm_dirichlet_LFunction_le χ
    (by simpa using hsigma0) (by simpa using hsigma2)
    (by simpa using (show 0 < t by linarith)) (by positivity)
  intro u hu
  exact hH t u eta sigma ht hu.1 hu.2 heta heta1 hsigma hsigma2

end FordDirichletGrowthStrip
#print axioms FordDirichletGrowthStrip.dirichlet_growth_strip
