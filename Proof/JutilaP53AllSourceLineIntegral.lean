import JutilaP53SourceLineIntegral
import JutilaP53PrincipalSourceLineIntegral

/-! # A uniform source-line integral estimate for every ambient character -/
namespace MAPJutilaP53AllSourceLineIntegral
open Complex Real MeasureTheory
open MAPJutilaP53TwoScaleContour
noncomputable section

theorem exists_all_sourceLine_integrable_and_norm_integral_le
    {epsilon : ℝ} (heps : 0 < epsilon) (hepsHi : epsilon ≤ 1 / 8) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q)
      (s : ℂ) (U V : ℝ), 0 < U → 0 < V →
      0 ≤ s.re → s.re ≤ 2 * epsilon →
      Integrable (fun t : ℝ => p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)) ∧
      ‖∫ t : ℝ, p53TwoScaleContourIntegrand chi s U V
        (((-1 + epsilon : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
        K * Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) *
          (Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon)) := by
  obtain ⟨Kn, hKn, hn⟩ :=
    MAPJutilaP53SourceLineIntegral.exists_sourceLine_integrable_and_norm_integral_le heps hepsHi
  obtain ⟨Kp, hKp, hp⟩ :=
    MAPJutilaP53PrincipalSourceLineIntegral.exists_principal_sourceLine_integrable_and_norm_integral_le
      heps hepsHi
  refine ⟨Kn + Kp, add_pos hKn hKp, ?_⟩
  intro q _inst chi s U V hU hV hsLo hsHi
  have hB : 0 ≤ Real.rpow ((q : ℝ) * (1 + |s.im|)) (1 / 2) :=
    Real.rpow_nonneg (by positivity) _
  have hD : 0 ≤ Real.rpow U (-1 + epsilon) + Real.rpow V (-1 + epsilon) :=
    add_nonneg (Real.rpow_nonneg hU.le _) (Real.rpow_nonneg hV.le _)
  by_cases hchi : chi = 1
  · subst chi
    obtain ⟨hInt, hbound⟩ := hp q s U V hU hV hsLo hsHi
    refine ⟨hInt, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Kp ≤ Kn + Kp) hB) hD
  · obtain ⟨hInt, hbound⟩ := hn q chi hchi s U V hU hV hsLo hsHi
    refine ⟨hInt, hbound.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Kn ≤ Kn + Kp) hB) hD
end
end MAPJutilaP53AllSourceLineIntegral
#print axioms MAPJutilaP53AllSourceLineIntegral.exists_all_sourceLine_integrable_and_norm_integral_le
