import JutilaCollarSourceParameters
import JutilaCollarNoLogBudget

/-! Exact final absorption for the canonical source inequality. -/
namespace MAPJutilaCanonicalQuadraticAbsorption

theorem card_le_two_linear_div_detector_sq
    {J V Q F E : ℝ} (hJ : 0 ≤ J) (hV : 2 ≤ V) (hQF : 0 ≤ Q * F)
    (hQE : Q * E ≤ 1)
    (hquad : V ^ 2 * J ^ 2 ≤ Q * (F * J + E * J ^ 2)) :
    J ≤ 2 * Q * F / V ^ 2 := by
  have hV2 : 4 ≤ V ^ 2 := by nlinarith
  have hVpos : 0 < V ^ 2 := by linarith
  by_cases hJ0 : J = 0
  · rw [hJ0]
    exact div_nonneg (by nlinarith) hVpos.le
  · have hJpos : 0 < J := lt_of_le_of_ne hJ (Ne.symm hJ0)
    have hcancel : (V ^ 2 - Q * E) * J ≤ Q * F := by
      apply (mul_le_mul_iff_of_pos_right hJpos).mp
      nlinarith [hquad]
    have hhalf : V ^ 2 / 2 ≤ V ^ 2 - Q * E := by linarith
    have hmain := (mul_le_mul_of_nonneg_right hhalf hJ).trans hcancel
    apply (le_div_iff₀ hVpos).mpr
    nlinarith

noncomputable section
open MAPJutilaCollarSourceParameters MAPJutilaLemma6GenericTailAbsorption
open MAPJutilaCollarNoLogBudget

theorem cutoffPower_logCost_le {δ D sigma : ℝ}
    (hD : 0 < D) (hlog : 0 ≤ Real.log D) (hsigma : sigma ≤ 1)
    (hgeo : SourceGeometry δ D) :
    Real.rpow (lemmaSixDirectCutoff δ D : ℝ) (2 - 2 * sigma) * (1 + Real.log D)^6 ≤
      collarLogCost D δ sigma := by
  have hp : 0 ≤ 2 - 2 * sigma := by linarith
  have hbase := Real.rpow_le_rpow (Nat.cast_nonneg (lemmaSixDirectCutoff δ D)) hgeo.x_upper hp
  have heq : Real.rpow (lemmaSixSmoothScale δ D * (Real.log D)^2) (2 - 2 * sigma) =
      Real.rpow D (2 * (1 + 12 * δ) * (1 - sigma)) *
        Real.rpow (Real.log D) (4 * (1 - sigma)) := by
    unfold lemmaSixSmoothScale
    simp only [Real.rpow_eq_pow]
    rw [Real.mul_rpow (Real.rpow_nonneg hD.le _) (sq_nonneg _)]
    rw [← Real.rpow_mul hD.le]
    rw [show (Real.log D)^2 = (Real.log D)^(2 : ℝ) by norm_num,
      ← Real.rpow_mul hlog]
    congr 1 <;> congr 1 <;> ring
  simp only [Real.rpow_eq_pow] at heq
  rw [heq] at hbase
  exact mul_le_mul_of_nonneg_right hbase (pow_nonneg (by linarith) _)

end

end MAPJutilaCanonicalQuadraticAbsorption
#print axioms MAPJutilaCanonicalQuadraticAbsorption.card_le_two_linear_div_detector_sq

#print axioms MAPJutilaCanonicalQuadraticAbsorption.cutoffPower_logCost_le
