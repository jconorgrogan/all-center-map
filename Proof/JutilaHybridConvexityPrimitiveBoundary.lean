import HuxleyPrimitiveFunctionalEquation
import NearOneThreeLines
import PrimitiveRootNumberNorm

/-!
# Primitive left boundary below Jutila's p. 48 hybrid convexity estimate

The p. 48 estimate is a convexity consequence of the primitive functional
equation and an archimedean Gamma-ratio estimate.  This file certifies the
functional-equation boundary reduction exactly and leaves the Gamma ratio in
the literal form in which a quantitative complex Stirling theorem must prove
it.  Thus the remaining analytic leaf is strictly smaller than an L-function
convexity theorem.
-/

namespace MAPJutilaHybridConvexityPrimitiveBoundary

open Complex DirichletCharacter

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The right functional-equation point corresponding to the left line
`Re z = -delta`. -/
def rightPoint (delta t : ℝ) : ℂ :=
  ((1 + delta : ℝ) : ℂ) - (t : ℂ) * I

/-- The reflected left point. -/
def leftPoint (delta t : ℝ) : ℂ :=
  ((-delta : ℝ) : ℂ) + (t : ℂ) * I

theorem one_sub_rightPoint (delta t : ℝ) :
    1 - rightPoint delta t = leftPoint delta t := by
  apply Complex.ext <;> simp [rightPoint, leftPoint] <;> ring

theorem rightPoint_re (delta t : ℝ) :
    (rightPoint delta t).re = 1 + delta := by
  simp [rightPoint]

/-- The precise archimedean input required on the shifted right point.  It is
kept as a predicate on the Gamma factors rather than as an L-function bound,
so a future quantitative Stirling module can inhabit it directly. -/
def GammaRatioBoundAtShift (delta CΓ : ℝ) : Prop :=
  0 ≤ CΓ ∧ ∀ (chi : DirichletCharacter ℂ q) (t : ℝ),
    ‖chi⁻¹.gammaFactor (rightPoint delta t) /
        chi.gammaFactor (1 - rightPoint delta t)‖ ≤
      CΓ * Real.rpow (1 + |t|) (1 / 2 + delta)

/-- Exact primitive left-boundary consequence of the ordinary functional
equation, absolute convergence on `Re s = 1+delta`, and the displayed Gamma
ratio estimate.  All conductor and height exponents remain symbolic. -/
theorem norm_LFunction_leftPoint_le_of_gammaRatio
    (chi : DirichletCharacter ℂ q) (hprim : chi.IsPrimitive)
    (hchi : chi ≠ 1) {delta CΓ : ℝ} (hdelta : 0 < delta)
    (hGamma : GammaRatioBoundAtShift (q := q) delta CΓ) (t : ℝ) :
    ‖DirichletCharacter.LFunction chi (leftPoint delta t)‖ ≤
      CΓ * MAPZeroFreeSiegelSpine.rightEdgePSeries delta *
        Real.rpow (q : ℝ) (1 / 2 + delta) *
          Real.rpow (1 + |t|) (1 / 2 + delta) := by
  have hspos : 0 < (rightPoint delta t).re := by
    rw [rightPoint_re]
    linarith
  have hfe :=
    MAPHuxleyPrimitiveFunctionalEquation.LFunction_one_sub_eq_huxleyFactor
      hprim hchi (s := rightPoint delta t) hspos
  have hright :
      ‖DirichletCharacter.LFunction chi⁻¹ (rightPoint delta t)‖ ≤
        MAPZeroFreeSiegelSpine.rightEdgePSeries delta := by
    apply MAPZeroFreeSiegelSpine.norm_LFunction_rightEdge_le_pSeries
      chi⁻¹ hdelta
    exact rightPoint_re delta t
  have hqnorm :
      ‖(q : ℂ) ^ (rightPoint delta t - 1 / 2)‖ =
        Real.rpow (q : ℝ) (1 / 2 + delta) := by
    rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos q)]
    congr 1
    simp [rightPoint]
    ring
  have hroot : ‖chi.rootNumber‖ = 1 :=
    FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one chi hprim
  have hgamma := hGamma.2 chi t
  rw [← one_sub_rightPoint delta t, hfe]
  rw [show (q : ℂ) ^ (rightPoint delta t - 1 / 2) * chi.rootNumber *
        DirichletCharacter.LFunction chi⁻¹ (rightPoint delta t) *
          chi⁻¹.gammaFactor (rightPoint delta t) /
            chi.gammaFactor (1 - rightPoint delta t) =
      (((q : ℂ) ^ (rightPoint delta t - 1 / 2) * chi.rootNumber) *
        DirichletCharacter.LFunction chi⁻¹ (rightPoint delta t)) *
          (chi⁻¹.gammaFactor (rightPoint delta t) /
            chi.gammaFactor (1 - rightPoint delta t)) by ring]
  rw [norm_mul, norm_mul, norm_mul, hqnorm, hroot, mul_one]
  have hqnonneg : 0 ≤ Real.rpow (q : ℝ) (1 / 2 + delta) :=
    Real.rpow_nonneg (Nat.cast_nonneg q) _
  have hLnonneg :
      0 ≤ ‖DirichletCharacter.LFunction chi⁻¹ (rightPoint delta t)‖ :=
    norm_nonneg _
  have hGnonneg :
      0 ≤ ‖chi⁻¹.gammaFactor (rightPoint delta t) /
        chi.gammaFactor (1 - rightPoint delta t)‖ := norm_nonneg _
  calc
    Real.rpow (q : ℝ) (1 / 2 + delta) *
          ‖DirichletCharacter.LFunction chi⁻¹ (rightPoint delta t)‖ *
        ‖chi⁻¹.gammaFactor (rightPoint delta t) /
          chi.gammaFactor (1 - rightPoint delta t)‖ ≤
      Real.rpow (q : ℝ) (1 / 2 + delta) *
          MAPZeroFreeSiegelSpine.rightEdgePSeries delta *
        (CΓ * Real.rpow (1 + |t|) (1 / 2 + delta)) := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hright hqnonneg) hgamma hGnonneg
        (mul_nonneg hqnonneg
          (le_trans (norm_nonneg _)
            (MAPZeroFreeSiegelSpine.norm_LFunction_rightEdge_le_pSeries
              chi⁻¹ hdelta (rightPoint_re delta t))))
    _ = CΓ * MAPZeroFreeSiegelSpine.rightEdgePSeries delta *
        Real.rpow (q : ℝ) (1 / 2 + delta) *
          Real.rpow (1 + |t|) (1 / 2 + delta) := by ring

end

end MAPJutilaHybridConvexityPrimitiveBoundary

#print axioms MAPJutilaHybridConvexityPrimitiveBoundary.one_sub_rightPoint
#print axioms MAPJutilaHybridConvexityPrimitiveBoundary.norm_LFunction_leftPoint_le_of_gammaRatio
