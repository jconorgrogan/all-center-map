import GoldfeldContourBounds

/-!
# Unconditional full Goldfeld contour identity

The quantitative boundary hypotheses are discharged at Riesz order `14`.
-/

namespace MAPGoldfeldSiegel

open Set MeasureTheory Complex Filter
open scoped Topology Interval Real

noncomputable section

set_option maxHeartbeats 800000

/-- The full smoothed Goldfeld contour identity, with no boundary hypotheses
left in its interface. -/
theorem normalized_full_goldfeld_contour
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
        ((1 / 2 : ℝ) + t * I)) =
      goldfeldPoleResidue chi psi beta 14 X +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
            ((-1 / 2 : ℝ) + t * I)) := by
  let r : ℝ := min ((1 - beta) / 2) ((beta - 1 / 2) / 2)
  have hleftPos : 0 < (1 - beta) / 2 := by linarith
  have hrightPos : 0 < (beta - 1 / 2) / 2 := by linarith
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hleftPos hrightPos
  have hrleLeft : r ≤ (1 - beta) / 2 := min_le_left _ _
  have hrleRight : r ≤ (beta - 1 / 2) / 2 := min_le_right _ _
  apply normalized_full_goldfeld_contour_of_left_integrable_horizontal_decay
    chi psi hchi hpsi hmul hzero hbetaLow hbetaHigh
      (k := 14) (X := X) (r := r) (by norm_num) hX hr
  · linarith
  · linarith
  · exact integrable_goldfeldRaw_left chi psi hchi hpsi hmul hzero
      hbetaLow hbetaHigh hX
  · exact tendsto_goldfeld_horizontal_minus chi psi hchi hpsi hmul
      hbetaLow hbetaHigh hX
  · exact tendsto_goldfeld_horizontal_plus chi psi hchi hpsi hmul
      hbetaLow hbetaHigh hX

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.normalized_full_goldfeld_contour
