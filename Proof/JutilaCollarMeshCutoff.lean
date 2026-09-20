import RelativeNearOneMesh27

/-!
# Exact relative-mesh cutoff for Jutila's in-paper collar argument

Jutila's proof of Theorem 1 reduces to `alpha >= 1 - delta` before its
in-paper argument.  Page 52 chooses `X = D^(1+12*delta)`, so the page-53
quadratic conclusion contributes density coefficient `2*(1+12*delta)`.
Reserving `4*kappa` for the remaining logarithms, the source-faithful choices
`delta = kappa = 1/280` give the exact target coefficient `21/10`.

This module verifies that the fixed relative mesh first enters the resulting
closed collar at index `95`, and supplies the exact finite-index split used to
route earlier cells to the existing CGL branch.
-/

namespace MAPJutilaCollarMeshCutoff

open scoped BigOperators
open MAPRelativeNearOneMesh27

noncomputable section

/-- Working collar width in Jutila's page-52 parameter selection. -/
def collarDelta : ℝ := 1 / 280

/-- Power budget which absorbs the two logarithmic factors after squaring. -/
def logarithmicBudget : ℝ := 1 / 280

/-- The page-52 power and logarithmic overhead sum to the exact `21/10`
coefficient consumed by the MAP relative mesh. -/
theorem collar_density_coefficient :
    2 * (1 + 12 * collarDelta) + 4 * logarithmicBudget = 21 / 10 := by
  norm_num [collarDelta, logarithmicBudget]

/-- The first fixed index used by the source-faithful MAP splice. -/
def collarIndex : ℕ := 95

/-- At index 95 the relative mesh is already in the closed Jutila collar
`sigma >= 1 - 1/280 = 279/280`. -/
theorem relativePoint_collarIndex :
    (279 / 280 : ℝ) ≤ relativePoint collarIndex := by
  norm_num [collarIndex, relativePoint, relativeDistance]

/-- Index 94 is still outside the collar, so index 95 is not a rounded-up
convenience: it is the first legal source index. -/
theorem relativePoint_before_collarIndex :
    relativePoint (collarIndex - 1) < (279 / 280 : ℝ) := by
  norm_num [collarIndex, relativePoint, relativeDistance]

/-- Every later mesh point remains in the same closed collar. -/
theorem relativePoint_mem_collar {j : ℕ} (hj : collarIndex ≤ j) :
    (279 / 280 : ℝ) ≤ relativePoint j := by
  exact relativePoint_collarIndex.trans (relativePoint_mono hj)

/-- Exact case split for welding the fixed compact branch to the in-paper
Jutila collar branch. -/
theorem mesh_density_of_compact_or_collar
    {P : ℕ → Prop} {L : ℕ}
    (hcompact : ∀ j < L, j < collarIndex → P j)
    (hcollar : ∀ j < L, collarIndex ≤ j → P j) :
    ∀ j < L, P j := by
  intro j hj
  rcases lt_or_ge j collarIndex with hlt | hge
  · exact hcompact j hj hlt
  · exact hcollar j hj hge

/-- Exact mass-level splice.  Cells with `j < 95` are supplied by the fixed
compact/CGL route, including the cell whose closed right endpoint is
`relativePoint 95`.  Cells with `95 <= j` are supplied by Jutila's closed
density collar at their left endpoint.  The existing half-open cell partition
then proves that there is neither an omitted atom nor a duplicated mass term.

The two analytic branches may be proved by unrelated estimates: this theorem
only asks each branch for the same final per-cell majorant `B`. -/
theorem relativeNearMass_le_log_mul_of_compact_collar_cell_bounds
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {omega X B : ℝ} {L : ℕ}
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaGap : ∀ z ∈ S, beta z ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hB : 0 ≤ B)
    (hcompact : ∀ j < L, j < collarIndex →
      (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤ B)
    (hcollar : ∀ j < L, collarIndex ≤ j →
      (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤ B) :
    (∑ z ∈ S,
      (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      Real.log X * B := by
  have hendpoint : ∀ z ∈ S, beta z ≤ relativePoint L := by
    intro z hz
    have hgap := hbetaGap z hz
    unfold relativePoint
    linarith
  rw [← sum_relativeCells_eq S beta
    (fun z => (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1)))
    hbetaLow hendpoint]
  calc
    (∑ j ∈ Finset.range L, ∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
        ∑ _j ∈ Finset.range L, B := by
      apply Finset.sum_le_sum
      intro j hj
      have hjL := Finset.mem_range.mp hj
      rcases lt_or_ge j collarIndex with hjcompact | hjcollar
      · exact hcompact j hjL hjcompact
      · exact hcollar j hjL hjcollar
    _ = (L : ℝ) * B := by simp
    _ ≤ Real.log X * B := mul_le_mul_of_nonneg_right hLlog hB

end

end MAPJutilaCollarMeshCutoff

#print axioms MAPJutilaCollarMeshCutoff.relativePoint_collarIndex
#print axioms MAPJutilaCollarMeshCutoff.relativePoint_before_collarIndex
#print axioms MAPJutilaCollarMeshCutoff.collar_density_coefficient
#print axioms MAPJutilaCollarMeshCutoff.relativePoint_mem_collar
#print axioms MAPJutilaCollarMeshCutoff.mesh_density_of_compact_or_collar
#print axioms MAPJutilaCollarMeshCutoff.relativeNearMass_le_log_mul_of_compact_collar_cell_bounds
