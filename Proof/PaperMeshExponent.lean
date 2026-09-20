import Mathlib

/-!
# The literal mesh and exponent conversion in the MAP zero-density splice

This file formalizes the two-parameter mesh used in Proposition 2.2 of the
all-center MAP package.  The lower cutoff `delta0` and cell width `Delta` are
kept distinct.  It also converts a density bound stated at height
`T = X ^ tau` into the exact `X ^ (-3 * epsilon / 52)` cell saving.

No zero-density estimate is assumed globally or declared as an axiom.  The
analytic estimate is a local premise of `densityAtHeight_mul_weight_le`.
-/

namespace MAPGuthMaynard

open scoped BigOperators

noncomputable section

/-- Height exponent at the `2/15 + epsilon` threshold. -/
def tau (epsilon : ℝ) : ℝ := 13 / 15 - epsilon / 2

/-- The `30/13` uniform density coefficient. -/
def densityCoeff : ℝ := 30 / 13

/-- The density loss allocated in the paper. -/
def etaZD (epsilon : ℝ) : ℝ := 3 * epsilon / (52 * tau epsilon)

/-- Left endpoint of cell `j`, with lower cutoff and width kept distinct. -/
def meshPoint (delta0 Delta : ℝ) (j : ℕ) : ℝ :=
  1 / 2 + delta0 + j * Delta

/-- Enough cells of width `Delta` to cover `[1/2 + delta0, 4/5]`. -/
def meshCellCount (delta0 Delta : ℝ) : ℕ :=
  ⌊((3 / 10 : ℝ) - delta0) / Delta⌋₊ + 1

theorem tau_pos {epsilon : ℝ} (hepsilon_le : epsilon ≤ 1 / 10) :
    0 < tau epsilon := by
  unfold tau
  linarith

theorem tau_ne_zero {epsilon : ℝ} (hepsilon_le : epsilon ≤ 1 / 10) :
    tau epsilon ≠ 0 := (tau_pos hepsilon_le).ne'

/-- The paper's choice makes `tau * etaZD` exactly `3 epsilon / 52`. -/
theorem tau_mul_etaZD {epsilon : ℝ} (hepsilon_le : epsilon ≤ 1 / 10) :
    tau epsilon * etaZD epsilon = 3 * epsilon / 52 := by
  rw [etaZD]
  field_simp [tau_ne_zero hepsilon_le]

/-- Every point of the compact strip lies in the literal two-parameter mesh. -/
theorem exists_mesh_cell {delta0 Delta sigma : ℝ} (hDelta : 0 < Delta)
    (hsigma_low : 1 / 2 + delta0 ≤ sigma) (hsigma_high : sigma ≤ 4 / 5) :
    ∃ j ∈ Finset.range (meshCellCount delta0 Delta),
      meshPoint delta0 Delta j ≤ sigma ∧
        sigma < meshPoint delta0 Delta j + Delta := by
  let y : ℝ := (sigma - (1 / 2 + delta0)) / Delta
  let R : ℝ := ((3 / 10 : ℝ) - delta0) / Delta
  have hy0 : 0 ≤ y := div_nonneg (sub_nonneg.mpr hsigma_low) hDelta.le
  have hyR : y ≤ R := by
    dsimp [y, R]
    apply (div_le_div_iff_of_pos_right hDelta).2
    linarith
  let j : ℕ := ⌊y⌋₊
  have hjR : j ≤ ⌊R⌋₊ := Nat.floor_mono hyR
  have hjmem : j ∈ Finset.range (meshCellCount delta0 Delta) := by
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le hjR
  refine ⟨j, hjmem, ?_, ?_⟩
  · have hjy : (j : ℝ) ≤ y := Nat.floor_le hy0
    have hmul : (j : ℝ) * Delta ≤ sigma - (1 / 2 + delta0) := by
      exact (le_div_iff₀ hDelta).mp hjy
    dsimp [meshPoint]
    linarith
  · have hyj : y < (j : ℝ) + 1 := by
      simpa [j] using (Nat.lt_floor_add_one y)
    have hmul : sigma - (1 / 2 + delta0) < ((j : ℝ) + 1) * Delta := by
      exact (div_lt_iff₀ hDelta).mp hyj
    dsimp [meshPoint]
    linarith

/-- Every mesh left endpoint stays at or below `4/5`. -/
theorem meshPoint_le_four_fifths {delta0 Delta : ℝ}
    (hDelta : 0 < Delta) (hdelta0_cap : delta0 ≤ 3 / 10)
    {j : ℕ} (hj : j < meshCellCount delta0 Delta) :
    meshPoint delta0 Delta j ≤ 4 / 5 := by
  have hR0 : 0 ≤ ((3 / 10 : ℝ) - delta0) / Delta :=
    div_nonneg (sub_nonneg.mpr hdelta0_cap) hDelta.le
  have hjfloor : j ≤ ⌊((3 / 10 : ℝ) - delta0) / Delta⌋₊ := by
    simpa [meshCellCount] using Nat.le_of_lt_succ hj
  have hfloor :
      (⌊((3 / 10 : ℝ) - delta0) / Delta⌋₊ : ℝ) ≤
        ((3 / 10 : ℝ) - delta0) / Delta := Nat.floor_le hR0
  have hjdiv : (j : ℝ) ≤ ((3 / 10 : ℝ) - delta0) / Delta := by
    exact (Nat.cast_le.mpr hjfloor).trans hfloor
  have hjmul : (j : ℝ) * Delta ≤ (3 / 10 : ℝ) - delta0 :=
    (le_div_iff₀ hDelta).mp hjdiv
  dsimp [meshPoint]
  linarith

/-- Exact algebra behind the exponent ledger before inequalities are applied. -/
theorem paper_cell_exponent_identity {epsilon sigma Delta : ℝ}
    (hepsilon_le : epsilon ≤ 1 / 10) :
    tau epsilon *
          (densityCoeff * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) =
      -((15 / 13) * epsilon) * (1 - sigma) +
        2 * Delta + 3 * epsilon / 52 := by
  rw [mul_add, tau_mul_etaZD hepsilon_le]
  unfold tau densityCoeff
  ring

/-- The exact paper mesh retains the advertised `3 epsilon / 52` saving. -/
theorem paper_cell_exponent_bound {epsilon sigma Delta : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52) :
    tau epsilon *
          (densityCoeff * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + Delta - 1) ≤
      -(3 * epsilon / 52) := by
  rw [paper_cell_exponent_identity hepsilon_le]
  nlinarith

/-- A density estimate at `T = X ^ tau`, multiplied by the largest zero
weight in one mesh cell, gives the exact paper saving.

`zeroCount` is deliberately abstract: the theorem is the analytic-to-arithmetic
exponent conversion, while an eventual formalization of Guth--Maynard and the
Montgomery detector supplies `hdensity` for the divisor-backed count.
-/
theorem densityAtHeight_mul_weight_le
    {epsilon sigma Delta X C zeroCount : ℝ}
    (hepsilon_pos : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hDelta : Delta ≤ 3 * epsilon / 52)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : zeroCount ≤
      C * Real.rpow (Real.rpow X (tau epsilon))
        (densityCoeff * (1 - sigma) + etaZD epsilon)) :
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
      C * Real.rpow X (-(3 * epsilon / 52)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hweight_nonneg :
      0 ≤ Real.rpow X (2 * (sigma + Delta - 1)) :=
    Real.rpow_nonneg hXpos.le _
  have hcollapse :
      Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - sigma) + etaZD epsilon) =
        Real.rpow X
          (tau epsilon * (densityCoeff * (1 - sigma) + etaZD epsilon)) :=
    (Real.rpow_mul hXpos.le _ _).symm
  calc
    zeroCount * Real.rpow X (2 * (sigma + Delta - 1)) ≤
        (C * Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - sigma) + etaZD epsilon)) *
            Real.rpow X (2 * (sigma + Delta - 1)) :=
      mul_le_mul_of_nonneg_right hdensity hweight_nonneg
    _ = C * Real.rpow X
          (tau epsilon *
              (densityCoeff * (1 - sigma) + etaZD epsilon) +
            2 * (sigma + Delta - 1)) := by
      rw [hcollapse, mul_assoc]
      congr 1
      exact (Real.rpow_add hXpos _ _).symm
    _ ≤ C * Real.rpow X (-(3 * epsilon / 52)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      exact paper_cell_exponent_bound hepsilon_pos hepsilon_le
        hsigma_high hDelta

/-- Finite aggregation of uniform cell bounds.  This is the exact place where
the finite mesh cardinality is paid; no power of `X` is lost. -/
theorem sum_mesh_cells_le
    {delta0 Delta M : ℝ}
    (cellMass : ℕ → ℝ)
    (hcell : ∀ j, j < meshCellCount delta0 Delta →
      0 ≤ cellMass j ∧ cellMass j ≤ M) :
    (∑ j ∈ Finset.range (meshCellCount delta0 Delta), cellMass j) ≤
      meshCellCount delta0 Delta * M := by
  calc
    (∑ j ∈ Finset.range (meshCellCount delta0 Delta), cellMass j) ≤
        ∑ _j ∈ Finset.range (meshCellCount delta0 Delta), M := by
      apply Finset.sum_le_sum
      intro j hj
      exact (hcell j (Finset.mem_range.mp hj)).2
    _ = meshCellCount delta0 Delta * M := by simp

end

end MAPGuthMaynard
