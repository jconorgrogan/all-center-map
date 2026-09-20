import FordEulerCellSeriesBound
import FordEulerCellFinite
import FordEulerBoundaryDecay
import Mathlib.NumberTheory.LSeries.HurwitzZeta

open Filter Set
open scoped BigOperators Topology
noncomputable section
namespace FordEulerHurwitzAboveOne
open FordEulerCellAnalytic

theorem hurwitz_eq_finite_add_cellSeries
    {u : ℝ} (hu : u ∈ Icc 0 1) {M : ℕ} (hM : 1 ≤ M)
    {s : ℂ} (hs : 1 < s.re) :
    HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s =
      (∑ n ∈ Finset.range M, (((n : ℝ) + u : ℝ) : ℂ) ^ (-s)) +
        ((((M : ℝ) + u : ℝ) : ℂ) ^ (1 - s)) / (s - 1) + cellSeries M u s := by
  let f : ℕ → ℂ := fun n => (((n : ℝ) + u : ℝ) : ℂ) ^ (-s)
  let a : ℝ := (M : ℝ) + u
  have hu0 : 0 ≤ u := hu.1
  have ha : 0 < a := by dsimp [a]; positivity
  have hs0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have hfull : HasSum f (HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s) := by
    simpa [f, Complex.cpow_neg, one_div] using
      HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re hu hs
  have htail := (hasSum_nat_add_iff' (f := f) M).mpr hfull
  have htail' : HasSum (fun n : ℕ => ((a + n : ℝ) : ℂ) ^ (-s))
      (HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s - ∑ n ∈ Finset.range M, f n) := by
    simpa [f, a, Nat.cast_add, add_comm, add_left_comm, add_assoc] using htail
  have hcell := FordEulerCellSeriesBound.summable_cell ha hs0 hs1
  have hdec := FordEulerBoundaryDecay.tendsto_cpow_one_sub_atTop_zero ha hs
  have hlim := htail'.tendsto_sum_nat.sub
    ((hdec.sub (tendsto_const_nhds (x := (a : ℂ) ^ (1 - s)))).div_const (1 - s))
  have hlim' : Tendsto (fun K : ℕ => ∑ n ∈ Finset.range K, cell (a + n) s) atTop
      (𝓝 ((HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s - ∑ n ∈ Finset.range M, f n) -
        (0 - (a : ℂ) ^ (1 - s)) / (1 - s))) := by
    convert hlim using 1
    funext K
    exact FordEulerCellFinite.sum_cells a s K
  have hid := tendsto_nhds_unique hcell.hasSum.tendsto_sum_nat hlim'
  change cellSeries M u s = _ at hid
  change HurwitzZeta.hurwitzZeta (u : UnitAddCircle) s =
    (∑ n ∈ Finset.range M, f n) + (a : ℂ) ^ (1 - s) / (s - 1) + cellSeries M u s
  have hquot : (0 - (a : ℂ) ^ (1 - s)) / (1 - s) =
      (a : ℂ) ^ (1 - s) / (s - 1) := by
    rw [zero_sub, show (1 : ℂ) - s = -(s - 1) by ring]
    exact neg_div_neg_eq _ _
  rw [hid]
  rw [hquot]
  ring

end FordEulerHurwitzAboveOne
#print axioms FordEulerHurwitzAboveOne.hurwitz_eq_finite_add_cellSeries
