import Mathlib
import Mathlib.Analysis.Complex.LocallyUniformLimit
import FordEulerCellBound

open Set
noncomputable section

namespace FordEulerCellAnalytic

/-- The first Euler correction cell, written with explicit complex powers. -/
def cell (a : ℝ) (s : ℂ) : ℂ :=
  (a : ℂ) ^ (-s) -
    (((a + 1 : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s)

/-- The explicit Euler cell series beginning at `M + u`. -/
def cellSeries (M : ℕ) (u : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, cell (M + u + n) s

theorem differentiableAt_cell {M : ℕ} {u : ℝ} {n : ℕ} {s : ℂ}
    (hM : 1 ≤ M) (hu : 0 ≤ u) (hs : s ≠ 1) :
    DifferentiableAt ℂ (fun z => cell (M + u + n) z) s := by
  have ha : 0 < M + u + n := by positivity
  have ha0 : (M + u + n : ℝ) ≠ 0 := ne_of_gt ha
  have hap0 : (M + u + n + 1 : ℝ) ≠ 0 := by positivity
  have hac0 : ((M + u + n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha0
  have hapc0 : ((M + u + n + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hap0
  have hneg : DifferentiableAt ℂ (fun z : ℂ => -z) s := differentiableAt_id.neg
  have hone_sub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
    (differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id
  have hleft : DifferentiableAt ℂ (fun z : ℂ =>
      ((M + u + n : ℝ) : ℂ) ^ (-z)) s :=
    hneg.const_cpow (Or.inl hac0)
  have hright : DifferentiableAt ℂ (fun z : ℂ =>
      ((M + u + n + 1 : ℝ) : ℂ) ^ (1 - z)) s :=
    hone_sub.const_cpow (Or.inl hapc0)
  have hmid : DifferentiableAt ℂ (fun z : ℂ =>
      ((M + u + n : ℝ) : ℂ) ^ (1 - z)) s :=
    hone_sub.const_cpow (Or.inl hac0)
  have hden0 : (1 - s) ≠ 0 := sub_ne_zero.mpr hs.symm
  have hquot : DifferentiableAt ℂ (fun z : ℂ =>
      ((((M + u + n + 1 : ℝ) : ℂ) ^ (1 - z) -
        ((M + u + n : ℝ) : ℂ) ^ (1 - z)) / (1 - z))) s :=
    (hright.sub hmid).div hone_sub hden0
  exact hleft.sub hquot

/-- A locally uniform summable majorant promotes the explicit cell series to a
differentiable function.  The Euler cell bound supplies this hypothesis on
any right half-plane neighbourhood where the real part and `‖s‖` are bounded. -/
theorem differentiableOn_cellSeries_of_summable
    {M : ℕ} {u : ℝ} {U : Set ℂ} {b : ℕ → ℝ}
    (hM : 1 ≤ M) (hu : 0 ≤ u) (hU : IsOpen U)
    (hb : Summable b)
    (hbound : ∀ n : ℕ, ∀ z : ℂ, z ∈ U → ‖cell (M + u + n) z‖ ≤ b n)
    (hne : ∀ z : ℂ, z ∈ U → z ≠ 1) :
    DifferentiableOn ℂ (cellSeries M u) U := by
  apply Complex.differentiableOn_tsum_of_summable_norm hb
  · intro n z hz
    exact differentiableAt_cell hM hu (hne z hz) |>.differentiableWithinAt
  · exact hU
  · exact hbound

theorem differentiableAt_cellSeries {M : ℕ} {u : ℝ} {s : ℂ}
    (hM : 1 ≤ M) (hu : 0 ≤ u) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ (cellSeries M u) s := by
  let d : ℝ := s.re / 2
  let δ : ℝ := min d (‖s - 1‖ / 2)
  let K : ℝ := ‖s‖ + δ
  have hd : 0 < d := by dsimp [d]; linarith
  have hsneq : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hd (half_pos (norm_pos_iff.mpr hsneq))
  let U : Set ℂ := Metric.ball s δ
  have hU : IsOpen U := Metric.isOpen_ball
  have hne : ∀ z : ℂ, z ∈ U → z ≠ 1 := by
    intro z hz hz1
    have hzdist : ‖z - s‖ < δ := by
      simpa [U, dist_eq_norm, norm_sub_rev] using hz
    have hδ' : δ ≤ ‖s - 1‖ / 2 := min_le_right _ _
    subst z
    rw [norm_sub_rev] at hzdist
    linarith [norm_nonneg (s - 1)]
  have hzre : ∀ z : ℂ, z ∈ U → d < z.re := by
    intro z hz
    have hzdist : ‖z - s‖ < δ := by
      simpa [U, dist_eq_norm, norm_sub_rev] using hz
    have hδ' : δ ≤ d := min_le_left _ _
    have hre : |(z - s).re| ≤ ‖z - s‖ := Complex.abs_re_le_norm _
    dsimp [d] at *
    change |z.re - s.re| ≤ ‖z - s‖ at hre
    have hlow := (abs_le.mp hre).1
    linarith
  have hznorm : ∀ z : ℂ, z ∈ U → ‖z‖ ≤ K := by
    intro z hz
    have hzdist : ‖z - s‖ < δ := by
      simpa [U, dist_eq_norm, norm_sub_rev] using hz
    dsimp [K]
    have htri := norm_add_le (z - s) s
    have heq : (z - s) + s = z := by abel
    rw [heq] at htri
    linarith
  have hbase : Summable (fun n : ℕ => ((n : ℝ) ^ (-(d + 1)))) := by
    apply (Real.summable_nat_rpow).2
    linarith
  have hshift : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(d + 1))) := by
    simpa [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).2 hbase
  have hsum : Summable (fun n : ℕ => K * (((n + 1 : ℕ) : ℝ) ^ (-(d + 1)))) :=
    hshift.mul_left K
  have hbound : ∀ n : ℕ, ∀ z : ℂ, z ∈ U →
      ‖cell (M + u + n) z‖ ≤ K * (((n + 1 : ℕ) : ℝ) ^ (-(d + 1))) := by
    intro n z hz
    have hzpos : 0 < z.re := lt_trans hd (hzre z hz)
    have ha : 0 < (M + u + n : ℝ) := by positivity
    have ha1 : (1 : ℝ) ≤ M + u + n := by
      have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      linarith
    have hc := FordEulerCellBound.norm_cell_le ha hzpos (hne z hz)
    have hc' : ‖cell (M + u + n) z‖ ≤ ‖z‖ *
        (M + u + n : ℝ) ^ (-z.re - 1) := by
      simpa [cell] using hc
    have hexp : -z.re - 1 ≤ -(d + 1) := by linarith [hzre z hz]
    have hpow1 : (M + u + n : ℝ) ^ (-z.re - 1) ≤
        (M + u + n : ℝ) ^ (-(d + 1)) :=
      Real.rpow_le_rpow_of_exponent_le ha1 hexp
    have hshiftbase : ((n + 1 : ℕ) : ℝ) ≤ M + u + n := by
      have hMn : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith
    have hpow2 : (M + u + n : ℝ) ^ (-(d + 1)) ≤
        ((n + 1 : ℕ) : ℝ) ^ (-(d + 1)) := by
      apply Real.rpow_le_rpow_of_nonpos (by positivity) hshiftbase
      linarith
    calc
      ‖cell (M + u + n) z‖ ≤ ‖z‖ *
          (M + u + n : ℝ) ^ (-z.re - 1) := hc'
      _ ≤ K * (M + u + n : ℝ) ^ (-z.re - 1) :=
        mul_le_mul_of_nonneg_right (hznorm z hz) (Real.rpow_nonneg (le_of_lt ha) _)
      _ ≤ K * (M + u + n : ℝ) ^ (-(d + 1)) := by
        gcongr
      _ ≤ K * (((n + 1 : ℕ) : ℝ) ^ (-(d + 1))) := by
        gcongr
  have hdo := differentiableOn_cellSeries_of_summable hM hu hU hsum hbound hne
  exact hdo.differentiableAt (hU.mem_nhds (Metric.mem_ball_self hδ))

end FordEulerCellAnalytic

#print axioms FordEulerCellAnalytic.differentiableOn_cellSeries_of_summable
#print axioms FordEulerCellAnalytic.differentiableAt_cell
#print axioms FordEulerCellAnalytic.differentiableAt_cellSeries
