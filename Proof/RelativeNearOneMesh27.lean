import CGLMeshFormalization

/-!
# Relative near-one beta mesh for equation (2.7)

This staging file supplies the finite geometric summation omitted after the
one-cell estimate in `CGLMeshFormalization`.  The mesh is source-neutral: the
only analytic hypothesis of the final theorem is the pointwise cumulative
zero-density inequality at its left endpoints.

The cells are `(sigma_j, sigma_{j+1}]`, where

`1 - sigma_j = (1/5) * (23/24)^j`.

Thus `sigma_0 = 4/5` belongs to the compact branch, not the near-one branch,
and the relative width is exactly `(1 - sigma_j)/24`.  Analytic
multiplicities are represented by an arbitrary `Nat`-valued function, so all
finite-sum deductions below are literal and multiplicity-aware.
-/

namespace MAPRelativeNearOneMesh27

open scoped BigOperators
open CGLMeshFormalization ZeroDensityArithmetic MAPAPZeroDensityCert
open MAPGuthMaynard

noncomputable section

/-- Distance of the `j`th near-one mesh point from one. -/
def relativeDistance (j : ℕ) : ℝ :=
  (1 / 5 : ℝ) * (23 / 24 : ℝ) ^ j

/-- Left endpoint of the `j`th relative near-one cell. -/
def relativePoint (j : ℕ) : ℝ :=
  1 - relativeDistance j

/-- Width of the `j`th relative near-one cell. -/
def relativeWidth (j : ℕ) : ℝ :=
  relativeDistance j / 24

@[simp] theorem relativeDistance_zero : relativeDistance 0 = 1 / 5 := by
  simp [relativeDistance]

@[simp] theorem relativePoint_zero : relativePoint 0 = 4 / 5 := by
  norm_num [relativePoint, relativeDistance]

theorem relativeDistance_pos (j : ℕ) : 0 < relativeDistance j := by
  unfold relativeDistance
  positivity

theorem relativeWidth_pos (j : ℕ) : 0 < relativeWidth j := by
  unfold relativeWidth
  exact div_pos (relativeDistance_pos j) (by norm_num)

theorem relativeDistance_succ (j : ℕ) :
    relativeDistance (j + 1) = (23 / 24 : ℝ) * relativeDistance j := by
  unfold relativeDistance
  rw [pow_succ]
  ring

theorem relativePoint_succ (j : ℕ) :
    relativePoint (j + 1) = relativePoint j + relativeWidth j := by
  rw [relativePoint, relativePoint, relativeWidth,
    relativeDistance_succ]
  ring

theorem one_sub_relativePoint (j : ℕ) :
    1 - relativePoint j = relativeDistance j := by
  simp [relativePoint]

theorem relativeWidth_eq_one_sub_point_div (j : ℕ) :
    relativeWidth j = (1 - relativePoint j) / 24 := by
  rw [relativeWidth, one_sub_relativePoint]

theorem relativePoint_lt_succ (j : ℕ) :
    relativePoint j < relativePoint (j + 1) := by
  rw [relativePoint_succ]
  linarith [relativeWidth_pos j]

theorem relativePoint_mono : Monotone relativePoint := by
  exact monotone_nat_of_le_succ fun j => (relativePoint_lt_succ j).le

theorem relativePoint_le_one (j : ℕ) : relativePoint j ≤ 1 := by
  unfold relativePoint
  linarith [relativeDistance_pos j]

/-- Every positive zero-free gap is reached by the geometric mesh. -/
theorem exists_relativeDistance_le {omega : ℝ} (homega : 0 < omega) :
    ∃ J : ℕ, relativeDistance J ≤ omega := by
  obtain ⟨J, hJ⟩ := exists_pow_lt_of_lt_one
    (show 0 < (5 : ℝ) * omega by positivity)
    (show (23 / 24 : ℝ) < 1 by norm_num)
  refine ⟨J, ?_⟩
  unfold relativeDistance
  nlinarith

/-- The first mesh point entering the gap has both endpoint properties needed
for the cell argument: it reaches `omega`, while every earlier cell begins at
distance at least `omega` from one. -/
theorem exists_minimal_relative_cutoff {omega : ℝ} (homega : 0 < omega) :
    ∃ J : ℕ, relativeDistance J ≤ omega ∧
      ∀ j < J, omega < relativeDistance j := by
  let P : ℕ → Prop := fun n => relativeDistance n ≤ omega
  have hP : ∃ n, P n := exists_relativeDistance_le homega
  let J := Nat.find hP
  refine ⟨J, Nat.find_spec hP, ?_⟩
  intro j hj
  have hnot : ¬ P j := Nat.find_min hP hj
  dsimp [P] at hnot
  exact lt_of_not_ge hnot

/-- Half-open-on-the-left, closed-on-the-right relative cell.  This convention
keeps the shared endpoint `4/5` out of the near-one branch and assigns every
subsequent mesh endpoint to exactly one cell. -/
def relativeCell {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) (j : ℕ) : Finset ι :=
  S.filter fun z => relativePoint j < beta z ∧
    beta z ≤ relativePoint (j + 1)

/-- A near-one atom below the terminal mesh point lies in a relative cell.
The proof chooses the first mesh point lying to the right of the atom, so no
endpoint convention is hidden. -/
theorem exists_relative_cell {beta : ℝ} {J : ℕ}
    (hbetaLow : 4 / 5 < beta)
    (hbetaHigh : beta ≤ relativePoint J) :
    ∃ j < J, relativePoint j < beta ∧
      beta ≤ relativePoint (j + 1) := by
  let P : ℕ → Prop := fun n => beta ≤ relativePoint n
  have hP : ∃ n, P n := ⟨J, hbetaHigh⟩
  let n := Nat.find hP
  have hnP : beta ≤ relativePoint n := Nat.find_spec hP
  have hn0 : n ≠ 0 := by
    intro hn
    have hnP0 : beta ≤ relativePoint 0 := by simpa [hn] using hnP
    rw [relativePoint_zero] at hnP0
    linarith
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
  let j := n - 1
  have hjadd : j + 1 = n := by
    dsimp [j]
    omega
  have hnJ : n ≤ J := Nat.find_min' hP hbetaHigh
  have hjJ : j < J := by
    dsimp [j]
    omega
  have hnot : ¬ P j := Nat.find_min hP (by
    dsimp [j]
    omega)
  have hjLow : relativePoint j < beta := by
    dsimp [P] at hnot
    exact lt_of_not_ge hnot
  refine ⟨j, hjJ, hjLow, ?_⟩
  rw [hjadd]
  exact hnP

/-- Distinct relative cells are disjoint. -/
theorem relativeCell_pairwise_disjoint {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) (J : ℕ) :
    (Finset.range J : Set ℕ).PairwiseDisjoint (relativeCell S beta) := by
  intro j hj k hk hjk
  apply Finset.disjoint_left.2
  intro z hzj hzk
  have hjmem := (Finset.mem_filter.mp hzj).2
  have hkmem := (Finset.mem_filter.mp hzk).2
  rcases hjmem with ⟨hjlow, hjhigh⟩
  rcases hkmem with ⟨hklow, hkhigh⟩
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hsucc : j + 1 ≤ k := by omega
    have hpoints := relativePoint_mono hsucc
    linarith
  · have hsucc : k + 1 ≤ j := by omega
    have hpoints := relativePoint_mono hsucc
    linarith

/-- If every atom is strictly above `4/5` and no farther right than the
terminal endpoint, the relative cells form an exact finite partition. -/
theorem biUnion_relativeCell_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) {J : ℕ}
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaHigh : ∀ z ∈ S, beta z ≤ relativePoint J) :
    (Finset.range J).biUnion (relativeCell S beta) = S := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, hj, hzcell⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hzcell).1
  · intro hz
    obtain ⟨j, hjJ, hjlow, hjhigh⟩ :=
      exists_relative_cell (hbetaLow z hz) (hbetaHigh z hz)
    apply Finset.mem_biUnion.mpr
    exact ⟨j, Finset.mem_range.mpr hjJ,
      Finset.mem_filter.mpr ⟨hz, hjlow, hjhigh⟩⟩

/-- Exact multiplicity-weighted mass decomposition over the relative cells. -/
theorem sum_relativeCells_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) (weight : ι → ℝ) {J : ℕ}
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaHigh : ∀ z ∈ S, beta z ≤ relativePoint J) :
    (∑ j ∈ Finset.range J, ∑ z ∈ relativeCell S beta j, weight z) =
      ∑ z ∈ S, weight z := by
  rw [← Finset.sum_biUnion (relativeCell_pairwise_disjoint S beta J)]
  rw [biUnion_relativeCell_eq S beta hbetaLow hbetaHigh]

/-- A cell's multiplicity is bounded by the cumulative count at its closed
left density endpoint. -/
theorem cellMultiplicity_le_cumulative {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ) (j : ℕ) :
    (∑ z ∈ relativeCell S beta j, multiplicity z : ℕ) ≤
      ∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z), multiplicity z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro z hz
    have hz' := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.1.le⟩
  · intro z _ _
    exact Nat.zero_le _

/-- The largest weight in `(sigma_j,sigma_{j+1}]` occurs at its closed right
endpoint. -/
theorem relativeCellMass_le_count_mul_upperWeight
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {X : ℝ} (j : ℕ) (hX : 1 ≤ X) :
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) *
        Real.rpow X (2 * (relativePoint (j + 1) - 1)) := by
  let W := Real.rpow X (2 * (relativePoint (j + 1) - 1))
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  calc
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ∑ z ∈ relativeCell S beta j, (multiplicity z : ℝ) * W := by
        apply Finset.sum_le_sum
        intro z hz
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply Real.rpow_le_rpow_of_exponent_le hX
        have hzupper := (Finset.mem_filter.mp hz).2.2
        linarith
    _ = ((∑ z ∈ relativeCell S beta j, multiplicity z : ℕ) : ℝ) * W := by
      push_cast
      rw [Finset.sum_mul]
    _ ≤ ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
        multiplicity z : ℕ) : ℝ) * W := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast cellMultiplicity_le_cumulative S multiplicity beta j
      · exact Real.rpow_nonneg hXpos.le _

/-- One relative cell follows from the exact pointwise `21/10` density
inequality.  The only non-arithmetic premise is `hdensity`. -/
theorem relativeCellMass_le_of_density
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u omega X C : ℝ} {j : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (homega : omega ≤ relativeDistance j)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity :
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow X
          ((21 / 10) * (tau epsilon + u) *
            (1 - relativePoint j))) :
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      C * Real.rpow X (-(omega / 12)) := by
  have hmass := relativeCellMass_le_count_mul_upperWeight
    S multiplicity beta j hX
  have hlocal := near_one_density_mul_weight_le_of_gap
    (sigma := relativePoint j) (Delta := relativeWidth j)
    hepsilon hu0 hu (relativePoint_le_one j)
    (by simpa [one_sub_relativePoint] using homega)
    (by rw [relativeWidth_eq_one_sub_point_div])
    hX hC hdensity
  calc
    (∑ z ∈ relativeCell S beta j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) *
        Real.rpow X (2 * (relativePoint (j + 1) - 1)) := hmass
    _ = ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) *
        Real.rpow X
          (2 * (relativePoint j + relativeWidth j - 1)) := by
      rw [relativePoint_succ]
    _ ≤ C * Real.rpow X (-(omega / 12)) := hlocal

/-- Finite geometric-mesh integration of the pointwise density bound into
the literal multiplicity-weighted near-one mass.  The factor `J` is the exact
mesh-cardinality loss. -/
theorem relativeNearMass_le_card_mul
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u omega X C : ℝ} {J : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaGap : ∀ z ∈ S, beta z ≤ 1 - omega)
    (hterminal : relativeDistance J ≤ omega)
    (hmeshGap : ∀ j < J, omega ≤ relativeDistance j)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ j < J,
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow X
          ((21 / 10) * (tau epsilon + u) *
            (1 - relativePoint j))) :
    (∑ z ∈ S,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      (J : ℝ) * (C * Real.rpow X (-(omega / 12))) := by
  have hendpoint : ∀ z ∈ S, beta z ≤ relativePoint J := by
    intro z hz
    have := hbetaGap z hz
    unfold relativePoint
    linarith
  rw [← sum_relativeCells_eq S beta
    (fun z => (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1)))
    hbetaLow hendpoint]
  calc
    (∑ j ∈ Finset.range J,
        ∑ z ∈ relativeCell S beta j,
          (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ∑ _j ∈ Finset.range J,
        C * Real.rpow X (-(omega / 12)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact relativeCellMass_le_of_density S multiplicity beta
            hepsilon hu0 hu (hmeshGap j (Finset.mem_range.mp hj)) hX hC
            (hdensity j (Finset.mem_range.mp hj))
    _ = (J : ℝ) * (C * Real.rpow X (-(omega / 12))) := by simp

/-- If the exact mesh cardinality is at most `log X`, the sole cost of
integrating the pointwise density bound is one explicit logarithm. -/
theorem relativeNearMass_le_log_mul
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u omega X C : ℝ} {J : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaGap : ∀ z ∈ S, beta z ≤ 1 - omega)
    (hterminal : relativeDistance J ≤ omega)
    (hmeshGap : ∀ j < J, omega ≤ relativeDistance j)
    (hJlog : (J : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ j < J,
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow X
          ((21 / 10) * (tau epsilon + u) *
            (1 - relativePoint j))) :
    (∑ z ∈ S,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  have hcard := relativeNearMass_le_card_mul S multiplicity beta
    hepsilon hu0 hu hbetaLow hbetaGap hterminal hmeshGap hX hC hdensity
  exact hcard.trans (mul_le_mul_of_nonneg_right hJlog
    (mul_nonneg hC (Real.rpow_nonneg (zero_le_one.trans hX) _)))

/-- Final equation-(2.7) mesh form.  A proposed logarithmic depth `L` only
has to reach the zero-free gap.  The proof chooses the first such mesh point,
derives both endpoint inequalities, and pays at most the single displayed
`log X` factor.  Hence no cutoff minimality or summation fact remains among
the hypotheses.

The local premise `hdensity` is precisely the pointwise `21/10` density
inequality after converting `qT` to the explicit ratio `tau epsilon + u`.
-/
theorem relativeNearMass_le_log_mul_of_depth
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u omega X C : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaGap : ∀ z ∈ S, beta z ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ j < L,
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow X
          ((21 / 10) * (tau epsilon + u) *
            (1 - relativePoint j))) :
    (∑ z ∈ S,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  let P : ℕ → Prop := fun n => relativeDistance n ≤ omega
  have hP : ∃ n, P n := ⟨L, hdepth⟩
  let J := Nat.find hP
  have hterminal : relativeDistance J ≤ omega := Nat.find_spec hP
  have hJL : J ≤ L := Nat.find_min' hP hdepth
  have hmeshGap : ∀ j < J, omega ≤ relativeDistance j := by
    intro j hj
    have hnot : ¬ P j := Nat.find_min hP hj
    dsimp [P] at hnot
    exact (lt_of_not_ge hnot).le
  have hJlog : (J : ℝ) ≤ Real.log X := by
    have hJLreal : (J : ℝ) ≤ (L : ℝ) := by exact_mod_cast hJL
    exact hJLreal.trans hLlog
  apply relativeNearMass_le_log_mul S multiplicity beta
    hepsilon hu0 hu hbetaLow hbetaGap hterminal hmeshGap hJlog hX hC
  intro j hj
  exact hdensity j (lt_of_lt_of_le hj hJL)

/-- Source-base version of the final mesh theorem.  Here `R` is literally the
base occurring in the pointwise density theorem (for the intended
application, `R = q*T`).  The inequality `R ≤ X^(tau epsilon + u)` is the
entire base-conversion allowance; the proof preserves the exact source power
`(21/10) * (1-sigma_j)` before doing that conversion. -/
theorem relativeNearMass_le_log_mul_of_source_density
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon u omega X C R : ℝ} {L : ℕ}
    (hepsilon : 0 ≤ epsilon) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 315)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaGap : ∀ z ∈ S, beta z ≤ 1 - omega)
    (hdepth : relativeDistance L ≤ omega)
    (hLlog : (L : ℝ) ≤ Real.log X)
    (hX : 1 ≤ X) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRtoX : R ≤ Real.rpow X (tau epsilon + u))
    (hdensity : ∀ j < L,
      ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow R
          ((21 / 10) * (1 - relativePoint j))) :
    (∑ z ∈ S,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      Real.log X * (C * Real.rpow X (-(omega / 12))) := by
  apply relativeNearMass_le_log_mul_of_depth S multiplicity beta
    hepsilon hu0 hu hbetaLow hbetaGap hdepth hLlog hX hC
  intro j hj
  have he : 0 ≤ (21 / 10 : ℝ) * (1 - relativePoint j) := by
    exact mul_nonneg (by norm_num) (by linarith [relativePoint_le_one j])
  have hpow : Real.rpow R ((21 / 10) * (1 - relativePoint j)) ≤
      Real.rpow (Real.rpow X (tau epsilon + u))
        ((21 / 10) * (1 - relativePoint j)) :=
    Real.rpow_le_rpow hR hRtoX he
  calc
    ((∑ z ∈ S.filter (fun z => relativePoint j ≤ beta z),
        multiplicity z : ℕ) : ℝ) ≤
      C * Real.rpow R ((21 / 10) * (1 - relativePoint j)) :=
        hdensity j hj
    _ ≤ C * Real.rpow (Real.rpow X (tau epsilon + u))
        ((21 / 10) * (1 - relativePoint j)) :=
      mul_le_mul_of_nonneg_left hpow hC
    _ = C * Real.rpow X
        ((21 / 10) * (tau epsilon + u) *
          (1 - relativePoint j)) := by
      have hrpow :
          Real.rpow (Real.rpow X (tau epsilon + u))
              ((21 / 10) * (1 - relativePoint j)) =
            Real.rpow X
              ((tau epsilon + u) *
                ((21 / 10) * (1 - relativePoint j))) :=
        (Real.rpow_mul (zero_le_one.trans hX)
          (tau epsilon + u)
          ((21 / 10) * (1 - relativePoint j))).symm
      rw [hrpow]
      congr 2
      ring

end
end MAPRelativeNearOneMesh27

#print axioms MAPRelativeNearOneMesh27.exists_relative_cell
#print axioms MAPRelativeNearOneMesh27.biUnion_relativeCell_eq
#print axioms MAPRelativeNearOneMesh27.sum_relativeCells_eq
#print axioms MAPRelativeNearOneMesh27.relativeCellMass_le_of_density
#print axioms MAPRelativeNearOneMesh27.relativeNearMass_le_card_mul
#print axioms MAPRelativeNearOneMesh27.relativeNearMass_le_log_mul
#print axioms MAPRelativeNearOneMesh27.exists_minimal_relative_cutoff
#print axioms MAPRelativeNearOneMesh27.relativeNearMass_le_log_mul_of_depth
#print axioms MAPRelativeNearOneMesh27.relativeNearMass_le_log_mul_of_source_density
