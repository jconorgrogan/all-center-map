import CGLv2PolylogConductorDensity
import APRegularNearMeshRoute

/-!
# An epsilon-fine CGL mesh up to the Jutila collar

The fixed `1/24` relative mesh is too coarse to use the sharp `30/13`
term of CGL v2 above `4/5` when `epsilon` is arbitrarily small.  This file
uses an additive mesh of width `epsilon / 12000` only on the finite compact
bridge from `4/5` to `relativePoint collarIndex`.  The exact weighted
exponent retains `epsilon / 400`; all cardinality losses remain finite (and
therefore logarithmic/polynomially absorbable at the eventual endpoint).

No analytic theorem is introduced here.  The local density bound is an
explicit premise of the finite integration theorem.
-/

namespace MAPCGLNearFineMesh

open scoped BigOperators
open CGLMeshFormalization MAPGuthMaynard MAPRelativeNearOneMesh27
open MAPJutilaCollarMeshCutoff

noncomputable section

/-- Width of the epsilon-dependent compact bridge mesh. -/
def fineDelta (epsilon : ℝ) : ℝ := epsilon / 12000

/-- Left endpoint of cell `j`. -/
def finePoint (epsilon : ℝ) (j : ℕ) : ℝ :=
  4 / 5 + (j : ℝ) * fineDelta epsilon

/-- The exact number of cells needed to reach the first collar mesh point. -/
def fineCellCount (epsilon : ℝ) : ℕ :=
  ⌊(relativePoint collarIndex - 4 / 5) / fineDelta epsilon⌋₊ + 1

/-- Half-open epsilon-fine cell. -/
def fineCell {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) (epsilon : ℝ) (j : ℕ) : Finset ι :=
  S.filter fun z => finePoint epsilon j < beta z ∧
    beta z ≤ finePoint epsilon j + fineDelta epsilon

theorem fineDelta_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < fineDelta epsilon := by
  unfold fineDelta
  positivity

@[simp] theorem finePoint_zero (epsilon : ℝ) :
    finePoint epsilon 0 = 4 / 5 := by
  simp [finePoint]

theorem collarDistance_lower :
    (1 / 300 : ℝ) ≤ relativeDistance collarIndex := by
  norm_num [relativeDistance, collarIndex]

theorem finePoint_cellCount_left_le_collar {epsilon : ℝ}
    (hepsilon : 0 < epsilon) {j : ℕ} (hj : j < fineCellCount epsilon) :
    finePoint epsilon j ≤ relativePoint collarIndex := by
  have hD : 0 < fineDelta epsilon := fineDelta_pos hepsilon
  have hR0 : 0 ≤
      (relativePoint collarIndex - 4 / 5) / fineDelta epsilon := by
    apply div_nonneg
    · have hcollar := relativePoint_collarIndex
      norm_num at hcollar ⊢
      linarith
    · exact hD.le
  have hjfloor : j ≤
      ⌊(relativePoint collarIndex - 4 / 5) / fineDelta epsilon⌋₊ := by
    simpa [fineCellCount] using Nat.le_of_lt_succ hj
  have hfloor :
      (⌊(relativePoint collarIndex - 4 / 5) / fineDelta epsilon⌋₊ : ℝ) ≤
        (relativePoint collarIndex - 4 / 5) / fineDelta epsilon :=
    Nat.floor_le hR0
  have hjdiv : (j : ℝ) ≤
      (relativePoint collarIndex - 4 / 5) / fineDelta epsilon :=
    (Nat.cast_le.mpr hjfloor).trans hfloor
  have hjmul : (j : ℝ) * fineDelta epsilon ≤
      relativePoint collarIndex - 4 / 5 :=
    (le_div_iff₀ hD).mp hjdiv
  dsimp [finePoint]
  linarith

/-- Every point of the compact bridge is assigned to one epsilon-fine cell. -/
theorem exists_fineCell {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbetaLow : 4 / 5 < beta)
    (hbetaHigh : beta ≤ relativePoint collarIndex) :
    ∃ j < fineCellCount epsilon,
      finePoint epsilon j < beta ∧
        beta ≤ finePoint epsilon j + fineDelta epsilon := by
  let y : ℝ := (beta - 4 / 5) / fineDelta epsilon
  let j : ℕ := ⌈y⌉₊ - 1
  have hD : 0 < fineDelta epsilon := fineDelta_pos hepsilon
  have hy0 : 0 < y := div_pos (sub_pos.mpr hbetaLow) hD
  have hceilPos : 0 < ⌈y⌉₊ := by
    exact Nat.ceil_pos.mpr hy0
  have hjadd : j + 1 = ⌈y⌉₊ := by
    dsimp [j]
    omega
  have hyleft : (j : ℝ) < y := by
    have hcast : (j : ℝ) = (⌈y⌉₊ : ℝ) - 1 := by
      dsimp [j]
      exact Nat.cast_pred hceilPos
    rw [hcast]
    have hceilLt : (⌈y⌉₊ : ℝ) < y + 1 :=
      Nat.ceil_lt_add_one hy0.le
    linarith
  have hyright : y ≤ (j : ℝ) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, hjadd]
    exact Nat.le_ceil y
  have hleft : finePoint epsilon j < beta := by
    have := (lt_div_iff₀ hD).mp hyleft
    dsimp [finePoint] at *
    linarith
  have hright : beta ≤ finePoint epsilon j + fineDelta epsilon := by
    have := (div_le_iff₀ hD).mp hyright
    dsimp [finePoint] at *
    linarith
  have hyCap : y ≤
      (relativePoint collarIndex - 4 / 5) / fineDelta epsilon := by
    dsimp [y]
    exact (div_le_div_iff_of_pos_right hD).2 (by linarith)
  have hceilCap : ⌈y⌉₊ ≤
      ⌊(relativePoint collarIndex - 4 / 5) / fineDelta epsilon⌋₊ + 1 := by
    have hcap0 : 0 ≤
        (relativePoint collarIndex - 4 / 5) / fineDelta epsilon :=
      le_trans hy0.le hyCap
    have hceilMono := Nat.ceil_mono hyCap
    exact hceilMono.trans (Nat.ceil_le_floor_add_one _)
  have hjcount : j < fineCellCount epsilon := by
    dsimp [j, fineCellCount]
    omega
  exact ⟨j, hjcount, hleft, hright⟩

/-- Distinct fine cells are disjoint. -/
theorem fineCell_pairwise_disjoint {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) :
    (Finset.range (fineCellCount epsilon) : Set ℕ).PairwiseDisjoint
      (fineCell S beta epsilon) := by
  intro j _hj k _hk hjk
  apply Finset.disjoint_left.2
  intro z hzj hzk
  have zj := (Finset.mem_filter.mp hzj).2
  have zk := (Finset.mem_filter.mp hzk).2
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have hcast : (j : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hjklt
    have hD := (fineDelta_pos hepsilon).le
    have hpoints : finePoint epsilon j + fineDelta epsilon ≤
        finePoint epsilon k := by
      dsimp [finePoint]
      nlinarith
    linarith
  · have hcast : (k : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast hkjlt
    have hD := (fineDelta_pos hepsilon).le
    have hpoints : finePoint epsilon k + fineDelta epsilon ≤
        finePoint epsilon j := by
      dsimp [finePoint]
      nlinarith
    linarith

/-- The fine cells exactly partition any support in the compact bridge. -/
theorem biUnion_fineCell_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta : ι → ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaHigh : ∀ z ∈ S, beta z ≤ relativePoint collarIndex) :
    (Finset.range (fineCellCount epsilon)).biUnion
        (fineCell S beta epsilon) = S := by
  ext z
  constructor
  · intro hz
    obtain ⟨j, _hj, hzcell⟩ := Finset.mem_biUnion.mp hz
    exact (Finset.mem_filter.mp hzcell).1
  · intro hz
    obtain ⟨j, hj, hlow, hhigh⟩ :=
      exists_fineCell hepsilon (hbetaLow z hz) (hbetaHigh z hz)
    exact Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_range.mpr hj,
        Finset.mem_filter.mpr ⟨hz, hlow, hhigh⟩⟩

/-- Exact finite mass decomposition. -/
theorem sum_fineCells_eq {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (beta weight : ι → ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaHigh : ∀ z ∈ S, beta z ≤ relativePoint collarIndex) :
    (∑ j ∈ Finset.range (fineCellCount epsilon),
      ∑ z ∈ fineCell S beta epsilon j, weight z) =
      ∑ z ∈ S, weight z := by
  rw [← Finset.sum_biUnion (fineCell_pairwise_disjoint S beta epsilon hepsilon)]
  rw [biUnion_fineCell_eq S beta hepsilon hbetaLow hbetaHigh]

/-- Exact `30/13` weighted exponent on the fine compact bridge. -/
theorem fine_cell_exponent_bound
    {epsilon sigma eta : ℝ} {j : ℕ}
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hsigma : finePoint epsilon j ≤ sigma)
    (hsigmaCap : sigma ≤ relativePoint collarIndex)
    (heta0 : 0 ≤ eta) (heta : eta ≤ epsilon / 2000) :
    tau epsilon * (densityCoeff * (1 - finePoint epsilon j) + eta) +
        2 * (finePoint epsilon j + fineDelta epsilon - 1) ≤
      -(epsilon / 400) := by
  have htau : tau epsilon ≤ 1 := by
    unfold tau
    linarith
  have htau0 : 0 < tau epsilon := tau_pos hepsilonCap
  have hdist : (1 / 300 : ℝ) ≤ 1 - finePoint epsilon j := by
    have hpointCap : finePoint epsilon j ≤ relativePoint collarIndex :=
      hsigma.trans hsigmaCap
    have hcollar := collarDistance_lower
    have heq := one_sub_relativePoint collarIndex
    linarith
  have hetaCost : tau epsilon * eta ≤ epsilon / 2000 := by
    nlinarith
  have hid :
      tau epsilon * (densityCoeff * (1 - finePoint epsilon j) + eta) +
          2 * (finePoint epsilon j + fineDelta epsilon - 1) =
        -((15 / 13) * epsilon) * (1 - finePoint epsilon j) +
          tau epsilon * eta + 2 * fineDelta epsilon := by
    unfold tau densityCoeff
    ring
  rw [hid]
  unfold fineDelta
  nlinarith

/-- A fine cell's weighted mass follows from a cumulative `30/13` count at
its left endpoint. -/
theorem fineCellMass_le_of_density
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon eta X C : ℝ} {j : ℕ}
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hj : j < fineCellCount epsilon)
    (heta0 : 0 ≤ eta) (heta : eta ≤ epsilon / 2000)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity :
      ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - finePoint epsilon j) + eta)) :
    (∑ z ∈ fineCell S beta epsilon j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      C * Real.rpow X (-(epsilon / 400)) := by
  let W := Real.rpow X
    (2 * (finePoint epsilon j + fineDelta epsilon - 1))
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hcount :
      (∑ z ∈ fineCell S beta epsilon j, multiplicity z : ℕ) ≤
        ∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro z hz
      have hz' := Finset.mem_filter.mp hz
      exact Finset.mem_filter.mpr ⟨hz'.1, hz'.2.1.le⟩
    · intro z _ _
      exact Nat.zero_le _
  have hmass :
      (∑ z ∈ fineCell S beta epsilon j,
          (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
        ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
            multiplicity z : ℕ) : ℝ) * W := by
    calc
      (∑ z ∈ fineCell S beta epsilon j,
          (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
        ∑ z ∈ fineCell S beta epsilon j,
          (multiplicity z : ℝ) * W := by
            apply Finset.sum_le_sum
            intro z hz
            apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
            apply Real.rpow_le_rpow_of_exponent_le hX
            have hzupper := (Finset.mem_filter.mp hz).2.2
            linarith
      _ = ((∑ z ∈ fineCell S beta epsilon j,
          multiplicity z : ℕ) : ℝ) * W := by
            push_cast
            rw [Finset.sum_mul]
      _ ≤ ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z : ℕ) : ℝ) * W := by
            apply mul_le_mul_of_nonneg_right
            · exact_mod_cast hcount
            · exact Real.rpow_nonneg hXpos.le _
  have hcollapse :
      Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - finePoint epsilon j) + eta) =
        Real.rpow X (tau epsilon *
          (densityCoeff * (1 - finePoint epsilon j) + eta)) :=
    (Real.rpow_mul hXpos.le _ _).symm
  have hweighted :
      ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z : ℕ) : ℝ) * W ≤
        C * Real.rpow X (-(epsilon / 400)) := by
    calc
      ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z : ℕ) : ℝ) * W ≤
        (C * Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - finePoint epsilon j) + eta)) * W :=
        mul_le_mul_of_nonneg_right hdensity (Real.rpow_nonneg hXpos.le _)
      _ = C * Real.rpow X
          (tau epsilon *
              (densityCoeff * (1 - finePoint epsilon j) + eta) +
            2 * (finePoint epsilon j + fineDelta epsilon - 1)) := by
        rw [hcollapse, mul_assoc]
        congr 1
        exact (Real.rpow_add hXpos _ _).symm
      _ ≤ C * Real.rpow X (-(epsilon / 400)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Real.rpow_le_rpow_of_exponent_le hX
        exact fine_cell_exponent_bound hepsilon hepsilonCap
          le_rfl (finePoint_cellCount_left_le_collar hepsilon hj)
          heta0 heta
  exact hmass.trans hweighted

/-- Finite integration of all epsilon-fine compact cells. -/
theorem fineCompactMass_le_card_mul
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon eta X C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonCap : epsilon ≤ 1 / 10)
    (hbetaLow : ∀ z ∈ S, 4 / 5 < beta z)
    (hbetaHigh : ∀ z ∈ S, beta z ≤ relativePoint collarIndex)
    (heta0 : 0 ≤ eta) (heta : eta ≤ epsilon / 2000)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : ∀ j < fineCellCount epsilon,
      ((∑ z ∈ S.filter (fun z => finePoint epsilon j ≤ beta z),
          multiplicity z : ℕ) : ℝ) ≤
        C * Real.rpow (Real.rpow X (tau epsilon))
          (densityCoeff * (1 - finePoint epsilon j) + eta)) :
    (∑ z ∈ S, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
      (fineCellCount epsilon : ℝ) *
        (C * Real.rpow X (-(epsilon / 400))) := by
  rw [← sum_fineCells_eq S beta
    (fun z => (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1)))
    hepsilon hbetaLow hbetaHigh]
  calc
    (∑ j ∈ Finset.range (fineCellCount epsilon),
      ∑ z ∈ fineCell S beta epsilon j,
        (multiplicity z : ℝ) * Real.rpow X (2 * (beta z - 1))) ≤
      ∑ _j ∈ Finset.range (fineCellCount epsilon),
        C * Real.rpow X (-(epsilon / 400)) := by
          apply Finset.sum_le_sum
          intro j hj
          exact fineCellMass_le_of_density S multiplicity beta
            hepsilon hepsilonCap (Finset.mem_range.mp hj)
            heta0 heta hX hC (hdensity j (Finset.mem_range.mp hj))
    _ = (fineCellCount epsilon : ℝ) *
        (C * Real.rpow X (-(epsilon / 400))) := by simp

end
end MAPCGLNearFineMesh

#print axioms MAPCGLNearFineMesh.exists_fineCell
#print axioms MAPCGLNearFineMesh.sum_fineCells_eq
#print axioms MAPCGLNearFineMesh.fine_cell_exponent_bound
#print axioms MAPCGLNearFineMesh.fineCellMass_le_of_density
#print axioms MAPCGLNearFineMesh.fineCompactMass_le_card_mul
