import PaperMeshExponent
import APZeroDensityCertificate

/-!
# Low-beta and mesh closure for Proposition 2.2

This file closes only the elementary bookkeeping around the split at
`beta = 1 / 2 + delta0`.  The low strip is taken half-open on the right and
the compact mesh is closed on the left, so no zero is lost and no endpoint
convention is hidden.  The analytic zero-count estimate remains a local
premise of the final weighted-mass theorem.
-/

namespace MAPLowBetaMeshClosure

open scoped BigOperators

noncomputable section

open MAPGuthMaynard
open DirichletZeros

/-- The short-interval exponent in Proposition 2.2. -/
def theta (epsilon : ℝ) : ℝ := 2 / 15 + epsilon

/-- The literal lower cutoff printed in the manuscript. -/
def paperDelta0 (epsilon : ℝ) : ℝ :=
  min (epsilon / 16) (1 / 120)

/-- A literal legal mesh width.  Any smaller positive width also works. -/
def paperDelta (epsilon : ℝ) : ℝ :=
  min (1 / 100) (3 * epsilon / 52)

/-- The exponent advertised by the abstract-only coarse `7/3` consequence. -/
def coarseDensityCoeff : ℝ := 7 / 3

/-- Reserve left by the coarse coefficient at the paper height. -/
def coarseReserve (epsilon : ℝ) : ℝ :=
  2 - coarseDensityCoeff * tau epsilon

/-- A legal height for the counterfactual `1/7 + epsilon` fallback. -/
def coarseSafeTau (epsilon : ℝ) : ℝ := 6 / 7 - epsilon / 2

/-! ## Literal parameter legality -/

theorem theta_add_tau (epsilon : ℝ) :
    theta epsilon + tau epsilon = 1 + epsilon / 2 := by
  unfold theta tau
  ring

/-- This is the `X^{-epsilon/2}` explicit-formula truncation margin. -/
theorem truncation_exponent (epsilon : ℝ) :
    1 - tau epsilon - theta epsilon = -(epsilon / 2) := by
  unfold theta tau
  ring

theorem one_sub_tau (epsilon : ℝ) :
    1 - tau epsilon = 2 / 15 + epsilon / 2 := by
  unfold tau
  ring

theorem one_sub_tau_lt_theta {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    1 - tau epsilon < theta epsilon := by
  rw [one_sub_tau]
  unfold theta
  linarith

theorem tau_le_thirteen_fifteenths {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    tau epsilon ≤ 13 / 15 := by
  unfold tau
  linarith

theorem forty_nine_sixtieths_le_tau {epsilon : ℝ}
    (hepsilon_le : epsilon ≤ 1 / 10) :
    49 / 60 ≤ tau epsilon := by
  unfold tau
  linarith

theorem paperDelta0_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < paperDelta0 epsilon := by
  unfold paperDelta0
  exact lt_min (div_pos hepsilon (by norm_num)) (by norm_num)

theorem paperDelta0_nonneg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 ≤ paperDelta0 epsilon := (paperDelta0_pos hepsilon).le

theorem paperDelta0_le_epsilon_sixteenth (epsilon : ℝ) :
    paperDelta0 epsilon ≤ epsilon / 16 := by
  exact min_le_left _ _

theorem paperDelta0_le_one_over_120 (epsilon : ℝ) :
    paperDelta0 epsilon ≤ 1 / 120 := by
  exact min_le_right _ _

/-- The manuscript cutoff is more than small enough for the elementary
low-strip reserve used in `ZeroDensityArithmetic.lowRangeExponent_bound`. -/
theorem paperDelta0_le_low_reserve (epsilon : ℝ) :
    paperDelta0 epsilon ≤ (1 - tau epsilon) / 8 := by
  have h := paperDelta0_le_epsilon_sixteenth epsilon
  unfold tau
  linarith

theorem paperDelta_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < paperDelta epsilon := by
  unfold paperDelta
  exact lt_min (by norm_num) (div_pos (mul_pos (by norm_num) hepsilon) (by norm_num))

theorem paperDelta_le_one_over_100 (epsilon : ℝ) :
    paperDelta epsilon ≤ 1 / 100 := by
  exact min_le_left _ _

theorem paperDelta_le_three_epsilon_over_52 (epsilon : ℝ) :
    paperDelta epsilon ≤ 3 * epsilon / 52 := by
  exact min_le_right _ _

theorem etaZD_pos {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10) :
    0 < etaZD epsilon := by
  unfold etaZD
  exact div_pos (mul_pos (by norm_num) hepsilon)
    (mul_pos (by norm_num) (tau_pos hepsilon_le))

/-! ## A disjoint, endpoint-complete split -/

/-- Every beta at or below `4/5` is either in the half-open low strip or in a
literal compact mesh cell.  Equality at the lower boundary belongs to cell
zero, not to the low strip. -/
theorem low_or_exists_paper_mesh_cell {epsilon beta : ℝ}
    (hepsilon : 0 < epsilon) (hbeta_high : beta ≤ 4 / 5) :
    beta < 1 / 2 + paperDelta0 epsilon ∨
      ∃ j ∈ Finset.range (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
        meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ beta ∧
          beta < meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
            paperDelta epsilon := by
  by_cases hlow : beta < 1 / 2 + paperDelta0 epsilon
  · exact Or.inl hlow
  · right
    exact exists_mesh_cell (paperDelta_pos hepsilon) (le_of_not_gt hlow) hbeta_high

/-- The two branches in the preceding split are literally disjoint. -/
theorem low_strip_disjoint_from_paper_mesh
    {epsilon beta : ℝ} {j : ℕ}
    (hepsilon : 0 < epsilon)
    (hlow : beta < 1 / 2 + paperDelta0 epsilon)
    (hcell : meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ beta) :
    False := by
  dsimp [meshPoint] at hcell
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hDelta : 0 ≤ paperDelta epsilon := (paperDelta_pos hepsilon).le
  have : 1 / 2 + paperDelta0 epsilon ≤ beta := by
    nlinarith
  linarith

/-- The lower mesh endpoint is included exactly. -/
theorem lower_endpoint_is_first_mesh_point (epsilon : ℝ) :
    meshPoint (paperDelta0 epsilon) (paperDelta epsilon) 0 =
      1 / 2 + paperDelta0 epsilon := by
  simp [meshPoint]

/-- In particular the equality endpoint belongs to the first half-open cell. -/
theorem lower_endpoint_mem_first_mesh_cell {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    0 ∈ Finset.range
        (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)) ∧
      meshPoint (paperDelta0 epsilon) (paperDelta epsilon) 0 ≤
          1 / 2 + paperDelta0 epsilon ∧
      1 / 2 + paperDelta0 epsilon <
        meshPoint (paperDelta0 epsilon) (paperDelta epsilon) 0 +
          paperDelta epsilon := by
  constructor
  · simp [meshCellCount]
  · rw [lower_endpoint_is_first_mesh_point]
    exact ⟨le_rfl, lt_add_of_pos_right _ (paperDelta_pos hepsilon)⟩

/-- The endpoint `beta = 4/5` is covered by a legal cell; it is not lost by
the half-open cell convention. -/
theorem four_fifths_has_paper_mesh_cell {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ j ∈ Finset.range (meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)),
      meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ 4 / 5 ∧
        (4 / 5 : ℝ) <
          meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j +
            paperDelta epsilon := by
  exact exists_mesh_cell (paperDelta_pos hepsilon) (by
    have hcap := paperDelta0_le_one_over_120 epsilon
    linarith) le_rfl

/-- Every left endpoint at which the density theorem is invoked lies in its
published range. -/
theorem paper_mesh_left_endpoint_le_four_fifths {epsilon : ℝ}
    (hepsilon : 0 < epsilon) {j : ℕ}
    (hj : j < meshCellCount (paperDelta0 epsilon) (paperDelta epsilon)) :
    meshPoint (paperDelta0 epsilon) (paperDelta epsilon) j ≤ 4 / 5 := by
  apply meshPoint_le_four_fifths (paperDelta_pos hepsilon)
  · exact (paperDelta0_le_one_over_120 epsilon).trans (by norm_num)
  · exact hj

/-! ## Low-beta weighted mass -/

/-- The literal low-strip exponent before absorbing the polylogarithmic
character count.  It is stronger than a merely epsilon-dependent saving. -/
theorem low_beta_exponent_bound {epsilon : ℝ} :
    tau epsilon - 1 + 2 * paperDelta0 epsilon ≤
      -(2 / 15 + 3 * epsilon / 8) := by
  have hdelta := paperDelta0_le_epsilon_sixteenth epsilon
  unfold tau
  linarith

theorem low_beta_exponent_le_neg_two_fifteenths {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    tau epsilon - 1 + 2 * paperDelta0 epsilon ≤ -(2 / 15) := by
  calc
    tau epsilon - 1 + 2 * paperDelta0 epsilon ≤
        -(2 / 15 + 3 * epsilon / 8) := low_beta_exponent_bound
    _ ≤ -(2 / 15) := by linarith

/-- Monotonicity of the zero weight on the low strip, with arbitrary finite
multiplicities.  This is the exact finite step before the elementary local
zero count is inserted. -/
theorem low_beta_weighted_mass_le_count_weight
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon X : ℝ} (hX : 1 ≤ X)
    (hbeta : ∀ z ∈ s, beta z ≤ 1 / 2 + paperDelta0 epsilon) :
    (∑ z ∈ s, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
      ((∑ z ∈ s, multiplicity z : ℕ) : ℝ) *
        Real.rpow X (-1 + 2 * paperDelta0 epsilon) := by
  let R : ℝ := Real.rpow X (-1 + 2 * paperDelta0 epsilon)
  calc
    (∑ z ∈ s, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
        ∑ z ∈ s, (multiplicity z : ℝ) * R := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.rpow_le_rpow_of_exponent_le hX
      have := hbeta z hz
      linarith
    _ = ((∑ z ∈ s, multiplicity z : ℕ) : ℝ) * R := by
      push_cast
      rw [Finset.sum_mul]

/-- Once the elementary zero count and the polylogarithmic family size have
been absorbed into `X^(tau + xi)` with `xi <= 1/30`, the whole low strip has
the fixed saving `X^(-1/10)`.  `hcount` is deliberately visible: this theorem
does not assume or manufacture an analytic zero-count estimate. -/
theorem low_beta_weighted_mass_power_saving
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (multiplicity : ι → ℕ) (beta : ι → ℝ)
    {epsilon X C xi : ℝ}
    (hepsilon : 0 < epsilon) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hxi : xi ≤ 1 / 30)
    (hbeta : ∀ z ∈ s, beta z ≤ 1 / 2 + paperDelta0 epsilon)
    (hcount : ((∑ z ∈ s, multiplicity z : ℕ) : ℝ) ≤
      C * Real.rpow X (tau epsilon + xi)) :
    (∑ z ∈ s, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
      C * Real.rpow X (-(1 / 10)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hweight_nonneg :
      0 ≤ Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
    Real.rpow_nonneg hXpos.le _
  calc
    (∑ z ∈ s, (multiplicity z : ℝ) *
        Real.rpow X (2 * (beta z - 1))) ≤
        ((∑ z ∈ s, multiplicity z : ℕ) : ℝ) *
          Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
      low_beta_weighted_mass_le_count_weight s multiplicity beta hX hbeta
    _ ≤ (C * Real.rpow X (tau epsilon + xi)) *
          Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
      mul_le_mul_of_nonneg_right hcount hweight_nonneg
    _ = C * Real.rpow X
          ((tau epsilon + xi) + (-1 + 2 * paperDelta0 epsilon)) := by
      rw [mul_assoc]
      congr 1
      exact (Real.rpow_add hXpos _ _).symm
    _ ≤ C * Real.rpow X (-(1 / 10)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hlow := low_beta_exponent_bound (epsilon := epsilon)
      linarith

/-! ## Instantiation on the literal Dirichlet-L zero divisor -/

variable {q : ℕ} [NeZero q]

/-- The actual multiplicity-aware low strip inside the standard nontrivial
rectangle `0 <= re rho <= 1`.  The strict filter matches the disjoint split
above; the equality endpoint is assigned to mesh cell zero. -/
def actualLowBetaSupport (chi : DirichletCharacter ℂ q)
    (T epsilon : ℝ) : Finset ℂ :=
  (zeroSupport chi 0 T).filter fun rho =>
    rho.re < 1 / 2 + paperDelta0 epsilon

/-- The literal low-beta contribution to the weighted zero mass. -/
def actualLowBetaMass (chi : DirichletCharacter ℂ q)
    (X T epsilon : ℝ) : ℝ :=
  ∑ rho ∈ actualLowBetaSupport chi T epsilon,
    (zeroMultiplicity chi 0 T rho : ℝ) *
      Real.rpow X (2 * (rho.re - 1))

/-- The divisor-backed low-beta mass is bounded by the full multiplicity-aware
zero count times the largest low-strip weight. -/
theorem actualLowBetaMass_le_fullCount
    (chi : DirichletCharacter ℂ q) {X T epsilon : ℝ}
    (hX : 1 ≤ X) :
    actualLowBetaMass chi X T epsilon ≤
      (dirichletZeroCount chi 0 T : ℝ) *
        Real.rpow X (-1 + 2 * paperDelta0 epsilon) := by
  let S := actualLowBetaSupport chi T epsilon
  let R := Real.rpow X (-1 + 2 * paperDelta0 epsilon)
  have hfinite := low_beta_weighted_mass_le_count_weight
    S (fun rho => zeroMultiplicity chi 0 T rho) Complex.re hX (by
      intro rho hrho
      have hlt := (Finset.mem_filter.mp hrho).2
      exact hlt.le)
  have hsubset : S ⊆ zeroSupport chi 0 T := by
    intro rho hrho
    exact (Finset.mem_filter.mp hrho).1
  have hcountNat :
      (∑ rho ∈ S, zeroMultiplicity chi 0 T rho) ≤
        dirichletZeroCount chi 0 T := by
    unfold dirichletZeroCount
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun _ _ _ => Nat.zero_le _)
  have hRnonneg : 0 ≤ R :=
    Real.rpow_nonneg (zero_le_one.trans hX) _
  calc
    actualLowBetaMass chi X T epsilon ≤
        ((∑ rho ∈ S, zeroMultiplicity chi 0 T rho : ℕ) : ℝ) * R := by
      simpa only [actualLowBetaMass, S, R] using hfinite
    _ ≤ (dirichletZeroCount chi 0 T : ℝ) * R := by
      apply mul_le_mul_of_nonneg_right _ hRnonneg
      exact_mod_cast hcountNat

/-- The exact low-strip consequence of an elementary zero-count estimate.
The count premise is the only analytic leaf in this declaration. -/
theorem actualLowBetaMass_power_saving
    (chi : DirichletCharacter ℂ q)
    {epsilon X T C xi : ℝ}
    (hepsilon : 0 < epsilon) (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hxi : xi ≤ 1 / 30)
    (hcount : (dirichletZeroCount chi 0 T : ℝ) ≤
      C * Real.rpow X (tau epsilon + xi)) :
    actualLowBetaMass chi X T epsilon ≤
      C * Real.rpow X (-(1 / 10)) := by
  have hXpos : 0 < X := zero_lt_one.trans_le hX
  have hweight_nonneg :
      0 ≤ Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
    Real.rpow_nonneg hXpos.le _
  calc
    actualLowBetaMass chi X T epsilon ≤
        (dirichletZeroCount chi 0 T : ℝ) *
          Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
      actualLowBetaMass_le_fullCount chi hX
    _ ≤ (C * Real.rpow X (tau epsilon + xi)) *
          Real.rpow X (-1 + 2 * paperDelta0 epsilon) :=
      mul_le_mul_of_nonneg_right hcount hweight_nonneg
    _ = C * Real.rpow X
          ((tau epsilon + xi) + (-1 + 2 * paperDelta0 epsilon)) := by
      rw [mul_assoc]
      congr 1
      exact (Real.rpow_add hXpos _ _).symm
    _ ≤ C * Real.rpow X (-(1 / 10)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Real.rpow_le_rpow_of_exponent_le hX
      have hlow := low_beta_exponent_bound (epsilon := epsilon)
      linarith

/-! ## Compact mesh exponent with the chosen parameters -/

theorem chosen_cell_exponent_bound
    {epsilon sigma : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5) :
    tau epsilon *
          (densityCoeff * (1 - sigma) + etaZD epsilon) +
        2 * (sigma + paperDelta epsilon - 1) ≤
      -(3 * epsilon / 52) := by
  exact paper_cell_exponent_bound hepsilon hepsilon_le hsigma_high
    (paperDelta_le_three_epsilon_over_52 epsilon)

/-- The existing analytic-to-arithmetic cell theorem instantiated with the
literal legal mesh width. -/
theorem chosen_densityAtHeight_mul_weight_le
    {epsilon sigma X C zeroCount : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon_le : epsilon ≤ 1 / 10)
    (hsigma_high : sigma ≤ 4 / 5)
    (hX : 1 ≤ X) (hC : 0 ≤ C)
    (hdensity : zeroCount ≤
      C * Real.rpow (Real.rpow X (tau epsilon))
        (densityCoeff * (1 - sigma) + etaZD epsilon)) :
    zeroCount * Real.rpow X
        (2 * (sigma + paperDelta epsilon - 1)) ≤
      C * Real.rpow X (-(3 * epsilon / 52)) := by
  exact densityAtHeight_mul_weight_le hepsilon hepsilon_le hsigma_high
    (paperDelta_le_three_epsilon_over_52 epsilon) hX hC hdensity

/-- The other term in the Chen--Gupta--Li hybrid estimate has a much larger
height reserve; it is not the term fixing `2/15`. -/
theorem hybrid_first_term_reserve (epsilon : ℝ) :
    2 - 2 * tau epsilon = 4 / 15 + epsilon := by
  unfold tau
  ring

/-! ## Hostile counterfactual: the coarse `7/3` statement -/

theorem coarseReserve_eq (epsilon : ℝ) :
    coarseReserve epsilon = -(1 / 45) + 7 * epsilon / 6 := by
  unfold coarseReserve coarseDensityCoeff tau
  ring

theorem coarseReserve_pos_iff {epsilon : ℝ} :
    0 < coarseReserve epsilon ↔ 2 / 105 < epsilon := by
  rw [coarseReserve_eq]
  constructor <;> intro h <;> linarith

/-- At the worst compact endpoint, even before mesh and density losses, the
coarse theorem has a nonnegative exponent for `epsilon <= 2/105`. -/
theorem coarse_endpoint_exponent_eq (epsilon : ℝ) :
    tau epsilon * (coarseDensityCoeff * (1 - 4 / 5)) +
        2 * ((4 / 5 : ℝ) - 1) =
      1 / 225 - 7 * epsilon / 30 := by
  unfold tau coarseDensityCoeff
  ring

theorem coarse_endpoint_exponent_nonneg {epsilon : ℝ}
    (hepsilon : epsilon ≤ 2 / 105) :
    0 ≤ tau epsilon * (coarseDensityCoeff * (1 - 4 / 5)) +
        2 * ((4 / 5 : ℝ) - 1) := by
  rw [coarse_endpoint_exponent_eq]
  linarith

/-- Therefore no positive power saving can follow from the coarse coefficient
at the paper height for all positive epsilon. -/
theorem coarse_endpoint_cannot_save {epsilon c : ℝ}
    (hepsilon : epsilon ≤ 2 / 105) (hc : 0 < c) :
    ¬ tau epsilon * (coarseDensityCoeff * (1 - 4 / 5)) +
        2 * ((4 / 5 : ℝ) - 1) ≤ -c := by
  have hnonneg := coarse_endpoint_exponent_nonneg hepsilon
  linarith

/-- Moving the threshold to `1/7 + epsilon` restores the two strict margins
for the coarse coefficient. -/
theorem coarseSafeReserve_eq (epsilon : ℝ) :
    2 - coarseDensityCoeff * coarseSafeTau epsilon =
      7 * epsilon / 6 := by
  unfold coarseDensityCoeff coarseSafeTau
  ring

theorem coarseSafe_truncation_exponent (epsilon : ℝ) :
    1 - coarseSafeTau epsilon - (1 / 7 + epsilon) =
      -(epsilon / 2) := by
  unfold coarseSafeTau
  ring

end

end MAPLowBetaMeshClosure

#print axioms MAPLowBetaMeshClosure.low_or_exists_paper_mesh_cell
#print axioms MAPLowBetaMeshClosure.low_beta_weighted_mass_power_saving
#print axioms MAPLowBetaMeshClosure.actualLowBetaMass_power_saving
#print axioms MAPLowBetaMeshClosure.chosen_densityAtHeight_mul_weight_le
#print axioms MAPLowBetaMeshClosure.coarse_endpoint_cannot_save
