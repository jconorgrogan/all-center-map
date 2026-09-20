import GuthMaynardLengthComparison

/-!
# Exact closed-to-open-left endpoint adapter for the Heath--Brown/Jutila chain

Heath--Brown's Theorem 1.6 is exposed on `Finset.Icc M (2 * M)`, whereas
Jutila's Lemma 29.8 uses `Finset.Ioc M (2 * M)`.  These sets are not
identified here.  The closed block is split into the open-left block, the
row and column through `M`, and the single `(M,M)` atom.

The phase remains the literal coefficient-one ratio kernel throughout.  The
boundary correction therefore retains its full dependence on `W`.  Its
deterministic bound uses only the triangle inequality for the finite kernel;
no Heath--Brown or other analytic premise is introduced.
-/

namespace GuthMaynardHeathBrownIccIocEndpointAdapter

open scoped BigOperators
open GuthMaynardHeathBrownInterface
open GuthMaynardRatioKernelIdentity

noncomputable section

/-- One ordered-pair summand in the coefficient-one ratio second moment. -/
def ratioKernelSquare (W : Finset ℝ) (n m : ℕ) : ℝ :=
  ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 2

/-- The exact closed block occurring after the coefficient-one
Heath--Brown majorant. -/
def closedRatioSecondMoment (M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc M (2 * M),
    ∑ m ∈ Finset.Icc M (2 * M), ratioKernelSquare W n m

/-- The exact open-left block occurring in Jutila's length comparison. -/
def openLeftRatioSecondMoment (M : ℕ) (W : Finset ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc M (2 * M),
    ∑ m ∈ Finset.Ioc M (2 * M), ratioKernelSquare W n m

/-- The two cross arms caused by retaining the left endpoint `M`. -/
def leftEndpointCrossContribution (M : ℕ) (W : Finset ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc M (2 * M), ratioKernelSquare W M n) +
    ∑ n ∈ Finset.Ioc M (2 * M), ratioKernelSquare W n M

/-- The rank-one diagonal atom caused by retaining the left endpoint `M`. -/
def leftEndpointRankOneContribution (M : ℕ) (W : Finset ℝ) : ℝ :=
  ratioKernelSquare W M M

/-- The complete endpoint correction: two cross arms and one rank-one atom. -/
def leftEndpointBoundaryContribution (M : ℕ) (W : Finset ℝ) : ℝ :=
  leftEndpointCrossContribution M W + leftEndpointRankOneContribution M W

/-- The endpoint sets differ by exactly the single atom `M`. -/
theorem Icc_eq_insert_Ioc (M : ℕ) :
    Finset.Icc M (2 * M) = insert M (Finset.Ioc M (2 * M)) := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
  omega

theorem leftEndpoint_not_mem_Ioc (M : ℕ) :
    M ∉ Finset.Ioc M (2 * M) := by
  simp

/-- Exact finite decomposition.  No endpoint convention is suppressed. -/
theorem closedRatioSecondMoment_eq_openLeft_add_boundary
    (M : ℕ) (W : Finset ℝ) :
    closedRatioSecondMoment M W =
      openLeftRatioSecondMoment M W +
        leftEndpointBoundaryContribution M W := by
  let A := Finset.Ioc M (2 * M)
  have hM : M ∉ A := by simp [A]
  rw [closedRatioSecondMoment, Icc_eq_insert_Ioc]
  change (∑ n ∈ insert M A, ∑ m ∈ insert M A,
      ratioKernelSquare W n m) = _
  simp only [Finset.sum_insert hM]
  unfold openLeftRatioSecondMoment leftEndpointBoundaryContribution
    leftEndpointCrossContribution leftEndpointRankOneContribution
  change _ =
    (∑ n ∈ A, ∑ m ∈ A, ratioKernelSquare W n m) +
      (((∑ n ∈ A, ratioKernelSquare W M n) +
        ∑ n ∈ A, ratioKernelSquare W n M) +
          ratioKernelSquare W M M)
  rw [Finset.sum_add_distrib]
  ring

/-- A coefficient-one ratio kernel has norm at most the number of ordinates.
This is the sharp pointwise deterministic input for the endpoint bound. -/
theorem norm_ratioDirichletKernel_le_card (W : Finset ℝ) (v : ℝ) :
    ‖ratioDirichletKernel W v‖ ≤ (W.card : ℝ) := by
  unfold ratioDirichletKernel
  calc
    ‖∑ t ∈ W, Complex.exp
        (Complex.I * ((t * Real.log |v| : ℝ) : ℂ))‖ ≤
        ∑ t ∈ W, ‖Complex.exp
          (Complex.I * ((t * Real.log |v| : ℝ) : ℂ))‖ :=
      norm_sum_le _ _
    _ = ∑ _t ∈ W, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Complex.norm_exp]
      simp
    _ = (W.card : ℝ) := by simp

theorem ratioKernelSquare_nonneg (W : Finset ℝ) (n m : ℕ) :
    0 ≤ ratioKernelSquare W n m := by
  exact sq_nonneg _

/-- Every ordered-pair boundary summand retains its exact `W` dependence and
is bounded by `|W|²`. -/
theorem ratioKernelSquare_le_card_sq (W : Finset ℝ) (n m : ℕ) :
    ratioKernelSquare W n m ≤ (W.card : ℝ) ^ 2 := by
  unfold ratioKernelSquare
  have h := norm_ratioDirichletKernel_le_card W ((n : ℝ) / (m : ℝ))
  nlinarith [norm_nonneg
    (ratioDirichletKernel W ((n : ℝ) / (m : ℝ))),
    (show 0 ≤ (W.card : ℝ) from Nat.cast_nonneg W.card)]

/-- At ratio one the coefficient-one kernel is exactly the cardinality of
`W`, so the rank-one atom is exactly `|W|²`. -/
theorem ratioDirichletKernel_one (W : Finset ℝ) :
    ratioDirichletKernel W 1 = (W.card : ℂ) := by
  unfold ratioDirichletKernel
  simp

theorem leftEndpointRankOneContribution_eq_card_sq
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    leftEndpointRankOneContribution M W = (W.card : ℝ) ^ 2 := by
  unfold leftEndpointRankOneContribution ratioKernelSquare
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  rw [div_self hM0, ratioDirichletKernel_one]
  simp

/-- The two cross arms cost at most `2 M |W|²`; the interval `(M,2M]`
contains exactly `M` integers. -/
theorem leftEndpointCrossContribution_le
    (M : ℕ) (W : Finset ℝ) :
    leftEndpointCrossContribution M W ≤
      2 * (M : ℝ) * (W.card : ℝ) ^ 2 := by
  unfold leftEndpointCrossContribution
  calc
    (∑ n ∈ Finset.Ioc M (2 * M), ratioKernelSquare W M n) +
        ∑ n ∈ Finset.Ioc M (2 * M), ratioKernelSquare W n M ≤
      (∑ _n ∈ Finset.Ioc M (2 * M), (W.card : ℝ) ^ 2) +
        ∑ _n ∈ Finset.Ioc M (2 * M), (W.card : ℝ) ^ 2 := by
      apply add_le_add
      · exact Finset.sum_le_sum
          (fun n hn => ratioKernelSquare_le_card_sq W M n)
      · exact Finset.sum_le_sum
          (fun n hn => ratioKernelSquare_le_card_sq W n M)
    _ = 2 * (M : ℝ) * (W.card : ℝ) ^ 2 := by
      have hcard : (Finset.Ioc M (2 * M)).card = M := by
        simp only [Nat.card_Ioc]
        omega
      simp only [Finset.sum_const, nsmul_eq_mul, hcard]
      ring

/-- Fully explicit deterministic endpoint cost. -/
theorem leftEndpointBoundaryContribution_le
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    leftEndpointBoundaryContribution M W ≤
      (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := by
  rw [leftEndpointBoundaryContribution,
    leftEndpointRankOneContribution_eq_card_sq M W hM]
  have hcross := leftEndpointCrossContribution_le M W
  linarith

/-- The closed Heath--Brown block is bounded by the literal Jutila block plus
the explicit endpoint correction. -/
theorem closedRatioSecondMoment_le_openLeft_add_endpointBound
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    closedRatioSecondMoment M W ≤
      openLeftRatioSecondMoment M W +
        (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := by
  rw [closedRatioSecondMoment_eq_openLeft_add_boundary]
  exact add_le_add (le_refl _) (leftEndpointBoundaryContribution_le M W hM)

/-- Conversely, positivity gives the lossless inclusion of the open-left
block into the closed block. -/
theorem openLeftRatioSecondMoment_le_closed
    (M : ℕ) (W : Finset ℝ) :
    openLeftRatioSecondMoment M W ≤ closedRatioSecondMoment M W := by
  rw [closedRatioSecondMoment_eq_openLeft_add_boundary]
  apply le_add_of_nonneg_right
  unfold leftEndpointBoundaryContribution leftEndpointCrossContribution
    leftEndpointRankOneContribution
  exact add_nonneg
    (add_nonneg
      (Finset.sum_nonneg
        (fun n hn => ratioKernelSquare_nonneg W M n))
      (Finset.sum_nonneg
        (fun n hn => ratioKernelSquare_nonneg W n M)))
    (ratioKernelSquare_nonneg W M M)

/-- Source-facing exact adapter from the coefficient-one Heath--Brown
difference quadratic form to Jutila's open-left ratio block. -/
theorem differenceQuadraticForm_one_eq_openLeft_add_boundary
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W =
      openLeftRatioSecondMoment M W +
        leftEndpointBoundaryContribution M W := by
  rw [differenceQuadraticForm_one_eq_ratioKernelSecondMoment M W hM]
  change closedRatioSecondMoment M W = _
  exact closedRatioSecondMoment_eq_openLeft_add_boundary M W

/-- Source-facing quantitative endpoint adapter.  This theorem introduces no
analytic input beyond the existing exact finite ratio-kernel identity. -/
theorem differenceQuadraticForm_one_le_openLeft_add_endpointBound
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    differenceQuadraticForm (fun _ => (1 : ℂ)) M W ≤
      openLeftRatioSecondMoment M W +
        (2 * (M : ℝ) + 1) * (W.card : ℝ) ^ 2 := by
  rw [differenceQuadraticForm_one_eq_openLeft_add_boundary M W hM]
  exact add_le_add (le_refl _) (leftEndpointBoundaryContribution_le M W hM)

end

end GuthMaynardHeathBrownIccIocEndpointAdapter

#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.Icc_eq_insert_Ioc
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.closedRatioSecondMoment_eq_openLeft_add_boundary
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.norm_ratioDirichletKernel_le_card
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.leftEndpointBoundaryContribution_le
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.openLeftRatioSecondMoment_le_closed
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.differenceQuadraticForm_one_eq_openLeft_add_boundary
#print axioms GuthMaynardHeathBrownIccIocEndpointAdapter.differenceQuadraticForm_one_le_openLeft_add_endpointBound
