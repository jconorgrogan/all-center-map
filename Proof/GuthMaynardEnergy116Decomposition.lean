import GuthMaynardLemma116ClassAlgebra
import GuthMaynardRatioKernelIdentity
import GuthMaynardJIterationDeterministic

open scoped BigOperators Real
open GuthMaynardLemma116
open GuthMaynardRatioKernelIdentity
open GuthMaynardJIteration
open Set

noncomputable section
set_option maxHeartbeats 1600000
namespace GuthMaynardEnergy116Decomposition

/-- The phase attached to an ordered pair of ordinates.  Keeping the product
with the conjugate phase explicit makes the fourth-moment identity exact. -/
def pairDifferencePhase (W : Finset ℝ) (v : ℝ)
    (p : ℝ × ℝ) : ℂ :=
  Complex.exp (Complex.I * (((p.1 * Real.log |v| : ℝ) : ℂ))) *
    star (Complex.exp (Complex.I * (((p.2 * Real.log |v| : ℝ) : ℂ))))

def pairDifferenceField (W : Finset ℝ) (v : ℝ) : ℂ :=
  ∑ p ∈ W.product W, pairDifferencePhase W v p

def activePairClass (W : Finset ℝ) (j : ℕ) : Finset (ℝ × ℝ) :=
  (W.product W).filter fun p =>
    Nat.log2 (floorDifferenceMultiplicity W (floorDifference p)) = j

def groupedDifferenceField (W : Finset ℝ) (j : ℕ) (v : ℝ) : ℂ :=
  ∑ p ∈ activePairClass W j, pairDifferencePhase W v p

def activeDyadicExponents116 (W : Finset ℝ) : Finset ℕ :=
  (floorDifferenceBins W).filter
      (fun u => floorDifferenceMultiplicity W u ≠ 0) |>.image
        (fun u => Nat.log2 (floorDifferenceMultiplicity W u))

/-- A grouped field is a sum of unit phases, hence its norm is bounded by the
number of ordered pairs in that active class. -/
theorem groupedDifferenceField_norm_le_card
    (W : Finset ℝ) (j : ℕ) (v : ℝ) :
    ‖groupedDifferenceField W j v‖ ≤ (activePairClass W j).card := by
  calc
    ‖groupedDifferenceField W j v‖ ≤
        ∑ p ∈ activePairClass W j, ‖pairDifferencePhase W v p‖ := by
      exact norm_sum_le _ _
    _ = ∑ _p ∈ activePairClass W j, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [pairDifferencePhase, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        norm_star]
      norm_num
    _ = (activePairClass W j).card := by simp

theorem groupedDifferenceField_sq_norm_le_card_sq
    (W : Finset ℝ) (j : ℕ) (v : ℝ) :
    ‖groupedDifferenceField W j v‖ ^ 2 ≤
      ((activePairClass W j).card : ℝ) ^ 2 := by
  have h := groupedDifferenceField_norm_le_card W j v
  nlinarith [norm_nonneg (groupedDifferenceField W j v)]

/-- The pair phase is the exact product of the two ratio-kernel phases. -/
theorem pairDifferenceField_eq_ratio_mul_star (W : Finset ℝ) (v : ℝ) :
    pairDifferenceField W v =
      ratioDirichletKernel W v * star (ratioDirichletKernel W v) := by
  unfold pairDifferenceField pairDifferencePhase ratioDirichletKernel
  calc
    (∑ p ∈ W.product W,
        Complex.exp (Complex.I * (((p.1 * Real.log |v| : ℝ) : ℂ))) *
          star (Complex.exp (Complex.I * (((p.2 * Real.log |v| : ℝ) : ℂ))))) =
      ∑ p ∈ W, ∑ q ∈ W,
        Complex.exp (Complex.I * (((p * Real.log |v| : ℝ) : ℂ))) *
          star (Complex.exp (Complex.I * (((q * Real.log |v| : ℝ) : ℂ)))) := by
            exact Finset.sum_product W W (fun p : ℝ × ℝ =>
              Complex.exp (Complex.I * (((p.1 * Real.log |v| : ℝ) : ℂ))) *
                star (Complex.exp (Complex.I * (((p.2 * Real.log |v| : ℝ) : ℂ)))))
    _ = _ := by
      rw [← Finset.sum_mul_sum]
      rw [star_sum]

/-- The fourth power of the ratio kernel is the squared norm of the pair field. -/
theorem ratioKernel_fourth_eq_pairDifferenceField_sq
    (W : Finset ℝ) (v : ℝ) :
    ‖ratioDirichletKernel W v‖ ^ 4 = ‖pairDifferenceField W v‖ ^ 2 := by
  rw [pairDifferenceField_eq_ratio_mul_star]
  rw [norm_mul, norm_star]
  ring

private theorem floorDifferenceMultiplicity_pos_of_mem
    {W : Finset ℝ} {p : ℝ × ℝ} (hp : p ∈ W.product W) :
    floorDifferenceMultiplicity W (floorDifference p) ≠ 0 := by
  unfold floorDifferenceMultiplicity
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

private theorem activePairClass_disjoint (W : Finset ℝ) :
    (activeDyadicExponents116 W : Set ℕ).PairwiseDisjoint
      (activePairClass W) := by
  intro j hj k hk hne
  change Disjoint (activePairClass W j) (activePairClass W k)
  rw [Finset.disjoint_left]
  intro p hpj hpk
  have hj' := (Finset.mem_filter.mp hpj).2
  have hk' := (Finset.mem_filter.mp hpk).2
  exact hne (hj'.symm.trans hk')

private theorem activePairClass_biUnion_eq_pairProduct (W : Finset ℝ) :
    (activeDyadicExponents116 W).biUnion (activePairClass W) =
      W.product W := by
  apply Finset.Subset.antisymm
  · intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_filter.mp hpj).1
  · intro p hp
    have hr := floorDifferenceMultiplicity_pos_of_mem hp
    have hu : floorDifference p ∈ floorDifferenceBins W := by
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hj : Nat.log2 (floorDifferenceMultiplicity W (floorDifference p)) ∈
        activeDyadicExponents116 W :=
      by
        unfold activeDyadicExponents116
        exact Finset.mem_image.mpr ⟨floorDifference p,
          Finset.mem_filter.mpr ⟨hu, hr⟩, rfl⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨Nat.log2 (floorDifferenceMultiplicity W (floorDifference p)), hj, ?_⟩
    exact Finset.mem_filter.mpr ⟨hp, rfl⟩

/-- Exact partition of all ordered difference phases by the active binary
multiplicity classes.  No multiplicity or ordered pair is discarded. -/
theorem pairDifferenceField_eq_sum_grouped
    (W : Finset ℝ) (v : ℝ) :
    pairDifferenceField W v =
      ∑ j ∈ activeDyadicExponents116 W, groupedDifferenceField W j v := by
  unfold pairDifferenceField groupedDifferenceField
  rw [← activePairClass_biUnion_eq_pairProduct W]
  rw [Finset.sum_biUnion (activePairClass_disjoint W)]

/-- The requested finite Cauchy decomposition on the literal dyadic interval.
The remaining local estimate is deliberately not hidden here: it is a bound on
one grouped field after the `|shift| ≤ 1` replacement. -/
theorem ratioKernel_fourth_le_active_grouped
    (W : Finset ℝ) (v : ℝ) :
    ‖ratioDirichletKernel W v‖ ^ 4 ≤
      ((activeDyadicExponents116 W).card : ℝ) *
        ∑ j ∈ activeDyadicExponents116 W,
          ‖groupedDifferenceField W j v‖ ^ 2 := by
  have hpart := pairDifferenceField_eq_sum_grouped W v
  rw [ratioKernel_fourth_eq_pairDifferenceField_sq W v, hpart]
  exact norm_finset_sum_sq_le_card_mul_sum_norm_sq
    (activeDyadicExponents116 W)
    (fun j => groupedDifferenceField W j v)

/- The same finite Cauchy decomposition summed over the closed dyadic block
`[M,2M]`.  This is only a finite rearrangement; no local Heath--Brown bound
is asserted. -/
theorem ratioKernel_fourth_Icc_sum_le_active_grouped
    (M : ℕ) (W : Finset ℝ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc M (2 * M),
      ∑ m ∈ Finset.Icc M (2 * M),
      ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 4) ≤
      ((activeDyadicExponents116 W).card : ℝ) *
        ∑ n ∈ Finset.Icc M (2 * M),
          ∑ m ∈ Finset.Icc M (2 * M),
            ∑ j ∈ activeDyadicExponents116 W,
              ‖groupedDifferenceField W j ((n : ℝ) / (m : ℝ))‖ ^ 2 := by
  let K : ℝ := (activeDyadicExponents116 W).card
  have hpoint (n m : ℕ)
      (hn : n ∈ Finset.Icc M (2 * M))
      (hm : m ∈ Finset.Icc M (2 * M)) :
      ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 4 ≤
        K * ∑ j ∈ activeDyadicExponents116 W,
          ‖groupedDifferenceField W j ((n : ℝ) / (m : ℝ))‖ ^ 2 := by
    dsimp [K]
    exact ratioKernel_fourth_le_active_grouped W ((n : ℝ) / (m : ℝ))
  calc
    (∑ n ∈ Finset.Icc M (2 * M),
        ∑ m ∈ Finset.Icc M (2 * M),
          ‖ratioDirichletKernel W ((n : ℝ) / (m : ℝ))‖ ^ 4) ≤
        ∑ n ∈ Finset.Icc M (2 * M),
          ∑ m ∈ Finset.Icc M (2 * M),
            (K * ∑ j ∈ activeDyadicExponents116 W,
              ‖groupedDifferenceField W j ((n : ℝ) / (m : ℝ))‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro m hm
      exact hpoint n m hn hm
    _ = K * ∑ n ∈ Finset.Icc M (2 * M),
          ∑ m ∈ Finset.Icc M (2 * M),
            ∑ j ∈ activeDyadicExponents116 W,
              ‖groupedDifferenceField W j ((n : ℝ) / (m : ℝ))‖ ^ 2 := by
      simp only [Finset.mul_sum]

end GuthMaynardEnergy116Decomposition

#print axioms GuthMaynardEnergy116Decomposition.ratioKernel_fourth_le_active_grouped
#print axioms GuthMaynardEnergy116Decomposition.ratioKernel_fourth_Icc_sum_le_active_grouped
#print axioms GuthMaynardEnergy116Decomposition.pairDifferenceField_eq_sum_grouped
