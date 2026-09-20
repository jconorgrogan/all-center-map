import MRTDynamicD12PerronMassAssembly
import MRTLemma215DynamicTypeIIGlobalCountV3

/-! Exact finite branch/bag bookkeeping for the D12 consumer.

The branch weight is retained as the literal `2 * K`, and the bag count is
the exact `dynamicLowComponentMultiplicityV3`.  This module supplies only the
polylogarithmic counting envelope; it does not bound any analytic component
mass or replace a pointwise coefficient cap.
-/
namespace MRTDynamicD12WeightedMultiplicity

open scoped BigOperators ArithmeticFunction
open ArithmeticFunction
open MAPDynamicHBSourceV3 MAPFinishDynamicThreeTypeTrace
open MAPDynamicHBSourcePacketBoundRefinedV3
open MRTLemma215DyadicPartition MRTLemma215HBExpansion
open MRTLemma215DynamicTypeIIGlobalCountV3

noncomputable section

set_option maxHeartbeats 800000

/-- The exact branch-weighted number of source bags is polylogarithmic. -/
theorem exists_d12_weighted_branch_multiplicity_polylog
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ E : ℕ,
      ∀ {X : ℝ}, 3 ≤ X →
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
              (branch : ℕ) : ℝ)) ≤
          C * Real.log X ^ E := by
  have hK : 1 ≤ hbOrder delta := hbOrder_one hdelta
  let K : ℕ := hbOrder delta
  let C : ℝ := 12 * (K : ℝ) ^ 2 *
    ((6 + K : ℕ) : ℝ) ^ (2 * K)
  refine ⟨C, ?_, 2 * K + 1, ?_⟩
  · dsimp [C]
    have hK0 : 0 < (K : ℝ) := by
      dsimp [K]
      exact_mod_cast (show 0 < hbOrder delta by omega)
    positivity
  · intro X hX
    have hlog : 0 ≤ Real.log X :=
      (log_one_le hX).trans' (by norm_num)
    have hKlt : ∀ (branch : Fin (hbOrder delta)),
        (branch : ℕ) < hbOrder delta := fun branch => branch.isLt
    have hsum :
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
              (branch : ℕ) : ℝ)) ≤
          ∑ branch : Fin (hbOrder delta),
            (2 * (K : ℝ)) *
              (6 * ((6 + K : ℕ) : ℝ) ^ (2 * K) *
                Real.log X ^ (2 * K + 1)) := by
      apply Finset.sum_le_sum
      intro branch hbranch
      have hm := dynamicLowComponentMultiplicity_le_polylog hX
        (hKlt branch)
      have hw : dynamicBranchLowWeightRefinedV3
          (K := hbOrder delta) = 2 * (K : ℝ) := by
        dsimp [dynamicBranchLowWeightRefinedV3, K]
      rw [hw]
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    calc
      _ ≤ ∑ branch : Fin (hbOrder delta),
          (2 * (K : ℝ)) *
            (6 * ((6 + K : ℕ) : ℝ) ^ (2 * K) *
              Real.log X ^ (2 * K + 1)) := hsum
      _ = C * Real.log X ^ (2 * K + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        dsimp [C]
        ring

/-- The same envelope after retaining an arbitrary nonnegative per-bag
coefficient.  This is the form consumed after the exact Perron/bag sum. -/
theorem d12_weighted_branch_multiplicity_mul_nonneg
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ C : ℝ, 0 < C ∧ ∃ E : ℕ,
      ∀ {X M : ℝ}, 3 ≤ X → 0 ≤ M →
        (∑ branch : Fin (hbOrder delta),
          dynamicBranchLowWeightRefinedV3 (K := hbOrder delta) *
            (dynamicLowComponentMultiplicityV3 X (hbOrder delta)
              (branch : ℕ) : ℝ) * M) ≤
          C * Real.log X ^ E * M := by
  obtain ⟨C, hC, E, hcount⟩ :=
    exists_d12_weighted_branch_multiplicity_polylog delta hdelta
  refine ⟨C, hC, E, ?_⟩
  intro X M hX hM
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (hcount hX) hM

end
end MRTDynamicD12WeightedMultiplicity

#print axioms MRTDynamicD12WeightedMultiplicity.exists_d12_weighted_branch_multiplicity_polylog
#print axioms MRTDynamicD12WeightedMultiplicity.d12_weighted_branch_multiplicity_mul_nonneg
