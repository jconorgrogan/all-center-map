import GuthMaynardProposition46RawTrace
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Guth--Maynard Lemma 4.1 via the literal matrix operator norm
-/
namespace GuthMaynardLemma41Operator

set_option synthInstance.maxHeartbeats 100000

open scoped BigOperators
open GuthMaynardSectionFourTrace

noncomputable section

def sourceMatrixOperator (W : Finset ℝ) (N : ℕ) :
    EuclideanSpace ℂ (SourceColumn N) →L[ℂ] EuclideanSpace ℂ (SourceRow W) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (sourceMatrix W N))

/-- Exact energy inequality behind source Lemma 4.1. -/
theorem source_large_value_energy_le
    (W : Finset ℝ) (N : ℕ) (b : ℕ → ℂ)
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1) :
    (∑ t : SourceRow W, ‖sourceDN b N t‖ ^ 2) ≤
      ‖sourceMatrixOperator W N‖ ^ 2 * (N : ℝ) := by
  let v : EuclideanSpace ℂ (SourceColumn N) :=
    WithLp.toLp 2 (sourceCoefficientVector b N)
  let T := sourceMatrixOperator W N
  have hop : ‖T v‖ ≤ ‖T‖ * ‖v‖ := ContinuousLinearMap.le_opNorm T v
  have hop2 : ‖T v‖ ^ 2 ≤ ‖T‖ ^ 2 * ‖v‖ ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left₀ (norm_nonneg (T v)) hop 2
  have hv : ‖v‖ ^ 2 ≤ (N : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ n : SourceColumn N, ‖b n‖ ^ 2) ≤ (N : ℝ)
    calc
      (∑ n : SourceColumn N, ‖b n‖ ^ 2) ≤ ∑ _n : SourceColumn N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n hn
        simpa using pow_le_pow_left₀ (norm_nonneg _) (hb n n.property) 2
      _ = (Fintype.card (SourceColumn N) : ℝ) := by simp
      _ = (N : ℝ) := by
        norm_cast
        simp [SourceColumn, Nat.card_Ioc]
        omega
  calc
    (∑ t : SourceRow W, ‖sourceDN b N t‖ ^ 2) = ‖T v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro t ht
      congr 1
      dsimp [T, sourceMatrixOperator]
      change ‖sourceDN b N t‖ =
        ‖(sourceMatrix W N).mulVec (sourceCoefficientVector b N) t‖
      exact congrArg norm (sourceMatrix_mulVec_eq_sourceDN W N b t).symm
    _ ≤ ‖T‖ ^ 2 * ‖v‖ ^ 2 := hop2
    _ ≤ ‖T‖ ^ 2 * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hv (sq_nonneg _)

/-- Pointwise largeness converts the energy inequality into the literal
cardinality statement of Lemma 4.1, before rewriting powers. -/
theorem source_large_value_cardinality_mul_le
    (W : Finset ℝ) (N : ℕ) (b : ℕ → ℂ) (L : ℝ)
    (hL : 0 ≤ L)
    (hb : ∀ n ∈ Finset.Ioc N (2 * N), ‖b n‖ ≤ 1)
    (hlarge : ∀ t : SourceRow W, L ≤ ‖sourceDN b N t‖) :
    (W.card : ℝ) * L ^ 2 ≤ ‖sourceMatrixOperator W N‖ ^ 2 * (N : ℝ) := by
  calc
    (W.card : ℝ) * L ^ 2 = ∑ _t : SourceRow W, L ^ 2 := by simp
    _ ≤ ∑ t : SourceRow W, ‖sourceDN b N t‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro t ht
      exact pow_le_pow_left₀ hL (hlarge t) 2
    _ ≤ _ := source_large_value_energy_le W N b hb

end
end GuthMaynardLemma41Operator

#print axioms GuthMaynardLemma41Operator.source_large_value_energy_le
#print axioms GuthMaynardLemma41Operator.source_large_value_cardinality_mul_le
