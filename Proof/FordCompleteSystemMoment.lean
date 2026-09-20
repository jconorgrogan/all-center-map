import Mathlib

/-! Literal complete-system Vinogradov count and its unconditional total-count
regime. No growing-degree mean-value estimate is assumed or asserted. -/
namespace MAPFordCompleteSystemMoment
noncomputable section
open Finset

/-- Ordered pairs of s-tuples from {1,...,P}, matching every power 1,...,k. -/
def completeMoment (s k P : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun xy : (Fin s → Fin P) × (Fin s → Fin P) =>
    ∀ j ∈ Finset.Icc 1 k,
      (∑ i : Fin s, ((xy.1 i).val + 1) ^ j) =
        ∑ i : Fin s, ((xy.2 i).val + 1) ^ j)).card

theorem completeMoment_le_total (s k P : ℕ) : completeMoment s k P ≤ P ^ (2*s) := by
  classical
  unfold completeMoment
  calc
    _ ≤ (Finset.univ : Finset ((Fin s → Fin P) × (Fin s → Fin P))).card := by
      apply Finset.card_le_card
      intro xy hxy
      exact Finset.mem_univ xy
    _ = P ^ (2*s) := by simp [two_mul, pow_add]

/-- Power of P removed from the trivial 2s moment in Ford Theorem 3's k≥200 row. -/
def sourceLoss (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 2 - 0.001 * (k : ℝ)^2

/-- Exponent of the degree-dependent prefactor in the same source row. -/
def sourcePrefactorExponent (k : ℕ) : ℝ := 2.3291 * (k : ℝ)^3

/-- Every count satisfies the printed bound when its prefactor already absorbs
the full saving in P. This is not the unproved complete-system mean-value theorem. -/
theorem completeMoment_le_source_of_prefactor_dominates
    (s k P : ℕ) (hk : 1 ≤ k) (hP : 1 ≤ P)
    (htrivial : sourceLoss k * Real.log P ≤ sourcePrefactorExponent k * Real.log k) :
    (completeMoment s k P : ℝ) ≤ Real.rpow k (sourcePrefactorExponent k) *
      Real.rpow P (2*(s : ℝ) - sourceLoss k) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hk)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) hP)
  have hc : (completeMoment s k P : ℝ) ≤ (P : ℝ) ^ (2*s) := by
    exact_mod_cast completeMoment_le_total s k P
  refine hc.trans ?_
  change (P : ℝ) ^ (2*s) ≤ (k : ℝ) ^ (sourcePrefactorExponent k) *
    (P : ℝ) ^ (2*(s : ℝ)-sourceLoss k)
  rw [← Real.rpow_natCast (P : ℝ) (2*s), Real.rpow_def_of_pos hPpos,
    Real.rpow_def_of_pos hkpos, Real.rpow_def_of_pos hPpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  nlinarith

end
end MAPFordCompleteSystemMoment
#print axioms MAPFordCompleteSystemMoment.completeMoment_le_source_of_prefactor_dominates
