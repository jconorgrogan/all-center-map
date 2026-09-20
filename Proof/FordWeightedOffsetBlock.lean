import FordHurwitzFirstLeaf
import FordOffsetLogTransfer

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordWeightedOffsetBlock

open FordHurwitz FordOffsetLogTransfer

lemma phase_eq_offsetPhase {u t : ℝ} {n : ℕ} :
    FordHurwitz.phase u t n = offsetPhase t u n := by
  unfold FordHurwitz.phase offsetPhase FordUnitPhaseLipschitz.unitPhase
  congr 1
  push_cast
  ring

/-- Finite Abel summation for the actual offset complex powers.  Cancellation
of every offset-phase prefix is the only oscillatory input. -/
theorem norm_weighted_offset_block_le
    {u σ t B : ℝ} {N H : ℕ}
    (hu : 0 ≤ u) (hσ : 0 ≤ σ) (hN : 2 ≤ N) (hH : H ≤ N)
    (hB : 0 ≤ B)
    (hprefix : ∀ q, q ≤ H →
      ‖∑ n ∈ Finset.range q, offsetPhase t u (N + n)‖ ≤ B) :
    ‖∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-((σ : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      B * (N : ℝ) ^ (-σ) := by
  have hN1 : 1 ≤ N := by omega
  have hcore := FordHurwitz.norm_weighted_range_le_first
    (r := H) (M := B) hB
    (w := fun n : ℕ => (((N + n : ℕ) : ℝ) + u) ^ (-σ))
    (z := fun n : ℕ => FordHurwitz.phase u t (N + n))
    (by intro i; positivity)
    (by
      intro i j hij
      apply Real.rpow_le_rpow_of_nonpos
      · positivity
      · have hn : N + i ≤ N + j := by omega
        have hreal : ((N + i : ℕ) : ℝ) ≤ ((N + j : ℕ) : ℝ) := by
          exact_mod_cast hn
        exact add_le_add hreal (le_refl u)
      · exact neg_nonpos.mpr hσ)
    (by
      intro q hq
      simpa [phase_eq_offsetPhase] using hprefix q hq)
  have hweighted :
      (∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-((σ : ℂ) + Complex.I * (t : ℂ)))) =
      ∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u) ^ (-σ) •
          FordHurwitz.phase u t (N + n) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hnu : 0 < ((N + n : ℕ) : ℝ) + u := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      push_cast
      linarith
    simpa [phase_eq_offsetPhase] using
      (FordHurwitz.cpow_neg_real_add_imag_eq_weight_phase
        (u := u) (σ := σ) (t := t) (n := N + n) hnu)
  rw [hweighted]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbound : ‖∑ n ∈ Finset.range H,
      (((N + n : ℕ) : ℝ) + u) ^ (-σ) •
        FordHurwitz.phase u t (N + n)‖ ≤
      (N : ℝ) ^ (-σ) * B := by
    exact hcore.trans (by
      apply mul_le_mul_of_nonneg_right _ hB
      apply Real.rpow_le_rpow_of_nonpos
      · exact hNpos
      · have hbase : (N : ℝ) ≤ ((N : ℝ) + u) := by linarith
        exact hbase
      · exact neg_nonpos.mpr hσ)
  calc
    _ ≤ (N : ℝ) ^ (-σ) * B := hbound
    _ = B * (N : ℝ) ^ (-σ) := by ring

end FordWeightedOffsetBlock

#print axioms FordWeightedOffsetBlock.phase_eq_offsetPhase
#print axioms FordWeightedOffsetBlock.norm_weighted_offset_block_le
