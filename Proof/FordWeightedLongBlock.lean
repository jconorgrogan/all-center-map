import FordLongBlockOffsetBound
import FordWeightedOffsetBlock

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordWeightedLongBlock

/-- A bounded long block with the real decay weight attached to Ford's phase. -/
theorem norm_weighted_long_block
    {N H : ℕ} (hN : 2 ≤ N) (hH : H ≤ N)
    {t u eta : ℝ} (ht : 0 < t) (htN : t ≤ (N : ℝ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1) :
    ‖∑ n ∈ Finset.range H,
        (((N + n : ℕ) : ℝ) + u : ℂ) ^
          (-(((1 - eta : ℝ) : ℂ) + Complex.I * (t : ℂ)))‖ ≤
      12 * Real.pi * (N : ℝ) ^ eta / t := by
  have hσ : 0 ≤ 1 - eta := by linarith
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hB : 0 ≤ 12 * Real.pi * (N : ℝ) / t := by
    positivity
  have hprefix : ∀ q, q ≤ H →
      ‖∑ n ∈ Finset.range q, FordOffsetLogTransfer.offsetPhase t u (N + n)‖ ≤
        12 * Real.pi * (N : ℝ) / t := by
    intro q hq
    exact FordLongBlockOffsetBound.long_block_offset_bound
      hN (le_trans hq hH) ht htN hu0 hu1
  have hweighted := FordWeightedOffsetBlock.norm_weighted_offset_block_le
    (u := u) (σ := 1 - eta) (t := t)
    (B := 12 * Real.pi * (N : ℝ) / t)
    (N := N) (H := H) hu0 hσ hN hH hB hprefix
  have hpow :
      (N : ℝ) * (N : ℝ) ^ (-(1 - eta)) = (N : ℝ) ^ eta := by
    calc
      (N : ℝ) * (N : ℝ) ^ (-(1 - eta)) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-(1 - eta)) := by
            rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((1 : ℝ) + (-(1 - eta))) :=
        (Real.rpow_add hNpos _ _).symm
      _ = (N : ℝ) ^ eta := by ring_nf
  calc
    _ ≤ (12 * Real.pi * (N : ℝ) / t) *
        (N : ℝ) ^ (-(1 - eta)) := hweighted
    _ = (12 * Real.pi / t) *
        ((N : ℝ) * (N : ℝ) ^ (-(1 - eta))) := by ring
    _ = (12 * Real.pi / t) * (N : ℝ) ^ eta := by rw [hpow]
    _ = 12 * Real.pi * (N : ℝ) ^ eta / t := by ring

end FordWeightedLongBlock

#print axioms FordWeightedLongBlock.norm_weighted_long_block
