import FordLogPhaseLeafBound
import FordOffsetLogTransfer
import FordUnitPhaseSign

open scoped BigOperators ComplexConjugate
noncomputable section
namespace FordLongBlockOffsetBound

open FordLogPhaseLeafBound FordMixedKernelBounds FordMixedLogEndpointMargins
open FordOffsetLogTransfer FordUnitPhaseSign FordUnitPhaseLipschitz
open FordPhaseDifferencing

/-- A direct long-block estimate, using only the explicit endpoint margin. -/
theorem long_block_offset_bound
    {N H : ℕ} (hN : 2 ≤ N) (hH : H ≤ N)
    {t u : ℝ} (ht : 0 < t) (htN : t ≤ (N : ℝ))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ ≤
      12 * Real.pi * (N : ℝ) / t := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hx : 0 < (N : ℝ) + u := by linarith
  have hdelta : 0 < t / (4 * (N : ℝ)) := by positivity
  have hcollar : (N : ℝ) + u + H + 1 ≤ 4 * (N : ℝ) := by
    have hHr : (H : ℝ) ≤ (N : ℝ) := by exact_mod_cast hH
    linarith
  have hdelta_lo : t / (4 * (N : ℝ)) ≤
      t * endpointCoeff ([] : List ℝ) /
        ((N : ℝ) + u + H + 1 + shiftSum ([] : List ℝ)) ^
          (([] : List ℝ).length + 1) := by
    simp [endpointCoeff, riseCoeff, shiftProd, shiftSum, List.length_nil]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    exact mul_le_mul_of_nonneg_left hcollar ht.le
  have hratio : t / ((N : ℝ) + u) ≤ 1 := by
    apply (div_le_iff₀ hx).2
    linarith
  have hdelta_quarter : t / (4 * (N : ℝ)) ≤ (1 : ℝ) / 4 := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith
  have hdelta_hi :
      t * endpointCoeff ([] : List ℝ) /
        ((N : ℝ) + u) ^ (([] : List ℝ).length + 1) ≤
      2 * Real.pi - t / (4 * (N : ℝ)) := by
    simp [endpointCoeff, riseCoeff, shiftProd, List.length_nil]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    nlinarith
  have hleaf := FordLogPhaseLeafBound.norm_sum_phaseDiff_le
    ([] : List ℝ) (by simp) ht.le hx hdelta H
    hdelta_lo hdelta_hi
  have hphase :
      ‖∑ n ∈ Finset.range H,
        phaseDiff ([] : List ℝ)
          (fun y : ℝ => t * Real.log y) ((N : ℝ) + u + (n : ℝ))‖ ≤
      12 * Real.pi * (N : ℝ) / t := by
    convert hleaf using 1 <;> simp [div_eq_mul_inv, inv_inv] <;> ring
  have hsign := FordUnitPhaseSign.norm_sum_unitPhase_sign
    (s := Finset.range H)
    (a := fun n : ℕ => t * Real.log (((N + n : ℕ) : ℝ) + u)) 1
  calc
    ‖∑ n ∈ Finset.range H, offsetPhase t u (N + n)‖ =
        ‖∑ n ∈ Finset.range H,
          unitPhase (t * Real.log (((N + n : ℕ) : ℝ) + u))‖ := by
      simpa [offsetPhase] using hsign
    _ = ‖∑ n ∈ Finset.range H,
        phaseDiff ([] : List ℝ)
          (fun y : ℝ => t * Real.log y) ((N : ℝ) + u + (n : ℝ))‖ := by
      apply congrArg norm
      apply Finset.sum_congr rfl
      intro n hn
      simp [phaseDiff]
      congr 2
      push_cast
      ring
    _ ≤ 12 * Real.pi * (N : ℝ) / t := hphase

end FordLongBlockOffsetBound

#print axioms FordLongBlockOffsetBound.long_block_offset_bound
