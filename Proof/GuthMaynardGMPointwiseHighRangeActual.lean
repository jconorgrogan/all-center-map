import GuthMaynardGMOffBandPerBand
import GuthMaynardGMPartitionSum
import GuthMaynardGMResonanceScalar

namespace GuthMaynardGMPointwiseHighRangeActual
open GuthMaynardGMPointwiseHighTPartition GuthMaynardGMPointwiseKernel
open GuthMaynardGMPartitionSum GuthMaynardGMOffBandPerBand GuthMaynardGMResonanceScalar

/-- Literal discrete high range; neither a kernel nor a band estimate is assumed. -/
theorem norm_kernel_high_range {N : ℕ} {t : ℝ} (hN : 1 ≤ N)
    (hNt : (N : ℝ) ≤ t) (htN : t ≤ (N : ℝ) ^ 2) :
    ‖gmDyadicKernel N t‖ ≤ 300 * Real.sqrt t := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have ht : 0 < t := lt_of_lt_of_le hNR hNt
  have hδ : 0 < Real.sqrt t / (N : ℝ) := by positivity
  have hδ1 : Real.sqrt t / (N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNR).2
    simpa using (Real.sqrt_le_left hNR.le).2 htN
  have hmain := norm_kernel_le_partition hN ht hδ
    (fun ell _ => norm_sum_gmOffBand_sourcePhase (ell := ell) hN ht hδ)
  have hcount := gmResonant_card_le_bandLabels hN hNt htN hδ hδ1
  have hratio : 2 * (Real.sqrt t / (N : ℝ)) / (t / (9 * (N : ℝ) ^ 2)) =
      18 * (Real.sqrt t / (N : ℝ)) * (N : ℝ) ^ 2 / t := by field_simp; ring
  rw [hratio] at hcount
  apply high_range_scalar hNR hNt htN (bandLabels_card_le_eight_t_div_N hN hNt)
  calc
    ‖gmDyadicKernel N t‖ ≤
        (gmResonant N t (Real.sqrt t / N)).card +
          (gmBandLabels N t).card * (3 * Real.pi / (Real.sqrt t / N)) := hmain
    _ ≤ (gmBandLabels N t).card *
        (1 + 18 * (Real.sqrt t / (N : ℝ)) * (N : ℝ) ^ 2 / t) +
          (gmBandLabels N t).card * (3 * Real.pi / (Real.sqrt t / N)) :=
      by linarith only [hcount]
    _ = _ := by ring

end GuthMaynardGMPointwiseHighRangeActual
#print axioms GuthMaynardGMPointwiseHighRangeActual.norm_kernel_high_range
