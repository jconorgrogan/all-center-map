import GuthMaynardGMOffBandPartition

namespace GuthMaynardGMPartitionSum
open GuthMaynardGMOffBandPartition GuthMaynardGMPointwiseHighTPartition
open GuthMaynardGMPointwiseKernel GuthMaynardSectionFourTrace
open scoped BigOperators
noncomputable section

theorem norm_sum_offResonant_le {N : ℕ} {t δ A : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) (hδ : 0 < δ)
    (hband : ∀ ell ∈ gmBandLabels N t,
      ‖∑ n ∈ gmOffBand N t δ ell, sourcePhase n t‖ ≤ A) :
    ‖∑ n ∈ gmOffResonant N t δ, sourcePhase n t‖ ≤
      (gmBandLabels N t).card * A := by
  classical
  rw [gmOffResonant_eq_biUnion hN ht hδ, Finset.sum_biUnion]
  · calc
      _ ≤ ∑ ell ∈ gmBandLabels N t, ‖∑ n ∈ gmOffBand N t δ ell, sourcePhase n t‖ :=
        norm_sum_le _ _
      _ ≤ ∑ ell ∈ gmBandLabels N t, A := Finset.sum_le_sum hband
      _ = _ := by simp
  · intro a ha b hb hab
    exact gmOffBand_disjoint hδ hab

theorem norm_kernel_le_partition {N : ℕ} {t δ A : ℝ} (hN : 1 ≤ N)
    (ht : 0 < t) (hδ : 0 < δ)
    (hband : ∀ ell ∈ gmBandLabels N t,
      ‖∑ n ∈ gmOffBand N t δ ell, sourcePhase n t‖ ≤ A) :
    ‖gmDyadicKernel N t‖ ≤ (gmResonant N t δ).card +
      (gmBandLabels N t).card * A := by
  classical
  have hd : Disjoint (gmResonant N t δ) (gmOffResonant N t δ) := by
    rw [Finset.disjoint_left]
    intro n hr ho
    exact (Finset.mem_filter.mp ho).2 (Finset.mem_filter.mp hr).2
  have hres : ‖∑ n ∈ gmResonant N t δ, sourcePhase n t‖ ≤ (gmResonant N t δ).card := by
    calc
      _ ≤ ∑ n ∈ gmResonant N t δ, ‖sourcePhase n t‖ := norm_sum_le _ _
      _ = _ := by
        have hu : ∀ n, ‖sourcePhase n t‖ = 1 := by
          intro n
          unfold sourcePhase
          simpa [mul_comm] using Complex.norm_exp_ofReal_mul_I (t * Real.log n)
        simp [hu]
  unfold gmDyadicKernel
  rw [← gm_resonant_union_offResonant N t δ, Finset.sum_union hd]
  exact (norm_add_le _ _).trans (add_le_add hres (norm_sum_offResonant_le hN ht hδ hband))

end
end GuthMaynardGMPartitionSum
#print axioms GuthMaynardGMPartitionSum.norm_kernel_le_partition
