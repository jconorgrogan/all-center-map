import GuthMaynardGMSourceKusminActual

namespace GuthMaynardGMSourceKusminSmallT

open scoped BigOperators
open GuthMaynardSectionFourTrace
open GuthMaynardGMPointwiseHighTPartition
open GuthMaynardGMSourceKusminActual

noncomputable section

theorem sourcePhase_Ioc_eq_shifted_range
    (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N), sourcePhase n t) =
      ∑ m ∈ Finset.range N, sourcePhase (N + 1 + m) t := by
  apply Finset.sum_bij (fun n _ => n - (N + 1))
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    exact Finset.mem_range.mpr (by omega)
  · intro a ha b hb hab
    have ha' := Finset.mem_Ioc.mp ha
    have hb' := Finset.mem_Ioc.mp hb
    omega
  · intro m hm
    have hm' := Finset.mem_range.mp hm
    refine ⟨N + 1 + m, ?_, ?_⟩
    · apply Finset.mem_Ioc.mpr
      constructor <;> omega
    · omega
  · intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    congr 1
    omega

theorem log_one_add_inv_twoN_lower
    {N : ℕ} (hN : 1 ≤ N) :
    1 / ((2 * (N : ℝ)) + 1) ≤ Real.log (1 + 1 / (2 * (N : ℝ))) := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hx : 0 < 1 + 1 / (2 * (N : ℝ)) := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hx
  have halg : 1 / ((2 * (N : ℝ)) + 1) ≤
      1 - (1 + 1 / (2 * (N : ℝ)))⁻¹ := by
    field_simp
    ring_nf
    nlinarith [hNpos]
  exact halg.trans hlog

theorem norm_sum_sourcePhase_Ioc_le_pi_N_div_t
    {N : ℕ} {t : ℝ} (hN : 1 ≤ N) (ht : 0 < t) (htN : t ≤ N) :
    ‖∑ n ∈ Finset.Ioc N (2 * N), sourcePhase n t‖ ≤
      9 * Real.pi * N / t := by
  have hNpos : 0 < N := by omega
  have hshift := norm_sum_sourcePhase_small_t (N + 1) (N - 1) t
    (by omega) ht (by
      have hNr : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by norm_num
      exact htN.trans hNr)
  rw [sourcePhase_Ioc_eq_shifted_range N t]
  have hshift' : ‖∑ m ∈ Finset.range N, sourcePhase (N + 1 + m) t‖ ≤
      3 * Real.pi / gmIncrement t (2 * N) := by
    have hlen : N - 1 + 1 = N := by omega
    have hend : N + 1 + (N - 1) = 2 * N := by omega
    simpa [hlen, hend, Nat.add_assoc] using hshift
  have hinc : 0 < gmIncrement t (2 * N) := by
    unfold gmIncrement
    have h2N : 0 < (2 * N : ℕ) := by omega
    have h2Nr : 0 < (2 * (N : ℝ)) := by positivity
    have h2Ncast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by norm_num
    rw [h2Ncast]
    apply mul_pos ht
    apply Real.log_pos
    have : 0 < 1 / (2 * (N : ℝ)) := one_div_pos.mpr h2Nr
    linarith
  have hlog := log_one_add_inv_twoN_lower hN
  have hlog' : t / (3 * (N : ℝ)) ≤ gmIncrement t (2 * N) := by
    unfold gmIncrement
    have h2Ncast : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by norm_num
    rw [h2Ncast]
    have hNrealpos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hNreal : (N : ℝ) ≤ 2 * (N : ℝ) + 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hlog ht.le
    have hbase : t / (3 * (N : ℝ)) ≤ t / (2 * (N : ℝ) + 1) := by
      apply (div_le_div_iff_of_pos_left ht (by positivity) (by positivity)).2
      nlinarith [hNrealpos]
    have hden : t / (2 * (N : ℝ) + 1) ≤
        t * Real.log (1 + 1 / (2 * (N : ℝ))) := by
      simpa [Nat.cast_mul, div_eq_mul_inv] using hmul
    exact hbase.trans hden
  have hfactor : 0 ≤ 9 * Real.pi * (N : ℝ) / t := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog' hfactor
  have htarget : 3 * Real.pi ≤
      (9 * Real.pi * (N : ℝ) / t) * gmIncrement t (2 * N) := by
    calc
      3 * Real.pi = (9 * Real.pi * (N : ℝ) / t) *
          (t / (3 * (N : ℝ))) := by field_simp; ring
      _ ≤ (9 * Real.pi * (N : ℝ) / t) * gmIncrement t (2 * N) := hmul
  have hfinal : 3 * Real.pi / gmIncrement t (2 * N) ≤
      9 * Real.pi * (N : ℝ) / t := by
    apply (div_le_iff₀ hinc).2
    exact htarget
  exact hshift'.trans hfinal

theorem norm_gmDyadicKernel_le_nine_pi_N_div_t
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) (htN : t ≤ N) :
    ‖GuthMaynardGMPointwiseKernel.gmDyadicKernel N t‖ ≤
      9 * Real.pi * N / t := by
  unfold GuthMaynardGMPointwiseKernel.gmDyadicKernel
  exact norm_sum_sourcePhase_Ioc_le_pi_N_div_t hN ht htN

end
end GuthMaynardGMSourceKusminSmallT

#print axioms GuthMaynardGMSourceKusminSmallT.norm_sum_sourcePhase_Ioc_le_pi_N_div_t
