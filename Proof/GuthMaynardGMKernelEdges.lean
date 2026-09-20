import GuthMaynardGMPointwiseKernel

open scoped BigOperators ComplexConjugate
noncomputable section
namespace GuthMaynardGMKernelEdges
open GuthMaynardGMPointwiseKernel

theorem sourcePhase_neg (n : ℕ) (t : ℝ) :
    GuthMaynardSectionFourTrace.sourcePhase n (-t) =
      conj (GuthMaynardSectionFourTrace.sourcePhase n t) := by
  unfold GuthMaynardSectionFourTrace.sourcePhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.ofReal_neg]
  ring

theorem gmDyadicKernel_neg (N : ℕ) (t : ℝ) :
    gmDyadicKernel N (-t) = conj (gmDyadicKernel N t) := by
  simp only [gmDyadicKernel, map_sum, sourcePhase_neg]

theorem norm_gmDyadicKernel_neg (N : ℕ) (t : ℝ) :
    ‖gmDyadicKernel N (-t)‖ = ‖gmDyadicKernel N t‖ := by
  rw [gmDyadicKernel_neg, Complex.norm_conj]

theorem norm_gmDyadicKernel_le_shape_of_sq_le_abs
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : (N : ℝ) ^ 2 ≤ |t|) :
    ‖gmDyadicKernel N t‖ ≤
      (N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ) := by
  have hroot : (N : ℝ) ≤ Real.sqrt |t| := by
    exact (Real.le_sqrt (by positivity) (abs_nonneg t)).2 ht
  have hraw := norm_gmDyadicKernel_le_card hN t
  have hfrac : 0 ≤ (N : ℝ) / (1 + |t|) := by positivity
  linarith [Real.sqrt_nonneg (N : ℝ)]

end GuthMaynardGMKernelEdges
#print axioms GuthMaynardGMKernelEdges.sourcePhase_neg
#print axioms GuthMaynardGMKernelEdges.norm_gmDyadicKernel_le_shape_of_sq_le_abs
