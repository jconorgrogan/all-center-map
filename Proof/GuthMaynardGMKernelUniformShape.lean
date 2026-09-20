import GuthMaynardGMKernelEdges
import GuthMaynardGMSourceKusminSmallT
import GuthMaynardGMPointwiseHighRangeActual
import GuthMaynardGMKernelCorrelation

namespace GuthMaynardGMKernelUniformShape

open GuthMaynardGMPointwiseKernel
open GuthMaynardGMKernelEdges
open GuthMaynardGMSourceKusminSmallT

noncomputable section

theorem norm_gmDyadicKernel_uniform_shape
    (Ch : ℝ)
    (hHigh : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 2 →
        ‖gmDyadicKernel N t‖ ≤ Ch * Real.sqrt t) :
    ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      ‖GuthMaynardGMPointwiseKernel.gmDyadicKernel N t‖ ≤
        max Ch (18 * Real.pi) *
          ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ)) := by
  let C : ℝ := max Ch (18 * Real.pi)
  have hCCh : Ch ≤ C := le_max_left _ _
  have hC18 : 18 * Real.pi ≤ C := le_max_right _ _
  have hC1 : 1 ≤ C := by nlinarith [Real.pi_gt_three]
  have hC2 : 2 ≤ C := by nlinarith [Real.pi_gt_three]
  have hCpos : 0 < C := by nlinarith [hC2]
  have hpos : ∀ N : ℕ, 1 ≤ N → ∀ s : ℝ, 0 ≤ s →
      ‖gmDyadicKernel N s‖ ≤ C *
        ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := by
    intro N hN s hs
    have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    by_cases hsmall : s ≤ 1
    · have hraw := norm_gmDyadicKernel_le_card hN s
      have hbase : (N : ℝ) / 2 ≤ (N : ℝ) / (1 + s) := by
        apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) (by positivity)).2
        nlinarith
      have hsum : 0 ≤ (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by positivity
      have hscale : (N : ℝ) ≤ C *
          ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := by
          have hB : (N : ℝ) / 2 ≤
              (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by
            nlinarith [hbase, Real.sqrt_nonneg s, Real.sqrt_nonneg (N : ℝ)]
          have hmul := mul_le_mul_of_nonneg_left hB hCpos.le
          nlinarith [hmul]
      exact hraw.trans hscale
    · have hs1 : 1 ≤ s := le_of_not_ge hsmall
      have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs1
      by_cases hSN : s ≤ (N : ℝ)
      · have hsmall' := norm_gmDyadicKernel_le_nine_pi_N_div_t hN hs0 hSN
        have hratio : 9 * Real.pi * (N : ℝ) / s ≤
            18 * Real.pi * (N : ℝ) / (1 + s) := by
          apply (div_le_div_iff₀ hs0 (by positivity)).2
          have hcoef : 0 ≤ 9 * Real.pi * (N : ℝ) := by positivity
          have hnon : 0 ≤ (9 * Real.pi * (N : ℝ)) * (s - 1) :=
            mul_nonneg hcoef (sub_nonneg.mpr hs1)
          nlinarith [hnon]
        have hscale : 18 * Real.pi * ((N : ℝ) / (1 + s)) ≤ C *
            ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := by
          have hsum : 0 ≤ (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by positivity
          have hterm : 18 * Real.pi * ((N : ℝ) / (1 + s)) ≤
              18 * Real.pi * ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := by
            have hnon : 0 ≤ 18 * Real.pi * (Real.sqrt s + Real.sqrt (N : ℝ)) := by positivity
            nlinarith
          exact hterm.trans (mul_le_mul_of_nonneg_right hC18 hsum)
        calc
          ‖gmDyadicKernel N s‖ ≤ 9 * Real.pi * (N : ℝ) / s := by
            simpa [div_eq_mul_inv, mul_assoc] using hsmall'
          _ ≤ 18 * Real.pi * (N : ℝ) / (1 + s) := hratio
          _ = 18 * Real.pi * ((N : ℝ) / (1 + s)) := by ring
          _ ≤ C * ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := hscale
      · have hNS : (N : ℝ) ≤ s := le_of_not_ge hSN
        by_cases hlarge : (N : ℝ) ^ 2 ≤ s
        · have hedge := norm_gmDyadicKernel_le_shape_of_sq_le_abs hN
            (t := s) (by simpa [abs_of_nonneg hs] using hlarge)
          have hsump : 0 ≤ (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by positivity
          have hscale :
              (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) ≤
                C * ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) :=
            (by simpa only [one_mul] using
              mul_le_mul_of_nonneg_right hC1 hsump)
          have hedge' : ‖gmDyadicKernel N s‖ ≤
              (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by
            simpa [abs_of_nonneg hs] using hedge
          exact hedge'.trans hscale
        · have hHigh' := hHigh N hN s hNS (le_of_not_ge hlarge)
          have hsum : 0 ≤ (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by positivity
          have hscale : Ch * Real.sqrt s ≤ C *
              ((N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ)) := by
            have hterm : Real.sqrt s ≤
                (N : ℝ) / (1 + s) + Real.sqrt s + Real.sqrt (N : ℝ) := by
              have hratio : 0 ≤ (N : ℝ) / (1 + s) := by positivity
              nlinarith [Real.sqrt_nonneg (N : ℝ)]
            have hmul := mul_le_mul_of_nonneg_right hCCh (Real.sqrt_nonneg s)
            nlinarith
          exact hHigh'.trans hscale
  intro N hN t
  by_cases ht : 0 ≤ t
  · simpa [abs_of_nonneg ht, C] using hpos N hN t ht
  · have htneg : t < 0 := lt_of_not_ge ht
    have hsymm : ‖gmDyadicKernel N t‖ = ‖gmDyadicKernel N (-t)‖ := by
      simpa using (norm_gmDyadicKernel_neg N (-t))
    rw [hsymm, abs_of_neg htneg]
    simpa [abs_of_neg htneg, C] using hpos N hN (-t) (le_of_lt (neg_pos.mpr htneg))

end
end GuthMaynardGMKernelUniformShape

#print axioms GuthMaynardGMKernelUniformShape.norm_gmDyadicKernel_uniform_shape

theorem norm_gmDyadicKernel_uniform_shape_300 :
    ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      ‖GuthMaynardGMPointwiseKernel.gmDyadicKernel N t‖ ≤
        300 * ((N : ℝ) / (1 + |t|) + Real.sqrt |t| + Real.sqrt (N : ℝ)) := by
  have hpi : 18 * Real.pi ≤ (300 : ℝ) := by
    nlinarith [Real.pi_lt_four]
  have hHigh : ∀ N : ℕ, 1 ≤ N → ∀ t : ℝ,
      (N : ℝ) ≤ t → t ≤ (N : ℝ) ^ 2 →
    ‖GuthMaynardGMPointwiseKernel.gmDyadicKernel N t‖ ≤ (300 : ℝ) * Real.sqrt t := by
    intro N hN t hNt htN
    exact GuthMaynardGMPointwiseHighRangeActual.norm_kernel_high_range hN hNt htN
  intro N hN t
  have h := GuthMaynardGMKernelUniformShape.norm_gmDyadicKernel_uniform_shape
    (Ch := (300 : ℝ)) hHigh N hN t
  simpa [max_eq_left hpi] using h

theorem uniformPointwiseKernelBound_300 :
    GuthMaynardGMKernelCorrelation.UniformPointwiseKernelBound 300 := by
  constructor
  · norm_num
  · intro N hN L hL W hsep hW t htmem u humem
    exact norm_gmDyadicKernel_uniform_shape_300 N hN (u - t)

#print axioms norm_gmDyadicKernel_uniform_shape_300
#print axioms uniformPointwiseKernelBound_300
