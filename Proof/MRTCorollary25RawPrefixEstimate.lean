import MRTCorollary25RawPrefix

/-!
# Aggregated raw-prefix error for MRT Lemma 2.4(ii)
-/

namespace MAPMRTCorollary25RawPrefixEstimate

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25PerronCore
open MAPMRTCorollary25RawPrefix MAPMRTCorollary25MinSum
open PrimitiveTruncatedExplicitFormulaBridge
open MixedMeanFrontend

noncomputable section

/-- The literal coefficientwise transition estimate aggregated over the whole
source support.  This is MRT Lemma 2.4(ii)'s `X log(2+T)/T` error before the
later summation-by-parts saving. -/
theorem norm_rawPrefixOn_sub_kernelPrefixOn_le_sourceScale
    {C X T B t : ℝ} (hC : 1 < C) (hX : 1 ≤ X) (hT : 1 ≤ T)
    (hB : 0 ≤ B) {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    (hf : ∀ n : ℕ, ‖f n‖ ≤ B)
    {N : ℕ} (hN : N ≤ Nat.ceil (C * X)) :
    ‖rawPrefixOn (Finset.Icc 1 (Nat.ceil (C * X))) N f t -
      kernelPrefixOn (Finset.Icc 1 (Nat.ceil (C * X))) N f t
        (1 / 2 : ℝ) T‖ ≤
      24 * (1 + Real.sqrt (C * (C + 2))) * (C + 2) *
        B * X * (1 + Real.log (2 + T)) / T := by
  let S := Finset.Icc 1 (Nat.ceil (C * X))
  let K := 3 * (1 + Real.sqrt (C * (C + 2)))
  let A := (C + 2) * X / T
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hApos : 0 < A := div_pos (mul_pos (by linarith) hXpos) hTpos
  have hK0 : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hMscale : ((Nat.ceil (C * X) : ℕ) : ℝ) ≤ A * T := by
    have hCX0 : 0 ≤ C * X := mul_nonneg hCpos.le hXpos.le
    have hceil : ((Nat.ceil (C * X) : ℕ) : ℝ) < C * X + 1 :=
      Nat.ceil_lt_add_one hCX0
    dsimp only [A]
    field_simp [hTpos.ne']
    nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ X - 1)]
  rw [rawPrefixOn_eq_stepSum S N f t (by
    intro n hn
    exact (Finset.mem_Icc.mp hn).1)]
  unfold kernelPrefixOn
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ n ∈ S,
        ((f n * mellinPhase n t) *
            (if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0) -
          (f n * mellinPhase n t) *
            PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
              (1 / 2 : ℝ) T)‖ ≤
      ∑ n ∈ S,
        ‖(f n * mellinPhase n t) *
            ((if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0) -
              PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
                (1 / 2 : ℝ) T)‖ := by
      simpa only [mul_sub] using
        (norm_sum_le S (fun n => (f n * mellinPhase n t) *
          ((if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0) -
            PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
              (1 / 2 : ℝ) T)))
    _ ≤ ∑ n ∈ S, B * K *
        min 1 (A / |halfIntegerPoint N - (n : ℝ)|) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hnz : f n = 0
      · simp only [hnz, zero_mul, norm_zero]
        have hmin0 : 0 ≤ min 1 (A / |halfIntegerPoint N - (n : ℝ)|) :=
          le_min (by norm_num) (div_nonneg hApos.le (abs_nonneg _))
        exact mul_nonneg (mul_nonneg hB hK0) hmin0
      · have hk := norm_kernel_sub_step_le_supportDistanceMin
          hC hX hT hSupp hN hnz
        have hflip :
            ‖(if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0) -
                PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
                  (1 / 2 : ℝ) T‖ =
              ‖PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
                  (1 / 2 : ℝ) T -
                (if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0)‖ := by
          rw [← norm_neg]
          congr 1
          ring
        rw [norm_mul, norm_mul, hflip]
        have hphase : ‖mellinPhase n t‖ = 1 := by
          unfold mellinPhase
          rw [Complex.norm_exp]
          have hre :
              ((-((t * Real.log (n : ℝ) : ℝ) : ℂ)) * Complex.I).re = 0 := by
            simp only [Complex.mul_re, Complex.ofReal_re,
              Complex.ofReal_im, Complex.neg_re, Complex.neg_im,
              Complex.I_re, Complex.I_im]
            ring
          rw [hre, Real.exp_zero]
        rw [hphase, mul_one]
        have hmin0 : 0 ≤ min 1 (A / |halfIntegerPoint N - (n : ℝ)|) := by
          exact le_min (by norm_num) (div_nonneg hApos.le (abs_nonneg _))
        have hrewrite :
            ((C + 2) * X) /
                (T * |halfIntegerPoint N - (n : ℝ)|) =
              A / |halfIntegerPoint N - (n : ℝ)| := by
          dsimp only [A]
          ring
        rw [hrewrite] at hk
        exact calc
          ‖f n‖ *
              ‖PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
                  (1 / 2) T -
                (if 1 < halfIntegerPoint N / (n : ℝ) then 1 else 0)‖ ≤
            ‖f n‖ * (K *
              min 1 (A / |halfIntegerPoint N - (n : ℝ)|)) :=
              mul_le_mul_of_nonneg_left hk (norm_nonneg _)
          _ ≤ B * K * min 1 (A / |halfIntegerPoint N - (n : ℝ)|) := by
            have hcoef := hf n
            nlinarith [mul_nonneg hK0 hmin0,
              mul_le_mul_of_nonneg_right hcoef (mul_nonneg hK0 hmin0)]
    _ = B * K * ∑ n ∈ S,
        min 1 (A / |halfIntegerPoint N - (n : ℝ)|) := by
      rw [Finset.mul_sum]
    _ ≤ B * K * (2 * ∑ k ∈ Finset.Icc 0 (Nat.ceil (C * X)),
        min 1 (A / ((k : ℝ) + 1 / 2))) := by
      apply mul_le_mul_of_nonneg_left
      · exact halfInteger_minSum_le_two_shellSums
          (Nat.ceil (C * X)) N hN A hApos.le
      · exact mul_nonneg hB hK0
    _ ≤ B * K * (2 * (4 * A * (1 + Real.log (2 + T)))) := by
      apply mul_le_mul_of_nonneg_left
      · gcongr
        exact halfInteger_shellMinSum_le hApos hT hMscale
      · exact mul_nonneg hB hK0
    _ = 24 * (1 + Real.sqrt (C * (C + 2))) * (C + 2) *
        B * X * (1 + Real.log (2 + T)) / T := by
      dsimp only [K, A]
      ring

end
end MAPMRTCorollary25RawPrefixEstimate

#print axioms MAPMRTCorollary25RawPrefixEstimate.norm_rawPrefixOn_sub_kernelPrefixOn_le_sourceScale
