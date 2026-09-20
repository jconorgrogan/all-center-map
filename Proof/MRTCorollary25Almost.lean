import MRTCorollary25EndpointClip

/-!
# Source proof of MRT Corollary 2.5 up to fixed-constant normalization
-/

namespace MAPMRTCorollary25Almost

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25PerronCore
open MAPMRTCorollary25RawPrefixFormula MAPMRTCorollary25EndpointClip
open MAPMRTCorollary25Abel MixedMeanFrontend

noncomputable section

/-- Below `ceil(X/C)`, the source support condition kills every coefficient. -/
theorem supported_eq_zero_below_ceil
    {C X : ℝ} {f : ℕ → ℂ} (hC : 1 < C) (hX : 1 ≤ X)
    (hSupp : SupportedNear X C f) {n : ℕ}
    (hn : n < Nat.ceil (X / C)) : f n = 0 := by
  apply hSupp n
  left
  exact (Nat.lt_ceil).mp hn

/-- The exact Corollary 2.5 cutoff polynomial is bounded by the certified raw
Perron envelope divided by the square root of the support's lower edge. -/
theorem cutoffPolynomial_le_four_rawEnvelope_div_sqrtLower
    {C X T X1 X2 t B : ℝ} (hC : 1 < C) (hX : 1 ≤ X)
    (hT : 1 ≤ T) (hB : 0 ≤ B) {f : ℕ → ℂ}
    (hSupp : SupportedNear X C f) (hf : ∀ n : ℕ, ‖f n‖ ≤ B) :
    let L := Nat.ceil (X / C)
    let M := Nat.ceil (C * X)
    let P :=
      3 * Real.sqrt ((C + 2) * X) *
        (∫ u in (-T)..T,
          ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|)) +
      24 * (1 + Real.sqrt (C * (C + 2))) * (C + 2) *
        B * X * (1 + Real.log (2 + T)) / T
    ‖halfLineDirichletPolynomial X C (intervalCutoff X1 X2 f) t‖ ≤
      4 * P / Real.sqrt (L : ℝ) := by
  dsimp only
  let L := Nat.ceil (X / C)
  let M := Nat.ceil (C * X)
  let P :=
      3 * Real.sqrt ((C + 2) * X) *
        (∫ u in (-T)..T,
          ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|)) +
      24 * (1 + Real.sqrt (C * (C + 2))) * (C + 2) *
        B * X * (1 + Real.log (2 + T)) / T
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hL : 1 ≤ L := by
    dsimp only [L]
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.ne_of_gt (Nat.ceil_pos.mpr (div_pos hXpos hCpos)))
  have hLM : L ≤ M := by
    apply Nat.ceil_mono
    apply (div_le_iff₀ hCpos).2
    nlinarith [mul_nonneg hXpos.le (sq_nonneg (C - 1))]
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    have hInt0 : 0 ≤ ∫ u in (-T)..T,
        ‖halfLineDirichletPolynomial X C f (t + u)‖ / (1 + |u|) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu
      positivity
    have hlog0 : 0 ≤ 1 + Real.log (2 + T) := by
      have : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
      linarith
    have hR0 : 0 ≤ C * (C + 2) := mul_nonneg hCpos.le (by linarith)
    have hCX0 : 0 ≤ (C + 2) * X := mul_nonneg (by linarith) hXpos.le
    positivity
  have hraw : ∀ K : ℕ, K ≤ M →
      ‖rawPrefixOn (Finset.Icc 1 M) K f t‖ ≤ P := by
    intro K hKM
    dsimp only [M, P] at hKM ⊢
    exact norm_rawPrefixOn_le_sourcePerron hC hX hT hB hSupp hf hKM
  let a : ℕ → ℂ := fun n => intervalCutoff X1 X2 f n * mellinPhase n t
  have hprefix : ∀ N : ℕ, L ≤ N → N ≤ M →
      ‖∑ n ∈ Finset.Icc L N, a n‖ ≤ 2 * P := by
    intro N hLN hNM
    have hclip := intervalCutoff_prefix_norm_le_two M N hNM f t X1 X2 P hP0 hraw
    have hfilter :
        (∑ n ∈ Finset.Icc 1 M,
          if n ≤ N then intervalCutoff X1 X2 f n * mellinPhase n t else 0) =
          ∑ n ∈ Finset.Icc 1 N, a n := by
      rw [← Finset.sum_filter]
      have hset : (Finset.Icc 1 M).filter (fun n => n ≤ N) =
          Finset.Icc 1 N := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Icc]
        omega
      rw [hset]
    rw [hfilter] at hclip
    have hsubset : Finset.Icc L N ⊆ Finset.Icc 1 N := by
      intro n hn
      have h := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨hL.trans h.1, h.2⟩
    have hzero : ∀ n ∈ Finset.Icc 1 N, n ∉ Finset.Icc L N → a n = 0 := by
      intro n hn hnnot
      have hnI := Finset.mem_Icc.mp hn
      have hnlt : n < L := by
        simp only [Finset.mem_Icc, not_and_or] at hnnot
        omega
      have hf0 := supported_eq_zero_below_ceil hC hX hSupp hnlt
      simp [a, intervalCutoff, hf0]
    have hsum := Finset.sum_subset hsubset hzero
    rw [hsum]
    exact hclip
  have hAbel := norm_sum_Icc_invSqrt_le_of_prefix a hL hLM
    (mul_nonneg (by norm_num) hP0) hprefix
  have htarget :
      halfLineDirichletPolynomial X C (intervalCutoff X1 X2 f) t =
        ∑ n ∈ Finset.Icc L M,
          (((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ) * a n) := by
    unfold halfLineDirichletPolynomial
    change (∑ n ∈ Finset.Icc 1 M,
      (intervalCutoff X1 X2 f n / (Real.sqrt (n : ℝ) : ℂ)) *
        mellinPhase n t) = _
    have hsubset : Finset.Icc L M ⊆ Finset.Icc 1 M := by
      intro n hn
      have h := Finset.mem_Icc.mp hn
      exact Finset.mem_Icc.mpr ⟨hL.trans h.1, h.2⟩
    have hzero : ∀ n ∈ Finset.Icc 1 M, n ∉ Finset.Icc L M →
        (intervalCutoff X1 X2 f n / (Real.sqrt (n : ℝ) : ℂ)) *
          mellinPhase n t = 0 := by
      intro n hn hnnot
      have hnI := Finset.mem_Icc.mp hn
      have hnlt : n < L := by
        simp only [Finset.mem_Icc, not_and_or] at hnnot
        omega
      have hf0 := supported_eq_zero_below_ceil hC hX hSupp hnlt
      simp [intervalCutoff, hf0]
    have hrestrict := Finset.sum_subset hsubset hzero
    rw [← hrestrict]
    apply Finset.sum_congr rfl
    intro n hn
    dsimp only [a]
    push_cast
    ring
  rw [htarget]
  convert hAbel using 1 <;> ring

end
end MAPMRTCorollary25Almost

#print axioms MAPMRTCorollary25Almost.cutoffPolynomial_le_four_rawEnvelope_div_sqrtLower
