import GuthMaynardSectionFourNormalization
import GuthMaynardS1Tail

/-! # Guth--Maynard Lemma 4.4 with an explicit Poisson tail -/

namespace GuthMaynardLemma44TraceOne

open scoped BigOperators
open GuthMaynardSectionFourTrace GuthMaynardSectionFourNormalization
open GuthMaynardSectionFourPoisson GuthMaynardS1Source GuthMaynardS1Tail
open GuthMaynardSectionThreeCutoff GuthMaynardJIteration
open GuthMaynardSectionThreeCutoffDerivativeBudget

noncomputable section

def sourceTraceOnePoissonTail (N : ℕ) (W : Finset ℝ) : ℂ :=
  (N : ℂ) * (W.card : ℂ) *
    ∑' m : ℤ, if m = 0 then 0 else sourceHhat 0 ((m : ℝ) * (N : ℝ))

theorem nat_div_pow_eq_zpow_one_sub
    {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (N : ℝ) / (N : ℝ) ^ j = (N : ℝ) ^ ((1 : ℤ) - (j : ℤ)) := by
  rw [zpow_sub₀ (by exact_mod_cast hN.ne')]
  norm_num

theorem sourceTraceOne_eq_poisson
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceOne W N =
      (N : ℂ) * (W.card : ℂ) *
        (∑' m : ℤ, sourceHhat 0 ((m : ℝ) * (N : ℝ))) := by
  unfold sourceTraceOne Matrix.trace
  simp only [Matrix.diag_apply]
  calc
    (∑ t : SourceRow W, sourceGram W N t t) =
        ∑ _t : SourceRow W, ∑ n : SourceColumn N,
          sectionThreeOscillatory 0 (((n : ℕ) : ℝ) / (N : ℝ)) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [sourceGram_eq_rowPhases_mul_normalized hN]
      rw [sourceRowPhase_mul_star]
      simp only [one_mul]
      simpa using sourceNormalizedGram_apply_oscillatory hN W t t
    _ = (W.card : ℂ) *
        (∑' z : ℤ, sectionThreeOscillatory 0 ((z : ℝ) / (N : ℝ))) := by
      rw [tsum_oscillatory_eq_columnSum 0 hN]
      simp
    _ = (W.card : ℂ) *
        ((N : ℂ) * ∑' m : ℤ, sourceHhat 0 ((m : ℝ) * (N : ℝ))) := by
      rw [tsum_sectionThreeOscillatory_scaled_eq 0 hN]
    _ = _ := by ring

theorem sourceTraceOne_eq_main_add_tail
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) :
    sourceTraceOne W N =
      (N : ℂ) * (W.card : ℂ) * sourceHhat 0 0 +
        sourceTraceOnePoissonTail N W := by
  rw [sourceTraceOne_eq_poisson hN W]
  have hs := (summable_norm_sourceHhat_scaled 0 hN).of_norm
  have hsplit := hs.tsum_eq_add_tsum_ite (0 : ℤ)
  rw [hsplit]
  unfold sourceTraceOnePoissonTail
  simp only [Int.cast_zero, zero_mul]
  ring

/-- Arbitrary-order `N^(1-j)` form of the Lemma 4.4 Poisson error.  The
source derivative order is `j=q+2`, so `q` may be chosen freely. -/
theorem norm_sourceTraceOnePoissonTail_le
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (q : ℕ) :
    ‖sourceTraceOnePoissonTail N W‖ ≤
      (W.card : ℝ) * lemma43DerivativeConstant (q + 2) *
        (2 ^ (q + 2) * integerQuadraticMass) *
          ((N : ℝ) / (N : ℝ) ^ (q + 2)) := by
  let f : ℤ → ℂ := fun m =>
    if m = 0 then 0 else sourceHhat 0 ((m : ℝ) * (N : ℝ))
  let g : ℤ → ℝ := fun m =>
    lemma43DerivativeConstant (q + 2) * (1 / (N : ℝ) ^ (q + 2)) *
      (if (1 : ℝ) ≤ |(m : ℝ)| then 1 / |(m : ℝ)| ^ (q + 2) else 0)
  have hpure := summable_far_power q (B := (1 : ℝ)) (by norm_num)
  have hK : 0 ≤ lemma43DerivativeConstant (q + 2) *
      (1 / (N : ℝ) ^ (q + 2)) := by
    exact mul_nonneg (lemma43DerivativeConstant_nonneg _)
      (by positivity)
  have hg : Summable g := hpure.mul_left _
  have hf0 : ∀ m, 0 ≤ ‖f m‖ := fun m => norm_nonneg _
  have hfg : ∀ m, ‖f m‖ ≤ g m := by
    intro m
    by_cases hm : m = 0
    · subst m
      simp [f, g]
    · have hm1 := one_le_abs_intCast hm
      have hraw := norm_sourceHhat_le_horizontal 0 (q + 2)
        (show (m : ℝ) * (N : ℝ) ≠ 0 by
          exact mul_ne_zero (Int.cast_ne_zero.mpr hm) (Nat.cast_ne_zero.mpr hN.ne'))
      have hscale := inv_abs_int_mul_nat_pow_eq hm hN (q + 2)
      simp only [f, if_neg hm]
      rw [show g m = lemma43DerivativeConstant (q + 2) *
          (1 / (N : ℝ) ^ (q + 2)) *
            (1 / |(m : ℝ)| ^ (q + 2)) by simp [g, hm1]]
      calc
        ‖sourceHhat 0 ((m : ℝ) * (N : ℝ))‖ ≤
            lemma43DerivativeConstant (q + 2) /
              |(m : ℝ) * (N : ℝ)| ^ (q + 2) := by
                simpa using hraw
        _ = _ := by
          rw [show lemma43DerivativeConstant (q + 2) /
                |(m : ℝ) * (N : ℝ)| ^ (q + 2) =
              lemma43DerivativeConstant (q + 2) *
                (1 / |(m : ℝ) * (N : ℝ)| ^ (q + 2)) by ring,
            hscale]
          ring
  have hfnorm : Summable fun m => ‖f m‖ := hg.of_nonneg_of_le hf0 hfg
  have htsum : ‖∑' m, f m‖ ≤
      lemma43DerivativeConstant (q + 2) *
        (1 / (N : ℝ) ^ (q + 2)) *
          (2 ^ (q + 2) * integerQuadraticMass) := by
    calc
      ‖∑' m, f m‖ ≤ ∑' m, ‖f m‖ := norm_tsum_le_tsum_norm hfnorm
      _ ≤ ∑' m, g m := hfnorm.tsum_le_tsum hfg hg
      _ = (lemma43DerivativeConstant (q + 2) *
          (1 / (N : ℝ) ^ (q + 2))) *
            (∑' m : ℤ, if (1 : ℝ) ≤ |(m : ℝ)| then
              1 / |(m : ℝ)| ^ (q + 2) else 0) := by
                rw [hpure.tsum_mul_left]
      _ ≤ (lemma43DerivativeConstant (q + 2) *
          (1 / (N : ℝ) ^ (q + 2))) *
            (2 ^ (q + 2) * integerQuadraticMass) := by
              gcongr
              simpa using tsum_far_power_le q (B := (1 : ℝ)) (by norm_num)
      _ = _ := by ring
  unfold sourceTraceOnePoissonTail
  change ‖(N : ℂ) * (W.card : ℂ) * (∑' m, f m)‖ ≤ _
  rw [norm_mul, norm_mul]
  simp only [Complex.norm_natCast]
  have hscaled := mul_le_mul_of_nonneg_left htsum
    (mul_nonneg (Nat.cast_nonneg N) (Nat.cast_nonneg W.card))
  calc
    (N : ℝ) * (W.card : ℝ) * ‖∑' m, f m‖ ≤
        (N : ℝ) * (W.card : ℝ) *
          (lemma43DerivativeConstant (q + 2) *
            (1 / (N : ℝ) ^ (q + 2)) *
              (2 ^ (q + 2) * integerQuadraticMass)) := hscaled
    _ = _ := by ring

theorem norm_sourceTraceOne_sub_main_le
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (q : ℕ) :
    ‖sourceTraceOne W N -
        (N : ℂ) * (W.card : ℂ) * sourceHhat 0 0‖ ≤
      (W.card : ℝ) * lemma43DerivativeConstant (q + 2) *
        (2 ^ (q + 2) * integerQuadraticMass) *
          ((N : ℝ) / (N : ℝ) ^ (q + 2)) := by
  rw [sourceTraceOne_eq_main_add_tail hN W]
  simpa using norm_sourceTraceOnePoissonTail_le hN W q

/-- The same bound in the literal source notation `N^(1-j)`, with
`j=q+2`. -/
theorem norm_sourceTraceOne_sub_main_le_zpow
    {N : ℕ} (hN : 0 < N) (W : Finset ℝ) (q : ℕ) :
    ‖sourceTraceOne W N -
        (N : ℂ) * (W.card : ℂ) * sourceHhat 0 0‖ ≤
      (W.card : ℝ) * lemma43DerivativeConstant (q + 2) *
        (2 ^ (q + 2) * integerQuadraticMass) *
          (N : ℝ) ^ ((1 : ℤ) - ((q + 2 : ℕ) : ℤ)) := by
  rw [← nat_div_pow_eq_zpow_one_sub hN (q + 2)]
  exact norm_sourceTraceOne_sub_main_le hN W q

end
end GuthMaynardLemma44TraceOne

#print axioms GuthMaynardLemma44TraceOne.sourceTraceOne_eq_poisson
#print axioms GuthMaynardLemma44TraceOne.norm_sourceTraceOne_sub_main_le
#print axioms GuthMaynardLemma44TraceOne.norm_sourceTraceOne_sub_main_le_zpow
