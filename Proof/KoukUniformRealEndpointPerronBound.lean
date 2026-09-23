import KoukSelectedHeightRealEndpointFormula
import PaperEdgePerronRemainder
import PaperEdgeOutsidePerronTail
import MRTCorollary25TransitionBand

/-!
# The literal real-endpoint finite Perron estimate

This file proves the deterministic Perron leaf used by the selected-height
version of Koukoulopoulos' Theorem 11.3.  The arithmetic cutoff remains
`Finset.Icc 1 floor(t)`.  The two coefficients adjacent to the discontinuity
are treated by the continuous transition kernel; all other coefficients use
the sharp logarithmic-distance estimate.
-/

namespace KoukUniformRealEndpointPerronBound

open Set
open scoped BigOperators ArithmeticFunction
open APFoundation PrimitiveExplicitFormulaSpine
open PrimitiveTruncatedExplicitFormulaBridge TruncatedTwistedPerron

noncomputable section

/-- The inside part of Perron's error at the requested real endpoint. -/
def realInsideKernelError {q : ℕ} (chi : DirichletCharacter ℂ q)
    (t : ℝ) (N : ℕ) (c T : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    twistedMangoldtCoeff chi n * (1 - PerronKernel.kernel (t / n) c T)

/-- Exact inside/outside decomposition, before any estimate. -/
theorem realEndpointPerronError_eq_inside_sub_tail
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t c T : ℝ} (ht : 0 < t) (hc : 1 < c) :
    KoukSelectedHeightRealEndpointFormula.realEndpointPerronError chi t c T =
      realInsideKernelError chi t ⌊t⌋₊ c T -
        coefficientTail chi t c T (Finset.Icc 1 ⌊t⌋₊) := by
  have hright := rightLineIntegral_eq_Icc_kernel_sum_add_tail
    chi (T := T) ht hc ⌊t⌋₊
  unfold KoukSelectedHeightRealEndpointFormula.realEndpointPerronError
    realInsideKernelError
  rw [hright, APFoundation.twistedMangoldtSum]
  rw [sub_add_eq_sub_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [twistedMangoldtCoeff]
  ring

/-- At a positive-height Perron transition the kernel is within a fixed
constant of either step value.  This is the only estimate used for the one
or two indices adjacent to the real endpoint. -/
theorem norm_kernel_sub_step_le_twenty
    {y c T : ℝ} (hy : 0 < y) (hyR : y ≤ 2)
    (hc0 : 0 < c) (hc2 : c ≤ 2) (hT : 2 ≤ T) :
    ‖PerronKernel.kernel y c T -
        (if 1 < y then (1 : ℂ) else 0)‖ ≤ 20 := by
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  by_cases hy1 : y = 1
  · subst y
    have hcenter :=
      MAPMRTCorollary25TransitionBand.norm_kernel_one_sub_step_le_one
        (y := (1 : ℝ)) hc0 hT0
    simpa using hcenter.trans (by norm_num : (1 : ℝ) ≤ 20)
  · have hlogpos : 0 < |Real.log y| :=
      abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hy hy1)
    by_cases hnear : |Real.log y| * (c + T) ≤ 1
    · have hnearKernel := PerronKernel.norm_kernel_sub_one_le
        hy hc0 hT0 hnear
      have hcenter :=
        MAPMRTCorollary25TransitionBand.norm_kernel_one_sub_step_le_one
          (y := y) hc0 hT0
      have htri :
          ‖PerronKernel.kernel y c T -
              (if 1 < y then (1 : ℂ) else 0)‖ ≤
            ‖PerronKernel.kernel y c T - PerronKernel.kernel 1 c T‖ +
              ‖PerronKernel.kernel 1 c T -
                (if 1 < y then (1 : ℂ) else 0)‖ := by
        simpa [sub_eq_add_neg, add_assoc] using
          norm_add_le
            (PerronKernel.kernel y c T - PerronKernel.kernel 1 c T)
            (PerronKernel.kernel 1 c T -
              (if 1 < y then (1 : ℂ) else 0))
      have hTc : T ≤ c + T := by linarith
      have hTa : T * |Real.log y| ≤ 1 := by
        nlinarith [abs_nonneg (Real.log y)]
      have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
      calc
        _ ≤ 2 * T * |Real.log y| / Real.pi + 1 :=
          htri.trans (add_le_add hnearKernel hcenter)
        _ ≤ 3 := by
          have : 2 * T * |Real.log y| / Real.pi ≤ 2 := by
            apply (div_le_iff₀ Real.pi_pos).2
            nlinarith
          linarith
        _ ≤ 20 := by norm_num
    · have hsharp := SharpFinitePerronStep.norm_kernel_sub_step_le
        hy hc0 hTpos hy1
      have hfar : 1 < |Real.log y| * (c + T) := lt_of_not_ge hnear
      have hden : 0 < Real.pi * T * |Real.log y| := by positivity
      have hrpow : y ^ c ≤ 4 := by
        calc
          y ^ c ≤ (2 : ℝ) ^ c := Real.rpow_le_rpow hy.le hyR hc0.le
          _ ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hc2
          _ = 4 := by norm_num
      have hcT : c + T ≤ 2 * T := by linarith
      have hinv : 1 / |Real.log y| < c + T := by
        rw [div_lt_iff₀ hlogpos]
        simpa [mul_comm] using hfar
      have hyc0 : 0 ≤ y ^ c := Real.rpow_nonneg hy.le c
      have hinner : y ^ c / (T * |Real.log y|) ≤
          y ^ c * (c + T) / T := by
        have hinvle : 1 / |Real.log y| ≤ c + T := hinv.le
        calc
          y ^ c / (T * |Real.log y|) =
              (y ^ c * (1 / |Real.log y|)) / T := by ring
          _ ≤ (y ^ c * (c + T)) / T := by
            exact div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left hinvle hyc0) hTpos.le
      have hinner8 : y ^ c * (c + T) / T ≤ 8 := by
        apply (div_le_iff₀ hTpos).2
        nlinarith
      calc
        _ ≤ y ^ c / (Real.pi * T * |Real.log y|) := hsharp
        _ = (y ^ c / (T * |Real.log y|)) / Real.pi := by ring
        _ ≤ (y ^ c * (c + T) / T) / Real.pi :=
          div_le_div_of_nonneg_right hinner Real.pi_pos.le
        _ ≤ 8 / Real.pi :=
          div_le_div_of_nonneg_right hinner8 Real.pi_pos.le
        _ ≤ 20 := by
          have hp : 0 < Real.pi := Real.pi_pos
          rw [div_le_iff₀ hp]
          nlinarith [Real.pi_gt_three]

/-- Sharp non-transition inside summand at a literal real endpoint. -/
theorem norm_inside_nontransition_term_le
    {q n : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT : 0 < T)
    (hn1 : 1 ≤ n) (hnt : (n : ℝ) < t) :
    ‖twistedMangoldtCoeff chi n *
        (1 - PerronKernel.kernel (t / n)
          (1 + (Real.log t)⁻¹) T)‖ ≤
      (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
        (1 / (n : ℝ) + 1 / (t - (n : ℝ))) := by
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hypos : 0 < t / (n : ℝ) := div_pos ht0 hnpos
  have hyone : 1 < t / (n : ℝ) := (one_lt_div hnpos).2 hnt
  have hc : 0 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr hlog
    linarith
  have hk := SharpFinitePerronStep.norm_kernel_sub_one_le hyone hc hT
  have hflip :
      ‖1 - PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T‖ =
        ‖PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T - 1‖ := by
    rw [← norm_neg]
    congr 1
    ring
  have hratio : t / (n : ℝ) ≤ t := by
    rw [div_le_iff₀ hnpos]
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  have hrpow := PaperEdgePerronRemainder.rpow_standardEdge_le
    ht1 hypos hratio
  have hlogLower := PerronKernel.abs_log_div_ge_abs_sub_div_max ht0 hnpos
  rw [max_eq_left hnt.le, abs_of_pos (sub_pos.mpr hnt)] at hlogLower
  have hdist : 0 < t - (n : ℝ) := sub_pos.mpr hnt
  have hlogAbs : 0 < |Real.log (t / (n : ℝ))| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hypos hyone.ne')
  have hvm : ArithmeticFunction.vonMangoldt n ≤ Real.log t :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hnpos hnt.le)
  rw [norm_mul, hflip]
  have hcoeff := norm_twistedMangoldtCoeff_le chi n
  calc
    ‖twistedMangoldtCoeff chi n‖ *
        ‖PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T - 1‖ ≤
      ArithmeticFunction.vonMangoldt n *
        ((t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) /
          (Real.pi * T * |Real.log (t / (n : ℝ))|)) :=
      mul_le_mul hcoeff hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = (ArithmeticFunction.vonMangoldt n *
          (t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) /
          (Real.pi * T)) * (1 / |Real.log (t / (n : ℝ))|) := by ring
    _ ≤ (Real.log t * (Real.exp 1 * (t / (n : ℝ))) /
          (Real.pi * T)) * (t / (t - (n : ℝ))) := by
      have hnum : ArithmeticFunction.vonMangoldt n *
          (t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) ≤
          Real.log t * (Real.exp 1 * (t / (n : ℝ))) :=
        mul_le_mul hvm hrpow (Real.rpow_nonneg hypos.le _) hlog.le
      have hfront : ArithmeticFunction.vonMangoldt n *
          (t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) /
            (Real.pi * T) ≤
          Real.log t * (Real.exp 1 * (t / (n : ℝ))) /
            (Real.pi * T) :=
        div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      have hinv : 1 / |Real.log (t / (n : ℝ))| ≤
          t / (t - (n : ℝ)) := by
        calc
          1 / |Real.log (t / (n : ℝ))| ≤
              1 / ((t - (n : ℝ)) / t) :=
            one_div_le_one_div_of_le (div_pos hdist ht0) hlogLower
          _ = t / (t - (n : ℝ)) := by
            field_simp [ht0.ne', hdist.ne']
      exact mul_le_mul hfront hinv (by positivity) (by positivity)
    _ = (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
          (1 / (n : ℝ) + 1 / (t - (n : ℝ))) := by
      field_simp [hnpos.ne', hdist.ne', (mul_pos Real.pi_pos hT).ne']
      ring

/-- The endpoint coefficient `n=floor(t)` is uniformly controlled by the
transition estimate, including the exact-integer case. -/
theorem norm_inside_endpoint_term_le
    {q N : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT : 2 ≤ T)
    (hN1 : 1 ≤ N) (hNle : (N : ℝ) ≤ t)
    (htN1 : t < (N : ℝ) + 1) :
    ‖twistedMangoldtCoeff chi N *
        (1 - PerronKernel.kernel (t / N)
          (1 + (Real.log t)⁻¹) T)‖ ≤
      20 * Real.log (t + 2) := by
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hy : 0 < t / (N : ℝ) := div_pos ht0 hNpos
  have hy2 : t / (N : ℝ) ≤ 2 := by
    rw [div_le_iff₀ hNpos]
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    nlinarith
  have hc0 : 0 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr hlog
    linarith
  have hc2 : 1 + (Real.log t)⁻¹ ≤ 2 := by
    have hlog2 : 2 ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht0).2 ht2
    have hinv : (Real.log t)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hlog]
      linarith
    linarith
  have hk := norm_kernel_sub_step_le_twenty hy hy2 hc0 hc2 hT
  have hyStep : 1 < t / (N : ℝ) ↔ (N : ℝ) < t :=
    one_lt_div hNpos
  have hvm : ArithmeticFunction.vonMangoldt N ≤ Real.log (t + 2) := by
    have hNt : (N : ℝ) ≤ t + 2 := by linarith
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hNpos hNt)
  rw [norm_mul]
  have hcoeff := norm_twistedMangoldtCoeff_le chi N
  by_cases hstrict : (N : ℝ) < t
  · have hstep : (if 1 < t / (N : ℝ) then (1 : ℂ) else 0) = 1 := by
      simp [hyStep, hstrict]
    rw [hstep] at hk
    have hflip :
        ‖1 - PerronKernel.kernel (t / N) (1 + (Real.log t)⁻¹) T‖ =
          ‖PerronKernel.kernel (t / N) (1 + (Real.log t)⁻¹) T - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hflip]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt N * 20 :=
        mul_le_mul hcoeff hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ Real.log (t + 2) * 20 :=
        mul_le_mul_of_nonneg_right hvm (by norm_num)
      _ = 20 * Real.log (t + 2) := by ring
  · have heq : (N : ℝ) = t := le_antisymm hNle (le_of_not_gt hstrict)
    have hyone : t / (N : ℝ) = 1 := by rw [← heq]; field_simp [hNpos.ne']
    rw [hyone]
    have hcenter :=
      MAPMRTCorollary25TransitionBand.norm_kernel_one_sub_step_le_one
        (y := (2 : ℝ)) hc0 (le_trans (by norm_num) hT)
    simp only [show (1 : ℝ) < 2 by norm_num, if_true] at hcenter
    have hflip :
        ‖1 - PerronKernel.kernel 1 (1 + (Real.log t)⁻¹) T‖ =
          ‖PerronKernel.kernel 1 (1 + (Real.log t)⁻¹) T - 1‖ := by
      rw [← norm_neg]
      congr 1
      ring
    rw [hflip]
    calc
      _ ≤ ArithmeticFunction.vonMangoldt N * 1 :=
        mul_le_mul hcoeff hcenter (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
      _ ≤ Real.log (t + 2) * 1 :=
        mul_le_mul_of_nonneg_right hvm (by norm_num)
      _ ≤ 20 * Real.log (t + 2) := by
        have : 0 ≤ Real.log (t + 2) := Real.log_nonneg (by linarith)
        nlinarith

/-- Complete literal inside Perron error.  The last coefficient is separated
before the harmonic estimate, so the bound remains uniform as `t` approaches
an integer. -/
theorem norm_realInsideKernelError_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT2 : 2 ≤ T) (hTt : T ≤ t) :
    ‖realInsideKernelError chi t ⌊t⌋₊
        (1 + (Real.log t)⁻¹) T‖ ≤
      100 * t * (Real.log (t + 2)) ^ 2 / T := by
  let N : ℕ := ⌊t⌋₊
  let M : ℕ := N - 1
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT2
  have hNle : (N : ℝ) ≤ t := by
    dsimp only [N]
    exact Nat.floor_le ht0.le
  have htN1 : t < (N : ℝ) + 1 := by
    dsimp only [N]
    exact Nat.lt_floor_add_one t
  have hN1 : 1 ≤ N := by
    apply Nat.le_floor
    exact_mod_cast (show (1 : ℝ) ≤ t by linarith)
  have hMN : M + 1 = N := by
    dsimp only [M]
    omega
  have hMleN : M ≤ N := by dsimp only [M]; omega
  have hsumSplit (f : ℕ → ℝ) :
      (∑ n ∈ Finset.Icc 1 N, f n) =
        (∑ n ∈ Finset.Icc 1 M, f n) + f N := by
    rw [← hMN]
    exact Finset.sum_Icc_succ_top (by omega) f
  have hnorm :
      ‖realInsideKernelError chi t N (1 + (Real.log t)⁻¹) T‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖twistedMangoldtCoeff chi n *
            (1 - PerronKernel.kernel (t / n)
              (1 + (Real.log t)⁻¹) T)‖ := by
    unfold realInsideKernelError
    exact norm_sum_le _ _
  rw [hsumSplit] at hnorm
  have hsafe :
      (∑ n ∈ Finset.Icc 1 M,
          ‖twistedMangoldtCoeff chi n *
            (1 - PerronKernel.kernel (t / n)
              (1 + (Real.log t)⁻¹) T)‖) ≤
        (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
          (∑ n ∈ Finset.Icc 1 M,
            (1 / (n : ℝ) + 1 / (t - (n : ℝ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
    have hnltN : n < N := by omega
    have hnt : (n : ℝ) < t := by
      have : (n : ℝ) < N := by exact_mod_cast hnltN
      exact this.trans_le hNle
    exact norm_inside_nontransition_term_le chi ht2 hT hn1 hnt
  have htrans := norm_inside_endpoint_term_le chi ht2 hT2 hN1 hNle htN1
  have hrecip :
      (∑ n ∈ Finset.Icc 1 M,
        (1 / (n : ℝ) + 1 / (t - (n : ℝ)))) ≤
          2 * ((harmonic M : ℚ) : ℝ) := by
    rw [Finset.sum_add_distrib,
      PaperEdgePerronRemainder.sum_Icc_one_div_eq_harmonic]
    have hsecond :
        (∑ n ∈ Finset.Icc 1 M, 1 / (t - (n : ℝ))) ≤
          ∑ n ∈ Finset.Icc 1 M,
            1 / ((M + 1 - n : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnM : n ≤ M := (Finset.mem_Icc.mp hn).2
      have hdenNat : 0 < M + 1 - n := by omega
      have hden : 0 < ((M + 1 - n : ℕ) : ℝ) := by exact_mod_cast hdenNat
      have hcast : ((M + 1 - n : ℕ) : ℝ) = (N : ℝ) - (n : ℝ) := by
        rw [Nat.cast_sub (by omega : n ≤ M + 1)]
        norm_num [hMN]
      rw [hcast]
      have hden' : 0 < (N : ℝ) - (n : ℝ) := by
        rw [← hcast]
        exact hden
      exact one_div_le_one_div_of_le hden' (by linarith)
    rw [PaperEdgePerronRemainder.sum_Icc_reverse_one_div_eq_harmonic] at hsecond
    linarith
  have hLp : 1 ≤ Real.log (t + 2) := by
    have htp : Real.exp 1 ≤ t + 2 := by
      have : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    exact (Real.le_log_iff_exp_le (by linarith : 0 < t + 2)).2 htp
  have hlogLe : Real.log t ≤ Real.log (t + 2) :=
    Real.log_le_log ht0 (by linarith)
  have hharm : ((harmonic M : ℚ) : ℝ) ≤
      2 * Real.log (t + 2) := by
    calc
      ((harmonic M : ℚ) : ℝ) ≤ 1 + Real.log M := harmonic_le_one_add_log M
      _ ≤ 1 + Real.log t := by
        by_cases hM0 : M = 0
        · rw [hM0]
          norm_num
          linarith
        · have hMpos : 0 < (M : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hM0
          have hMt : (M : ℝ) ≤ t :=
            (by exact_mod_cast hMleN : (M : ℝ) ≤ (N : ℝ)).trans hNle
          linarith [Real.log_le_log hMpos hMt]
      _ ≤ 2 * Real.log (t + 2) := by linarith
  have hsafeFinal :
      (∑ n ∈ Finset.Icc 1 M,
          ‖twistedMangoldtCoeff chi n *
            (1 - PerronKernel.kernel (t / n)
              (1 + (Real.log t)⁻¹) T)‖) ≤
        20 * t * (Real.log (t + 2)) ^ 2 / T := by
    calc
      _ ≤ (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
          (∑ n ∈ Finset.Icc 1 M,
            (1 / (n : ℝ) + 1 / (t - (n : ℝ)))) := hsafe
      _ ≤ (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
          (4 * Real.log (t + 2)) := by
        gcongr
        linarith
      _ ≤ 20 * t * (Real.log (t + 2)) ^ 2 / T := by
        have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
        have hp : 3 ≤ Real.pi := Real.pi_gt_three.le
        have hepi : Real.exp 1 / Real.pi ≤ 1 := by
          rw [div_le_one Real.pi_pos]
          exact he.trans hp
        have hbase0 : 0 ≤ t * Real.log t * Real.log (t + 2) / T := by
          positivity
        calc
          (Real.exp 1 * t * Real.log t / (Real.pi * T)) *
              (4 * Real.log (t + 2)) =
            4 * (Real.exp 1 / Real.pi) *
              (t * Real.log t * Real.log (t + 2) / T) := by ring
          _ ≤ 4 * 1 *
              (t * Real.log t * Real.log (t + 2) / T) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hepi (by norm_num)) hbase0
          _ ≤ 4 * (t * Real.log (t + 2) ^ 2 / T) := by
            have hmul : t * Real.log t * Real.log (t + 2) ≤
                t * Real.log (t + 2) ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_left hlogLe ht0.le]
            have := div_le_div_of_nonneg_right hmul hT.le
            nlinarith
          _ ≤ 20 * t * Real.log (t + 2) ^ 2 / T := by
            have hA : 0 ≤ t * Real.log (t + 2) ^ 2 / T := by positivity
            calc
              4 * (t * Real.log (t + 2) ^ 2 / T) ≤
                  20 * (t * Real.log (t + 2) ^ 2 / T) :=
                mul_le_mul_of_nonneg_right (by norm_num) hA
              _ = 20 * t * Real.log (t + 2) ^ 2 / T := by ring
  have htransFinal : 20 * Real.log (t + 2) ≤
      20 * t * (Real.log (t + 2)) ^ 2 / T := by
    apply (le_div_iff₀ hT).2
    have hLt : T ≤ t * Real.log (t + 2) := by
      calc
        T ≤ t := hTt
        _ ≤ t * Real.log (t + 2) := by
          nlinarith [mul_le_mul_of_nonneg_left hLp ht0.le]
    have hLp0 : 0 ≤ Real.log (t + 2) := zero_le_one.trans hLp
    have hmul := mul_le_mul_of_nonneg_left hLt hLp0
    have hmul20 := mul_le_mul_of_nonneg_left hmul
      (show (0 : ℝ) ≤ 20 by norm_num)
    nlinarith
  change ‖realInsideKernelError chi t N
      (1 + (Real.log t)⁻¹) T‖ ≤ _
  calc
    _ ≤ (∑ n ∈ Finset.Icc 1 M,
          ‖twistedMangoldtCoeff chi n *
            (1 - PerronKernel.kernel (t / n)
              (1 + (Real.log t)⁻¹) T)‖) +
        ‖twistedMangoldtCoeff chi N *
          (1 - PerronKernel.kernel (t / N)
            (1 + (Real.log t)⁻¹) T)‖ := hnorm
    _ ≤ 20 * t * (Real.log (t + 2)) ^ 2 / T +
          20 * t * (Real.log (t + 2)) ^ 2 / T :=
      add_le_add hsafeFinal (htrans.trans htransFinal)
    _ ≤ 100 * t * (Real.log (t + 2)) ^ 2 / T := by
      have hA : 0 ≤ t * (Real.log (t + 2)) ^ 2 / T := by positivity
      calc
        20 * t * (Real.log (t + 2)) ^ 2 / T +
            20 * t * (Real.log (t + 2)) ^ 2 / T =
          40 * (t * (Real.log (t + 2)) ^ 2 / T) := by ring
        _ ≤ 100 * (t * (Real.log (t + 2)) ^ 2 / T) :=
          mul_le_mul_of_nonneg_right (by norm_num) hA
        _ = 100 * t * (Real.log (t + 2)) ^ 2 / T := by ring

/-- A safe outside term, after the single transition coefficient, is
dominated by the certified half-integer shifted-harmonic majorant one index
above `floor(t)`. -/
theorem norm_outside_safe_term_le_halfIntegerMajorant
    {q M n : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT : 0 < T)
    (hMt : t < (M : ℝ)) (hM1 : 1 ≤ M)
    (hn : n ∉ Finset.Icc 1 M) :
    ‖twistedMangoldtCoeff chi n *
        PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T‖ ≤
      (Real.exp 1 * halfIntegerPoint M / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ *
            ((n : ℝ) - halfIntegerPoint M))) := by
  by_cases hn0 : n = 0
  · subst n
    simp [twistedMangoldtCoeff]
  have hnOne : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  have hMn : M < n := by
    by_contra hnot
    exact hn (Finset.mem_Icc.mpr ⟨hnOne, Nat.le_of_not_gt hnot⟩)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlogt : 0 < Real.log t := Real.log_pos ht1
  have hu1 : 1 < halfIntegerPoint M := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    unfold halfIntegerPoint
    linarith
  have hu0 : 0 < halfIntegerPoint M := zero_lt_one.trans hu1
  have htu : t < halfIntegerPoint M := by
    unfold halfIntegerPoint
    linarith
  have hun : halfIntegerPoint M < (n : ℝ) := by
    have hcast : ((M + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.add_one_le_iff.mpr hMn)
    unfold halfIntegerPoint
    norm_num at hcast ⊢
    linarith
  have hy : 0 < t / (n : ℝ) := div_pos ht0 hnpos
  have hy1 : t / (n : ℝ) < 1 :=
    (div_lt_one hnpos).2 (htu.trans hun)
  have hc : 0 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr hlogt
    linarith
  have hk := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hy hy1 hc hT
  have hloginv : 1 / |Real.log (t / (n : ℝ))| ≤
      (n : ℝ) / ((n : ℝ) - t) := by
    have hbase := PerronKernel.abs_log_div_ge_abs_sub_div_max ht0 hnpos
    rw [max_eq_right (htu.trans hun).le,
      abs_of_neg (sub_neg.mpr (htu.trans hun)), neg_sub] at hbase
    have hfrac : 0 < ((n : ℝ) - t) / (n : ℝ) :=
      div_pos (sub_pos.mpr (htu.trans hun)) hnpos
    calc
      1 / |Real.log (t / (n : ℝ))| ≤
          1 / (((n : ℝ) - t) / (n : ℝ)) :=
        one_div_le_one_div_of_le hfrac hbase
      _ = (n : ℝ) / ((n : ℝ) - t) := by
        field_simp [hnpos.ne', (sub_pos.mpr (htu.trans hun)).ne']
  have hid := PaperEdgeOutsidePerronTail.standardEdge_rpow_mul_outsideDistance
    ht1 hnpos (htu.trans hun)
  have hdelta : (Real.log (halfIntegerPoint M))⁻¹ ≤
      (Real.log t)⁻¹ := by
    have hlogle : Real.log t ≤ Real.log (halfIntegerPoint M) :=
      Real.log_le_log ht0 htu.le
    simpa only [one_div] using one_div_le_one_div_of_le hlogt hlogle
  have hnbase : 1 ≤ (n : ℝ) := by exact_mod_cast hnOne
  have hpows : (n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ ≤
      (n : ℝ) ^ (Real.log t)⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hnbase hdelta
  have hdist : (n : ℝ) - halfIntegerPoint M ≤ (n : ℝ) - t := by
    linarith
  have hdenposU : 0 < (n : ℝ) - halfIntegerPoint M := sub_pos.mpr hun
  have hdenposT : 0 < (n : ℝ) - t := sub_pos.mpr (htu.trans hun)
  have hpowposU : 0 < (n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ :=
    Real.rpow_pos_of_pos hnpos _
  have hpowposT : 0 < (n : ℝ) ^ (Real.log t)⁻¹ :=
    Real.rpow_pos_of_pos hnpos _
  have hdencomp :
      (n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ *
          ((n : ℝ) - halfIntegerPoint M) ≤
        (n : ℝ) ^ (Real.log t)⁻¹ * ((n : ℝ) - t) :=
    mul_le_mul hpows hdist hdenposU.le hpowposT.le
  have hfraccomp :
      ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log t)⁻¹ * ((n : ℝ) - t)) ≤
        ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ *
            ((n : ℝ) - halfIntegerPoint M)) := by
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
      (mul_pos hpowposU hdenposU) hdencomp
  have hfactor : Real.exp 1 * t / (Real.pi * T) ≤
      Real.exp 1 * halfIntegerPoint M / (Real.pi * T) := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left htu.le (Real.exp_pos 1).le)
      (mul_pos Real.pi_pos hT).le
  rw [norm_mul]
  have hcoeff := norm_twistedMangoldtCoeff_le chi n
  calc
    ‖twistedMangoldtCoeff chi n‖ *
        ‖PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T‖ ≤
      ArithmeticFunction.vonMangoldt n *
        ((t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) /
          (Real.pi * T * |Real.log (t / (n : ℝ))|)) :=
      mul_le_mul hcoeff hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ = (ArithmeticFunction.vonMangoldt n /
          (Real.pi * T)) *
        ((t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) *
          (1 / |Real.log (t / (n : ℝ))|)) := by ring
    _ ≤ (ArithmeticFunction.vonMangoldt n /
          (Real.pi * T)) *
        ((t / (n : ℝ)) ^ (1 + (Real.log t)⁻¹) *
          ((n : ℝ) / ((n : ℝ) - t))) := by
      gcongr
    _ = (Real.exp 1 * t / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log t)⁻¹ * ((n : ℝ) - t))) := by
      rw [hid]
      field_simp [(mul_pos Real.pi_pos hT).ne', hpowposT.ne', hdenposT.ne']
    _ ≤ (Real.exp 1 * halfIntegerPoint M / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          ((n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ *
            ((n : ℝ) - halfIntegerPoint M))) := by
      exact mul_le_mul hfactor hfraccomp
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (mul_pos hpowposT hdenposT).le)
        (div_nonneg (mul_nonneg (Real.exp_pos 1).le hu0.le)
          (mul_pos Real.pi_pos hT).le)

/-- Summation of the safe outside terms over the complement of `1..M`. -/
theorem norm_coefficientTail_safe_le_shiftedHarmonic
    {q M : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT : 0 < T)
    (hMt : t < (M : ℝ)) (hM1 : 1 ≤ M) :
    ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
        (Finset.Icc 1 M)‖ ≤
      (Real.exp 1 * halfIntegerPoint M / (Real.pi * T)) *
        (2 * Real.log (2 * M + 1 : ℝ) *
            ((harmonic (M + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint M))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint M))⁻¹ / 2)⁻¹))) := by
  let f : {n // n ∉ Finset.Icc 1 M} → ℂ := fun n =>
    twistedMangoldtCoeff chi n *
      PerronKernel.kernel (t / n) (1 + (Real.log t)⁻¹) T
  let g : {n // n ∉ Finset.Icc 1 M} → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n /
      ((n : ℝ) ^ (Real.log (halfIntegerPoint M))⁻¹ *
        ((n : ℝ) - halfIntegerPoint M))
  let K : ℝ := Real.exp 1 * halfIntegerPoint M / (Real.pi * T)
  have hg : Summable g := by
    simpa only [g] using
      PaperEdgeOutsidePerronTail.summable_outsideShiftedHarmonic_standardEdge
        M hM1
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact div_nonneg
      (mul_nonneg (Real.exp_pos 1).le (halfIntegerPoint_pos M).le)
      (mul_pos Real.pi_pos hT).le
  have hpoint : ∀ n, ‖f n‖ ≤ K * g n := by
    intro n
    exact norm_outside_safe_term_le_halfIntegerMajorant
      chi ht2 hT hMt hM1 n.property
  have hKg : Summable fun n => K * g n := hg.mul_left K
  have hnorm : Summable fun n => ‖f n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg (f n)) hpoint hKg
  rw [UniformPsiDeterministicBridge.coefficientTail_eq_tsum_kernels
    chi ((Real.exp_pos 2).trans_le ht2) (Finset.Icc 1 M)]
  change ‖∑' n, f n‖ ≤ K * _
  have hseries :=
    PaperEdgeOutsidePerronTail.tsum_outsideShiftedHarmonic_standardEdge_le
      M hM1
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n, K * g n := hnorm.tsum_le_tsum hpoint hKg
    _ = K * ∑' n, g n := by rw [tsum_mul_left]
    _ ≤ K *
        (2 * Real.log (2 * M + 1 : ℝ) *
            ((harmonic (M + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint M))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint M))⁻¹ / 2)⁻¹))) :=
      mul_le_mul_of_nonneg_left (by simpa only [g] using hseries) hK

/-- Exact tail split isolating the first omitted coefficient. -/
theorem coefficientTail_Icc_eq_transition_add_safe
    {q N : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t c T : ℝ} (ht : 0 < t) (hc : 1 < c) :
    coefficientTail chi t c T (Finset.Icc 1 N) =
      twistedMangoldtCoeff chi (N + 1) *
          PerronKernel.kernel (t / (N + 1)) c T +
        coefficientTail chi t c T (Finset.Icc 1 (N + 1)) := by
  have hN := rightLineIntegral_eq_Icc_kernel_sum_add_tail
    chi (T := T) ht hc N
  have hN1 := rightLineIntegral_eq_Icc_kernel_sum_add_tail
    chi (T := T) ht hc (N + 1)
  have hsum :
      (∑ n ∈ Finset.Icc 1 (N + 1),
          twistedMangoldtCoeff chi n * PerronKernel.kernel (t / n) c T) =
        (∑ n ∈ Finset.Icc 1 N,
          twistedMangoldtCoeff chi n * PerronKernel.kernel (t / n) c T) +
          twistedMangoldtCoeff chi (N + 1) *
            PerronKernel.kernel (t / (N + 1)) c T := by
    simpa using (Finset.sum_Icc_succ_top (a := 1) (b := N)
      (by omega : 1 ≤ N + 1)
      (fun n => twistedMangoldtCoeff chi n *
        PerronKernel.kernel (t / n) c T))
  rw [hsum] at hN1
  apply add_left_cancel (a :=
    ∑ n ∈ Finset.Icc 1 N,
      twistedMangoldtCoeff chi n * PerronKernel.kernel (t / n) c T)
  simpa [add_assoc] using hN.symm.trans hN1

/-- Uniform estimate for the first coefficient omitted by the inclusive
floor prefix. -/
theorem norm_outside_transition_term_le
    {q M : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT2 : 2 ≤ T)
    (hM1 : 1 ≤ M) (hMt : t < (M : ℝ)) (hMupper : (M : ℝ) ≤ t + 2) :
    ‖twistedMangoldtCoeff chi M *
        PerronKernel.kernel (t / M) (1 + (Real.log t)⁻¹) T‖ ≤
      20 * Real.log (t + 2) := by
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM1)
  have hy : 0 < t / (M : ℝ) := div_pos ht0 hMpos
  have hylt : t / (M : ℝ) < 1 := (div_lt_one hMpos).2 hMt
  have hy2 : t / (M : ℝ) ≤ 2 := hylt.le.trans (by norm_num)
  have hc0 : 0 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr hlog
    linarith
  have hc2 : 1 + (Real.log t)⁻¹ ≤ 2 := by
    have hlog2 : 2 ≤ Real.log t :=
      (Real.le_log_iff_exp_le ht0).2 ht2
    have hinv : (Real.log t)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hlog]
      linarith
    linarith
  have hk := norm_kernel_sub_step_le_twenty hy hy2 hc0 hc2 hT2
  have hstep : (if 1 < t / (M : ℝ) then (1 : ℂ) else 0) = 0 := by
    simp [not_lt.mpr hylt.le]
  rw [hstep, sub_zero] at hk
  have hvm : ArithmeticFunction.vonMangoldt M ≤ Real.log (t + 2) :=
    ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log hMpos hMupper)
  rw [norm_mul]
  have hcoeff := norm_twistedMangoldtCoeff_le chi M
  calc
    _ ≤ ArithmeticFunction.vonMangoldt M * 20 :=
      mul_le_mul hcoeff hk (norm_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ Real.log (t + 2) * 20 :=
      mul_le_mul_of_nonneg_right hvm (by norm_num)
    _ = 20 * Real.log (t + 2) := by ring

/-- Scalar collapse of the safe outside series with `M=floor(t)+1`. -/
theorem norm_coefficientTail_safe_floor_succ_le
    {q : ℕ} (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT : 0 < T) :
    ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
        (Finset.Icc 1 (⌊t⌋₊ + 1))‖ ≤
      1000 * t * (Real.log (t + 2)) ^ 2 / T := by
  let N : ℕ := ⌊t⌋₊
  let M : ℕ := N + 1
  let u : ℝ := halfIntegerPoint M
  let L : ℝ := Real.log (t + 2)
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hNle : (N : ℝ) ≤ t := by
    dsimp only [N]
    exact Nat.floor_le ht0.le
  have htM : t < (M : ℝ) := by
    dsimp only [M, N]
    norm_num
    exact Nat.lt_floor_add_one t
  have hM1 : 1 ≤ M := by dsimp only [M]; omega
  have hL : 1 ≤ L := by
    dsimp only [L]
    have he : Real.exp 1 ≤ t + 2 := by
      have : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    exact (Real.le_log_iff_exp_le (by linarith : 0 < t + 2)).2 he
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hMupper : (M : ℝ) ≤ t + 1 := by
    dsimp only [M]
    push_cast
    linarith
  have hu1 : 1 < u := by
    have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
    dsimp only [u, halfIntegerPoint]
    linarith
  have hu0 : 0 < u := zero_lt_one.trans hu1
  have huBound : u ≤ 2 * (t + 2) := by
    dsimp only [u, halfIntegerPoint]
    linarith
  have htwoM : (2 * M + 1 : ℝ) ≤ 2 * (t + 2) := by
    push_cast
    linarith
  have hMp1 : (M + 1 : ℝ) ≤ t + 2 := by
    push_cast
    linarith
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    nlinarith [Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)]
  have hlogDouble : Real.log (2 * (t + 2)) ≤ 2 * L := by
    rw [Real.log_mul (by norm_num) (by linarith : t + 2 ≠ 0)]
    linarith
  have hlu : Real.log u ≤ 2 * L :=
    (Real.log_le_log hu0 huBound).trans hlogDouble
  have hlogTwoM : Real.log (2 * M + 1 : ℝ) ≤ 2 * L := by
    have hp : 0 < (2 * M + 1 : ℝ) := by positivity
    exact (Real.log_le_log hp htwoM).trans hlogDouble
  have hlogMp1 : Real.log (M + 1 : ℝ) ≤ L := by
    have hp : 0 < (M + 1 : ℝ) := by positivity
    exact Real.log_le_log hp hMp1
  have hharm : ((harmonic (M + 1) : ℚ) : ℝ) ≤ 2 * L := by
    calc
      ((harmonic (M + 1) : ℚ) : ℝ) ≤
          1 + Real.log ((M + 1 : ℕ) : ℝ) := harmonic_le_one_add_log (M + 1)
      _ ≤ 1 + L := by norm_num; linarith
      _ ≤ 2 * L := by linarith
  have hharm0 : 0 ≤ ((harmonic (M + 1) : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (Nat.succ_ne_zero M)).le
  have hlu0 : 0 < Real.log u := Real.log_pos hu1
  have hsecondEq :
      (4 / (Real.log u)⁻¹) *
          (1 + (((Real.log u)⁻¹ / 2)⁻¹)) =
        4 * Real.log u * (1 + 2 * Real.log u) := by
    field_simp [hlu0.ne']
  have hsecond :
      (4 / (Real.log u)⁻¹) *
          (1 + (((Real.log u)⁻¹ / 2)⁻¹)) ≤ 40 * L ^ 2 := by
    rw [hsecondEq]
    have hinner : 1 + 2 * Real.log u ≤ 5 * L := by linarith
    have hinner0 : 0 ≤ 1 + 2 * Real.log u := by linarith
    calc
      4 * Real.log u * (1 + 2 * Real.log u) ≤
          4 * (2 * L) * (5 * L) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlu (by norm_num)) hinner
          hinner0 (by positivity)
      _ = 40 * L ^ 2 := by ring
  have hfirst :
      2 * Real.log (2 * M + 1 : ℝ) *
          ((harmonic (M + 1) : ℚ) : ℝ) ≤ 8 * L ^ 2 := by
    calc
      _ ≤ 2 * (2 * L) * (2 * L) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hlogTwoM (by norm_num)) hharm
          hharm0 (by positivity)
      _ = 8 * L ^ 2 := by ring
  have hbracket :
      2 * Real.log (2 * M + 1 : ℝ) *
            ((harmonic (M + 1) : ℚ) : ℝ) +
          (4 / (Real.log u)⁻¹) *
            (1 + (((Real.log u)⁻¹ / 2)⁻¹)) ≤ 48 * L ^ 2 := by
    linarith
  have hbracket0 : 0 ≤
      2 * Real.log (2 * M + 1 : ℝ) *
            ((harmonic (M + 1) : ℚ) : ℝ) +
          (4 / (Real.log u)⁻¹) *
            (1 + (((Real.log u)⁻¹ / 2)⁻¹)) := by
    rw [hsecondEq]
    have hlogTwo0 : 0 ≤ Real.log (2 * M + 1 : ℝ) := by
      apply Real.log_nonneg
      push_cast
      have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
      linarith
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hlogTwo0) hharm0)
      (mul_nonneg (mul_nonneg (by norm_num) hlu0.le) (by linarith))
  have hfactor : Real.exp 1 * u / (Real.pi * T) ≤ 4 * t / T := by
    have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
    have ht2' : (2 : ℝ) ≤ t := by
      have : (2 : ℝ) ≤ Real.exp 2 :=
        Real.exp_one_gt_two.le.trans
          (Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 2))
      exact this.trans ht2
    have hu4t : u ≤ 4 * t := by linarith
    have hnum : Real.exp 1 * u ≤ 12 * t := by
      calc
        Real.exp 1 * u ≤ 3 * u :=
          mul_le_mul_of_nonneg_right he hu0.le
        _ ≤ 3 * (4 * t) :=
          mul_le_mul_of_nonneg_left hu4t (by norm_num)
        _ = 12 * t := by ring
    calc
      Real.exp 1 * u / (Real.pi * T) ≤
          (12 * t) / (Real.pi * T) :=
        div_le_div_of_nonneg_right hnum (mul_pos Real.pi_pos hT).le
      _ ≤ (12 * t) / (3 * T) := by
        exact div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) hT)
          (mul_le_mul_of_nonneg_right Real.pi_gt_three.le hT.le)
      _ = 4 * t / T := by ring
  have hbase := norm_coefficientTail_safe_le_shiftedHarmonic
    chi ht2 hT htM hM1
  change ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
      (Finset.Icc 1 M)‖ ≤ _
  calc
    _ ≤ (Real.exp 1 * halfIntegerPoint M / (Real.pi * T)) *
        (2 * Real.log (2 * M + 1 : ℝ) *
            ((harmonic (M + 1) : ℚ) : ℝ) +
          (4 / (Real.log (halfIntegerPoint M))⁻¹) *
            (1 + (((Real.log (halfIntegerPoint M))⁻¹ / 2)⁻¹))) := hbase
    _ ≤ (4 * t / T) * (48 * L ^ 2) :=
      mul_le_mul hfactor (by simpa only [u] using hbracket)
        hbracket0 (by positivity)
    _ = 192 * t * L ^ 2 / T := by ring
    _ ≤ 1000 * t * L ^ 2 / T := by
      have hA : 0 ≤ t * L ^ 2 / T := by positivity
      calc
        192 * t * L ^ 2 / T = 192 * (t * L ^ 2 / T) := by ring
        _ ≤ 1000 * (t * L ^ 2 / T) :=
          mul_le_mul_of_nonneg_right (by norm_num) hA
        _ = 1000 * t * L ^ 2 / T := by ring

/-- Complete outside coefficient tail at the literal real endpoint. -/
theorem norm_coefficientTail_realEndpoint_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {t T : ℝ} (ht2 : Real.exp 2 ≤ t) (hT2 : 2 ≤ T) (hTt : T ≤ t) :
    ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
        (Finset.Icc 1 ⌊t⌋₊)‖ ≤
      2000 * t * (Real.log (t + 2)) ^ 2 / T := by
  let N : ℕ := ⌊t⌋₊
  let M : ℕ := N + 1
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hlog : 0 < Real.log t := Real.log_pos ht1
  have hc : 1 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr hlog
    linarith
  have hT : 0 < T := lt_of_lt_of_le (by norm_num) hT2
  have htM : t < (M : ℝ) := by
    dsimp only [M, N]
    norm_num
    exact Nat.lt_floor_add_one t
  have hM1 : 1 ≤ M := by dsimp only [M]; omega
  have hMupper : (M : ℝ) ≤ t + 2 := by
    have hNle : (N : ℝ) ≤ t := by
      dsimp only [N]
      exact Nat.floor_le ht0.le
    dsimp only [M]
    push_cast
    linarith
  have hsplit := coefficientTail_Icc_eq_transition_add_safe
    chi (N := N) (T := T) ht0 hc
  have htransition := norm_outside_transition_term_le
    chi ht2 hT2 hM1 htM hMupper
  have hsafe := norm_coefficientTail_safe_floor_succ_le chi ht2 hT
  have hL : 1 ≤ Real.log (t + 2) := by
    have he : Real.exp 1 ≤ t + 2 := by
      have : Real.exp 1 ≤ Real.exp 2 := Real.exp_le_exp.mpr (by norm_num)
      linarith
    exact (Real.le_log_iff_exp_le (by linarith : 0 < t + 2)).2 he
  have htransAbsorb : 20 * Real.log (t + 2) ≤
      1000 * t * (Real.log (t + 2)) ^ 2 / T := by
    apply (le_div_iff₀ hT).2
    have hL0 : 0 ≤ Real.log (t + 2) := zero_le_one.trans hL
    have hLt : T ≤ t * Real.log (t + 2) := by
      exact hTt.trans (by
        nlinarith [mul_le_mul_of_nonneg_left hL ht0.le])
    have hmul := mul_le_mul_of_nonneg_left hLt hL0
    have hmul20 := mul_le_mul_of_nonneg_left hmul
      (show (0 : ℝ) ≤ 20 by norm_num)
    nlinarith
  change ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
      (Finset.Icc 1 N)‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖twistedMangoldtCoeff chi (N + 1) *
          PerronKernel.kernel (t / (N + 1)) (1 + (Real.log t)⁻¹) T‖ +
        ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
          (Finset.Icc 1 (N + 1))‖ := norm_add_le _ _
    _ ≤ 1000 * t * (Real.log (t + 2)) ^ 2 / T +
          1000 * t * (Real.log (t + 2)) ^ 2 / T :=
      add_le_add (by simpa only [M, Nat.cast_add, Nat.cast_one] using
          htransition.trans htransAbsorb)
        (by simpa only [N] using hsafe)
    _ = 2000 * t * (Real.log (t + 2)) ^ 2 / T := by ring

/-- The source-level real-endpoint Perron leaf, with one absolute constant
and the exact quantifier order required by the selected-height contour. -/
theorem uniformRealEndpointPerronBound :
    KoukSelectedHeightRealEndpointFormula.UniformRealEndpointPerronBound := by
  refine ⟨3000, by norm_num, ?_⟩
  intro q _inst chi t T ht2 hT2 hTt
  have ht0 : 0 < t := (Real.exp_pos 2).trans_le ht2
  have ht1 : 1 < t :=
    (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 2)).trans_le ht2
  have hc : 1 < 1 + (Real.log t)⁻¹ := by
    have := inv_pos.mpr (Real.log_pos ht1)
    linarith
  have hsplit := realEndpointPerronError_eq_inside_sub_tail
    chi (T := T) ht0 hc
  have hinside := norm_realInsideKernelError_le chi ht2 hT2 hTt
  have houtside := norm_coefficientTail_realEndpoint_le chi ht2 hT2 hTt
  rw [hsplit]
  calc
    _ ≤ ‖realInsideKernelError chi t ⌊t⌋₊
          (1 + (Real.log t)⁻¹) T‖ +
        ‖coefficientTail chi t (1 + (Real.log t)⁻¹) T
          (Finset.Icc 1 ⌊t⌋₊)‖ := norm_sub_le _ _
    _ ≤ 100 * t * (Real.log (t + 2)) ^ 2 / T +
          2000 * t * (Real.log (t + 2)) ^ 2 / T :=
      add_le_add hinside houtside
    _ ≤ 3000 * t * (Real.log (t + 2)) ^ 2 / T := by
      have hA : 0 ≤ t * (Real.log (t + 2)) ^ 2 / T := by positivity
      calc
        100 * t * (Real.log (t + 2)) ^ 2 / T +
            2000 * t * (Real.log (t + 2)) ^ 2 / T =
          2100 * (t * (Real.log (t + 2)) ^ 2 / T) := by ring
        _ ≤ 3000 * (t * (Real.log (t + 2)) ^ 2 / T) :=
          mul_le_mul_of_nonneg_right (by norm_num) hA
        _ = 3000 * t * (Real.log (t + 2)) ^ 2 / T := by ring

end
end KoukUniformRealEndpointPerronBound

#print axioms KoukUniformRealEndpointPerronBound.realEndpointPerronError_eq_inside_sub_tail
#print axioms KoukUniformRealEndpointPerronBound.norm_kernel_sub_step_le_twenty
#print axioms KoukUniformRealEndpointPerronBound.norm_realInsideKernelError_le
#print axioms KoukUniformRealEndpointPerronBound.norm_coefficientTail_realEndpoint_le
#print axioms KoukUniformRealEndpointPerronBound.uniformRealEndpointPerronBound
