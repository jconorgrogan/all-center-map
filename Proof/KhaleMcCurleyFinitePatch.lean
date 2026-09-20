import KhaleAppendixBSourceReduction
import KhaleWeakVKConstantCorrection
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
# McCurley patch below the Appendix-B startup height

This is the deterministic comparison used in Khale's Corollary B.2 for
`3 ≤ |t| ≤ exp 11450`.  The closed consumer uses `safeClosedR`, so no unsafe
rounding of McCurley's published constant occurs.
-/

namespace MAPKhaleMcCurleyFinitePatch

open MAPKhaleWeakVKApplication MAPMcCurleyHighImaginaryBridge

noncomputable section

private theorem log_two_lt_seven_tenths :
    Real.log 2 < (7 / 10 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)]
  have h := Real.sum_le_exp_of_nonneg (x := (7 / 10 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem one_lt_log_three : (1 : ℝ) < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
  exact Real.exp_one_lt_three

theorem safeClosedR_mul_log_le_khale_height_term
    {u : ℝ} (hu3 : 3 ≤ u) (huTop : u ≤ Real.exp 11450) :
    safeClosedR * Real.log u ≤
      104 * Real.rpow (Real.log u) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log u)) (1 / 3 : ℝ) := by
  let L := Real.log u
  have huPos : 0 < u := by linarith
  have hLlower : Real.log 3 ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by norm_num) hu3
  have hLone : 1 ≤ L := one_lt_log_three.le.trans hLlower
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hLupper : L ≤ 11450 := by
    dsimp [L]
    calc
      Real.log u ≤ Real.log (Real.exp 11450) :=
        Real.log_le_log huPos huTop
      _ = 11450 := Real.log_exp _
  have hlogLlower : (1 / 20 : ℝ) ≤ Real.log L := by
    have hlogmono : Real.log (Real.log 3) ≤ Real.log L :=
      Real.log_le_log (by linarith [one_lt_log_three]) hLlower
    exact one_twentieth_lt_log_log_three.le.trans hlogmono
  have hlogLpos : 0 < Real.log L :=
    (by norm_num : (0 : ℝ) < 1 / 20).trans_le hlogLlower
  by_cases hsmall : L ≤ Real.exp 1
  · have hLpow : 1 ≤ Real.rpow L (2 / 3 : ℝ) :=
      Real.one_le_rpow hLone (by norm_num)
    have hlogRoot : (1 / 3 : ℝ) ≤
        Real.rpow (Real.log L) (1 / 3 : ℝ) := by
      apply ((pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 3)
        (Real.rpow_nonneg hlogLpos.le _) (by norm_num : (3 : ℕ) ≠ 0))).mp
      have hrootCube :
          (Real.rpow (Real.log L) (1 / 3 : ℝ)) ^ 3 = Real.log L := by
        simpa using Real.rpow_inv_natCast_pow hlogLpos.le
          (by norm_num : (3 : ℕ) ≠ 0)
      change (1 / 3 : ℝ) ^ 3 ≤
        (Real.rpow (Real.log L) (1 / 3 : ℝ)) ^ 3
      rw [hrootCube]
      norm_num
      linarith
    have hprod : (1 / 3 : ℝ) ≤
        Real.rpow L (2 / 3 : ℝ) *
          Real.rpow (Real.log L) (1 / 3 : ℝ) := by
      calc
        (1 / 3 : ℝ) = 1 * (1 / 3) := by ring
        _ ≤ Real.rpow L (2 / 3 : ℝ) *
            Real.rpow (Real.log L) (1 / 3 : ℝ) :=
          mul_le_mul hLpow hlogRoot (by norm_num)
            (Real.rpow_nonneg hLpos.le _)
    have hleft : safeClosedR * L < safeClosedR * 3 := by
      exact mul_lt_mul_of_pos_left (hsmall.trans_lt Real.exp_one_lt_three)
        (by norm_num [safeClosedR])
    calc
      safeClosedR * L ≤ safeClosedR * 3 := hleft.le
      _ ≤ 104 * (1 / 3 : ℝ) := by norm_num [safeClosedR]
      _ ≤ 104 * (Real.rpow L (2 / 3 : ℝ) *
          Real.rpow (Real.log L) (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
      _ = 104 * Real.rpow L (2 / 3 : ℝ) *
          Real.rpow (Real.log L) (1 / 3 : ℝ) := by ring
  · have hLarge : Real.exp 1 ≤ L := le_of_not_ge hsmall
    have hratio : Real.log 11450 / 11450 ≤ Real.log L / L := by
      exact Real.log_div_self_antitoneOn
        hLarge
        (show (11450 : ℝ) ∈ Set.Ici (Real.exp 1) by
          exact Real.exp_one_lt_three.le.trans (by norm_num))
        hLupper
    have hconstant : safeClosedR ^ 3 / 104 ^ 3 ≤
        Real.log 11450 / 11450 := by
      have hnum : safeClosedR ^ 3 / 104 ^ 3 < (9.345 : ℝ) / 11450 := by
        norm_num [safeClosedR]
      have hden : (9.345 : ℝ) / 11450 < Real.log 11450 / 11450 := by
        exact div_lt_div_of_pos_right log_11450_gt (by norm_num)
      exact (hnum.trans hden).le
    have hlinear : safeClosedR ^ 3 * L ≤ 104 ^ 3 * Real.log L := by
      have hc := hconstant.trans hratio
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 104 ^ 3) hLpos] at hc
      nlinarith
    have hL23 :
        (Real.rpow L (2 / 3 : ℝ)) ^ 3 = L ^ 2 := by
      convert (Real.rpow_mul_natCast hLpos.le (2 / 3 : ℝ) 3).symm using 1 <;>
        norm_num [Real.rpow_natCast]
    have hlog13 :
        (Real.rpow (Real.log L) (1 / 3 : ℝ)) ^ 3 = Real.log L := by
      simpa using Real.rpow_inv_natCast_pow hlogLpos.le
        (by norm_num : (3 : ℕ) ≠ 0)
    apply ((pow_le_pow_iff_left₀
      (mul_nonneg (by norm_num [safeClosedR]) hLpos.le)
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
        (Real.rpow_nonneg hlogLpos.le _))
      (by norm_num : (3 : ℕ) ≠ 0))).mp
    rw [mul_pow, mul_pow, mul_pow]
    change safeClosedR ^ 3 * L ^ 3 ≤
      104 ^ 3 * (Real.rpow L (2 / 3 : ℝ)) ^ 3 *
        (Real.rpow (Real.log L) (1 / 3 : ℝ)) ^ 3
    rw [hL23, hlog13]
    nlinarith [sq_nonneg L]

theorem mccurley_denominator_le_khaleWeakDenominatorAbs
    {q : ℕ} {t : ℝ} (hq : 3 ≤ q) (ht3 : 3 ≤ |t|)
    (htTop : |t| ≤ Real.exp 11450) :
    safeClosedR * Real.log (mccurleyScale q t) ≤
      khaleWeakDenominatorAbs q t := by
  let u := |t|
  have hu3 : 3 ≤ u := ht3
  have huPos : 0 < u := by linarith
  have hqReal : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hqPos : (0 : ℝ) < q := by linarith
  have hqu : (9 : ℝ) ≤ (q : ℝ) * u := by nlinarith
  have hscale : mccurleyScale q t ≤ 2 * ((q : ℝ) * u) := by
    unfold mccurleyScale
    apply max_le
    · apply max_le
      · nlinarith
      · simpa only [u] using
          (show (q : ℝ) * |t| ≤ 2 * ((q : ℝ) * |t|) by
            nlinarith [mul_pos hqPos huPos])
    · nlinarith
  have hscalePos : 0 < mccurleyScale q t :=
    zero_lt_one.trans (one_lt_mccurleyScale q t)
  have hlogscale : Real.log (mccurleyScale q t) ≤
      Real.log 2 + Real.log q + Real.log u := by
    have hmono := Real.log_le_log hscalePos hscale
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (mul_ne_zero hqPos.ne' huPos.ne'),
      Real.log_mul hqPos.ne' huPos.ne'] at hmono
    simpa only [add_assoc] using hmono
  have hqlog : 1 ≤ Real.log q := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hqReal
    exact one_lt_log_three.le.trans this
  have hsmallLogs :
      safeClosedR * (Real.log 2 + Real.log q) ≤ 18 * Real.log q := by
    have hlog2 := log_two_lt_seven_tenths.le
    norm_num [safeClosedR] at hlog2 ⊢
    nlinarith
  have huTerm := safeClosedR_mul_log_le_khale_height_term hu3 htTop
  unfold khaleWeakDenominatorAbs
  dsimp only [u] at huTerm ⊢
  calc
    safeClosedR * Real.log (mccurleyScale q t) ≤
        safeClosedR * (Real.log 2 + Real.log q + Real.log |t|) :=
      mul_le_mul_of_nonneg_left hlogscale (by norm_num [safeClosedR])
    _ = safeClosedR * (Real.log 2 + Real.log q) +
        safeClosedR * Real.log |t| := by ring
    _ ≤ 18 * Real.log q +
        104 * Real.rpow (Real.log |t|) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log |t|)) (1 / 3 : ℝ) :=
      add_le_add hsmallLogs huTerm

end
end MAPKhaleMcCurleyFinitePatch

#print axioms MAPKhaleMcCurleyFinitePatch.safeClosedR_mul_log_le_khale_height_term
#print axioms MAPKhaleMcCurleyFinitePatch.mccurley_denominator_le_khaleWeakDenominatorAbs
