import WeakVKNearDecay

/-!
# Deterministic conversion of Khale's denominator to the weak-VK MAP gap

This file does not assert a zero-free theorem.  It proves that the literal
denominator in Khale's Appendix-B corollary is eventually bounded by a fixed
multiple of `(log X)^(3/4)` on the MAP range `q <= (log X)^K`, `3 <= t <= X`.
-/

namespace MAPKhaleWeakVKApplication

open Filter Asymptotics

noncomputable section

private theorem eventually_log_le_quarter_rpow :
    ∀ᶠ L : ℝ in atTop, Real.log L ≤ Real.rpow L (1 / 4 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4)).eventuallyLE
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
  have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hrpow0 : 0 ≤ Real.rpow L (1 / 4 : ℝ) :=
    Real.rpow_nonneg (zero_lt_one.trans hL1).le _
  have hL' : Real.log L ≤ |Real.rpow L (1 / 4 : ℝ)| := by
    simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
  rw [abs_of_nonneg hrpow0] at hL'
  exact hL'

private theorem eventually_loglog_le_quarter_log_rpow :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤ Real.rpow (Real.log X) (1 / 4 : ℝ) :=
  Real.tendsto_log_atTop.eventually eventually_log_le_quarter_rpow

/-- On the MAP conductor and height range, Khale's literal Appendix-B
denominator is at most `(18K+104)(log X)^(3/4)` for all sufficiently large
`X`. -/
theorem khaleDenominator_le_log_three_quarters
    (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) (t : ℝ),
      1 ≤ q →
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      3 ≤ t → t ≤ X →
      18 * Real.log q +
          104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
            Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
        (18 * K + 104) * Real.rpow (Real.log X) (3 / 4 : ℝ) := by
  filter_upwards [eventually_loglog_le_quarter_log_rpow,
      eventually_gt_atTop (Real.exp (Real.exp 1))] with X hloglog hX q t hq1 hq ht htx
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hlogX1 : 1 < Real.log X := by
    rw [Real.lt_log_iff_exp_lt hXpos]
    have hexp : Real.exp 1 < Real.exp (Real.exp 1) := by
      exact Real.exp_lt_exp.mpr (Real.one_lt_exp_iff.mpr zero_lt_one)
    exact hexp.trans hX
  have hlogXpos : 0 < Real.log X := zero_lt_one.trans hlogX1
  have htpos : 0 < t := by linarith
  have hlogtpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogt_le : Real.log t ≤ Real.log X :=
    Real.log_le_log htpos htx
  have hloglogt_le : Real.log (Real.log t) ≤ Real.log (Real.log X) :=
    Real.log_le_log hlogtpos hlogt_le
  have hloglogt0 : 0 ≤ Real.log (Real.log t) := by
    have he3 : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans_le (by norm_num)
    have htlog : 1 < Real.log t := (Real.lt_log_iff_exp_lt htpos).2 (he3.trans_le ht)
    exact Real.log_nonneg htlog.le
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq1)
  have hlogq : Real.log q ≤ K * Real.log (Real.log X) := by
    calc
      Real.log q ≤ Real.log (Real.rpow (Real.log X) K) :=
        Real.log_le_log hqpos hq
      _ = K * Real.log (Real.log X) := by
        exact Real.log_rpow hlogXpos K
  have hloglog_quarter :
      Real.log (Real.log X) ≤ Real.rpow (Real.log X) (1 / 4 : ℝ) := hloglog
  have hquarter_le_threequarter :
      Real.rpow (Real.log X) (1 / 4 : ℝ) ≤
        Real.rpow (Real.log X) (3 / 4 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hlogX1.le (by norm_num)
  have hqterm :
      18 * Real.log q ≤ 18 * K * Real.rpow (Real.log X) (3 / 4 : ℝ) := by
    have hKquarter :
        K * Real.log (Real.log X) ≤
          K * Real.rpow (Real.log X) (1 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hloglog_quarter hK
    have hKthree :
        K * Real.rpow (Real.log X) (1 / 4 : ℝ) ≤
          K * Real.rpow (Real.log X) (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hquarter_le_threequarter hK
    calc
      18 * Real.log q ≤ 18 * (K * Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left hlogq (by norm_num)
      _ ≤ 18 * (K * Real.rpow (Real.log X) (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hKquarter (by norm_num)
      _ ≤ 18 * (K * Real.rpow (Real.log X) (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hKthree (by norm_num)
      _ = 18 * K * Real.rpow (Real.log X) (3 / 4 : ℝ) := by ring
  have htwo : Real.rpow (Real.log t) (2 / 3 : ℝ) ≤
      Real.rpow (Real.log X) (2 / 3 : ℝ) := by
    exact Real.rpow_le_rpow hlogtpos.le hlogt_le (by norm_num)
  have hone : Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
      Real.rpow (Real.rpow (Real.log X) (1 / 4 : ℝ)) (1 / 3 : ℝ) := by
    apply Real.rpow_le_rpow hloglogt0
    · exact hloglogt_le.trans hloglog_quarter
    · norm_num
  have hone' : Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
      Real.rpow (Real.log X) (1 / 12 : ℝ) := by
    calc
      Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
      Real.rpow (Real.rpow (Real.log X) (1 / 4 : ℝ)) (1 / 3 : ℝ) := hone
      _ = Real.rpow (Real.log X) ((1 / 4 : ℝ) * (1 / 3 : ℝ)) := by
        exact (Real.rpow_mul hlogXpos.le _ _).symm
      _ = Real.rpow (Real.log X) (1 / 12 : ℝ) := by norm_num
  have hproduct :
      Real.rpow (Real.log t) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
        Real.rpow (Real.log X) (3 / 4 : ℝ) := by
    calc
      _ ≤ Real.rpow (Real.log X) (2 / 3 : ℝ) *
          Real.rpow (Real.log X) (1 / 12 : ℝ) :=
        mul_le_mul htwo hone' (Real.rpow_nonneg hloglogt0 _)
          (Real.rpow_nonneg hlogXpos.le _)
      _ = Real.rpow (Real.log X) ((2 / 3 : ℝ) + (1 / 12 : ℝ)) :=
        (Real.rpow_add hlogXpos _ _).symm
      _ = Real.rpow (Real.log X) (3 / 4 : ℝ) := by norm_num
  have hsecondterm :
      104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
        104 * Real.rpow (Real.log X) (3 / 4 : ℝ) := by
    calc
      104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) =
        104 * (Real.rpow (Real.log t) (2 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ)) := by ring
      _ ≤ 104 * Real.rpow (Real.log X) (3 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hproduct (by norm_num)
  calc
    18 * Real.log q + 104 * Real.rpow (Real.log t) (2 / 3 : ℝ) *
        Real.rpow (Real.log (Real.log t)) (1 / 3 : ℝ) ≤
      18 * K * Real.rpow (Real.log X) (3 / 4 : ℝ) +
        104 * Real.rpow (Real.log X) (3 / 4 : ℝ) := by
          exact add_le_add hqterm hsecondterm
    _ = (18 * K + 104) * Real.rpow (Real.log X) (3 / 4 : ℝ) := by ring

end
end MAPKhaleWeakVKApplication

#print axioms MAPKhaleWeakVKApplication.khaleDenominator_le_log_three_quarters
