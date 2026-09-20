import PostA5HighStripSplitReductionFromFourthMoment

/-! # Uniform removal of the remaining collar logarithms -/
namespace MAPJutilaCollarNoLogBudget
open Filter Topology
noncomputable section

def collarLogCost (D delta sigma : ℝ) : ℝ :=
  Real.rpow D (2*(1+12*delta)*(1-sigma)) *
    Real.rpow (Real.log D) (4*(1-sigma)) * (1+Real.log D)^6

private theorem shifted_log_pow_six_le {D : ℝ} (hlog : 1 ≤ Real.log D) :
    (1+Real.log D)^6 ≤ 64*(Real.log D)^6 := by
  calc
    _ ≤ (2*Real.log D)^6 := pow_le_pow_left₀ (by linarith) (by linarith) 6
    _ = _ := by ring

private theorem variable_log_factor_le {D sigma : ℝ} (hD : 1 ≤ D)
    (hsigma : sigma ≤ 1) (hlog : Real.log D ≤ Real.rpow D (1/1120)) :
    Real.rpow (Real.log D) (4*(1-sigma)) ≤ Real.rpow D ((1/280)*(1-sigma)) := by
  have hp := Real.rpow_le_rpow (Real.log_nonneg hD) hlog (by linarith : 0 ≤ 4*(1-sigma))
  have hnest : Real.rpow (Real.rpow D (1/1120)) (4*(1-sigma)) =
      Real.rpow D ((1/280)*(1-sigma)) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_mul (zero_le_one.trans hD)]
    congr 1
    ring
  exact hp.trans_eq hnest

theorem collarLogCost_far_le {D sigma : ℝ}
    (hD : 1 ≤ D) (hsigma : sigma ≤ 559/560)
    (hlog : Real.log D ≤ Real.rpow D (1/1120))
    (hfixed : (1+Real.log D)^6 ≤ Real.rpow D (1/156800)) :
    collarLogCost D (1/280) sigma ≤ Real.rpow D ((293/140)*(1-sigma)) := by
  have hv := variable_log_factor_le (sigma := sigma) hD (by linarith) hlog
  have hf : (1+Real.log D)^6 ≤ Real.rpow D ((1/280)*(1-sigma)) :=
    hfixed.trans (Real.rpow_le_rpow_of_exponent_le hD (by linarith))
  have hDp : 0 < D := zero_lt_one.trans_le hD
  unfold collarLogCost
  calc
    _ ≤ Real.rpow D (2*(1+12*(1/280))*(1-sigma)) *
        Real.rpow D ((1/280)*(1-sigma)) * Real.rpow D ((1/280)*(1-sigma)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hDp.le _)) hf
        (pow_nonneg (by linarith [Real.log_nonneg hD]) 6)
        (mul_nonneg (Real.rpow_nonneg hDp.le _) (Real.rpow_nonneg hDp.le _))
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hDp, ← Real.rpow_add hDp]
      congr 1
      ring

theorem collarLogCost_near_le {D sigma omega : ℝ}
    (hD : 1 ≤ D) (hlogOne : 1 ≤ Real.log D) (hsigma : sigma ≤ 1)
    (homega : 0 ≤ omega) (hgap : omega ≤ 1-sigma)
    (hlog : Real.log D ≤ Real.rpow D (1/1120))
    (hlogGap : Real.log D ≤ Real.rpow D (omega/140)) :
    collarLogCost D (1/560) sigma ≤ 64*Real.rpow D ((293/140)*(1-sigma)) := by
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hv := variable_log_factor_le hD hsigma hlog
  have hlog6 : (Real.log D)^6 ≤ Real.rpow D ((3/70)*omega) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log D) hlogGap 6
    have heq : (Real.rpow D (omega/140))^6 = Real.rpow D ((3/70)*omega) := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul_natCast hDp.le]
      congr 1
      norm_num
      ring
    exact h.trans_eq heq
  have hf : (1+Real.log D)^6 ≤ 64*Real.rpow D ((3/70)*(1-sigma)) :=
    (shifted_log_pow_six_le hlogOne).trans ((mul_le_mul_of_nonneg_left hlog6 (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD (by linarith)) (by norm_num)))
  unfold collarLogCost
  calc
    _ ≤ Real.rpow D (2*(1+12*(1/560))*(1-sigma)) *
        Real.rpow D ((1/280)*(1-sigma)) * (64*Real.rpow D ((3/70)*(1-sigma))) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hv (Real.rpow_nonneg hDp.le _)) hf
        (pow_nonneg (by linarith [Real.log_nonneg hD]) 6)
        (mul_nonneg (Real.rpow_nonneg hDp.le _) (Real.rpow_nonneg hDp.le _))
    _ = 64*Real.rpow D ((117/56)*(1-sigma)) := by
      simp only [Real.rpow_eq_pow]
      calc
        _ = 64*(D^(2*(1+12*(1/560))*(1-sigma)) *
            D^((1/280)*(1-sigma)) * D^((3/70)*(1-sigma))) := by ring
        _ = _ := by
          rw [← Real.rpow_add hDp, ← Real.rpow_add hDp]
          congr 1
          congr 1
          ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith)) (by norm_num)

/-- One eventual scale works for both collar choices and every allowed
sigma and gap parameter. No logarithmic factor remains in the conclusion. -/
theorem eventually_collarLogCost_le
    : ∀ᶠ D : ℝ in atTop, ∀ sigma omega : ℝ,
      sigma ≤ 1 → 0 ≤ omega → omega ≤ 1-sigma →
      Real.log D ≤ Real.rpow D (omega/140) →
      collarLogCost D (if sigma ≤ 559/560 then 1/280 else 1/560) sigma ≤
        64*Real.rpow D ((293/140)*(1-sigma)) := by
  have hlog := PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
    1 1 (1/1120) (by norm_num) (by norm_num)
  have hfixed := PostA5HighStripSplitReductionFromFourthMoment.eventually_const_mul_polylog_le_rpow
    64 6 (1/156800) (by norm_num) (by norm_num)
  filter_upwards [hlog,hfixed,eventually_ge_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ))] with D hlogD hfixedD hD hlogOne
  have hlog' : Real.log D ≤ Real.rpow D (1/1120) := by simpa using hlogD
  have hfixed' : (1+Real.log D)^6 ≤ Real.rpow D (1/156800) :=
    (shifted_log_pow_six_le hlogOne).trans (by simpa using hfixedD)
  intro sigma omega hsigma homega hgap hlogGap
  by_cases hfar : sigma ≤ 559/560
  · rw [if_pos hfar]
    have hb := collarLogCost_far_le hD hfar hlog' hfixed'
    have hn := Real.rpow_nonneg (zero_le_one.trans hD) ((293/140)*(1-sigma))
    simp only [Real.rpow_eq_pow] at hb ⊢
    linarith
  · rw [if_neg hfar]
    exact collarLogCost_near_le hD hlogOne hsigma homega hgap hlog' hlogGap
end
end MAPJutilaCollarNoLogBudget
#print axioms MAPJutilaCollarNoLogBudget.eventually_collarLogCost_le
