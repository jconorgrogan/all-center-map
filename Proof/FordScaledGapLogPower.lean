import FordScaledZeroFreeGeometry

noncomputable section
namespace FordScaledGapLogPower

open Filter
open FordAllLambdaOffsetBound FordGrowthWidth FordScaledDiskGrowth
open FordScaledZeroFreeGeometry

/-- The scalar lower-bound target supplied by the thin-disk zero-free geometry. -/
def localgap (D : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  diskScale (2 * t) /
    (200 * remainderConstant * logBudget D N (2 * t))

private theorem eventually_loglog_le_twentieth_power :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤ Real.rpow (Real.log X) (1 / 20 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 1 / 20)).eventuallyLE
  have hbase : ∀ᶠ L : ℝ in atTop,
      Real.log L ≤ Real.rpow L (1 / 20 : ℝ) := by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
    have hpow0 : 0 ≤ Real.rpow L (1 / 20 : ℝ) :=
      Real.rpow_nonneg (zero_lt_one.trans hL1).le _
    have hL' : Real.log L ≤ |Real.rpow L (1 / 20 : ℝ)| := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
    rw [abs_of_nonneg hpow0] at hL'
    exact hL'
  exact Real.tendsto_log_atTop.eventually hbase

private theorem two_pow_neg_nine_tenths_ge_quarter :
    (1 / 4 : ℝ) ≤ Real.rpow 2 (-(9 / 10 : ℝ)) := by
  have h := Real.rpow_le_rpow_of_exponent_le
    (by norm_num : (1 : ℝ) ≤ 2)
    (by norm_num : -(2 : ℝ) ≤ -(9 / 10 : ℝ))
  convert h using 1 <;> norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The explicit thin-disk ratio has a uniform `(log X)^(-19/20)` lower bound
whenever `N` is at most a fixed power of `log X` and `3 ≤ t ≤ X`. -/
theorem gap_ge_log_power
    (D K : ℝ) (hD : 0 < D) (hK : 0 < K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ᶠ X : ℝ in atTop, ∀ (N : ℕ) (t : ℝ),
        1 ≤ N →
        (N : ℝ) ≤ Real.rpow (Real.log X) K →
        3 ≤ t → t ≤ X →
        c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) ≤ localgap D N t := by
  let B : ℝ := D + 3 * K + 5
  let c : ℝ := savingCoeff / (12800 * remainderConstant * B)
  have hB : 0 < B := by
    dsimp [B]
    nlinarith
  have hc : 0 < c := by
    dsimp [c]
    have hC : 0 < remainderConstant :=
      lt_of_lt_of_le zero_lt_one one_le_remainderConstant
    have hs : 0 < savingCoeff := savingCoeff_pos
    positivity
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_loglog_le_twentieth_power,
      eventually_ge_atTop (Real.exp (Real.exp 1)),
      eventually_ge_atTop (3 : ℝ)] with X hloglog hX hX3
  intro N t hN hNX ht htx
  have hXpos : 0 < X := (Real.exp_pos (Real.exp 1)).trans_le hX
  have hlogX1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact (Real.exp_lt_exp.mpr (by
      exact Real.one_lt_exp_iff.mpr zero_lt_one)).le.trans hX
  have hlogXpos : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hlogX1
  have hloglogX1 : 1 ≤ Real.log (Real.log X) := by
    rw [Real.le_log_iff_exp_le (Real.log_pos (by linarith))]
    exact (Real.le_log_iff_exp_le hXpos).2 hX
  have hloglogX0 : 0 ≤ Real.log (Real.log X) := by linarith
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hN)
  letI : NeZero N := ⟨by omega⟩
  have hlogN : Real.log (N : ℝ) ≤ K * Real.log (Real.log X) := by
    have h := Real.log_le_log hNpos hNX
    calc
      Real.log (N : ℝ) ≤ Real.log (Real.rpow (Real.log X) K) := h
      _ = K * Real.log (Real.log X) := Real.log_rpow hlogXpos K
  have ht2 : 3 ≤ 2 * t := by linarith
  have hT2base : 0 < 2 * t + 3 := by linarith
  have hT2pos : 0 < Real.log (2 * t + 3) := by
    apply Real.log_pos
    linarith
  have hquad : 2 * t + 3 ≤ X ^ (2 : ℕ) := by
    nlinarith
  have hT2 : Real.log (2 * t + 3) ≤ 2 * Real.log X := by
    have h := Real.log_le_log hT2base hquad
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hlogT2 : Real.log (Real.log (2 * t + 3)) ≤
      2 * Real.log (Real.log X) := by
    have h := Real.log_le_log hT2pos hT2
    have hmul : Real.log (2 * Real.log X) =
        Real.log 2 + Real.log (Real.log X) := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogXpos.ne']
    rw [hmul] at h
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      norm_num at h
      exact h
    linarith
  have hM : logBudget D N (2 * t) ≤ B * Real.rpow (Real.log X) (1 / 20 : ℝ) := by
    unfold logBudget
    have hlin : 1 + D + 3 * Real.log (N : ℝ) +
        2 * Real.log (Real.log (2 * t + 3)) ≤ B * Real.log (Real.log X) := by
      dsimp [B]
      nlinarith
    calc
      1 + D + 3 * Real.log (N : ℝ) +
          2 * Real.log (Real.log (2 * t + 3)) ≤
          B * Real.log (Real.log X) := hlin
      _ ≤ B * Real.rpow (Real.log X) (1 / 20 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hloglog hB.le
  have hT2le : Real.log (2 * t + 3) ≤ 2 * Real.log X := hT2
  have hscale :
      savingCoeff / 64 * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) ≤
        diskScale (2 * t) := by
    unfold diskScale widthEta
    have hpow := Real.rpow_le_rpow_of_nonpos hT2pos hT2le
      (by norm_num : -(9 / 10 : ℝ) ≤ 0)
    have hpow2 :
        (1 / 4 : ℝ) * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) ≤
          Real.rpow (2 * Real.log X) (-(9 / 10 : ℝ)) := by
      calc
        (1 / 4 : ℝ) * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) ≤
            Real.rpow 2 (-(9 / 10 : ℝ)) *
              Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
          exact mul_le_mul_of_nonneg_right two_pow_neg_nine_tenths_ge_quarter
            (Real.rpow_nonneg (show (0 : ℝ) ≤ Real.log X by linarith) _)
        _ = Real.rpow (2 * Real.log X) (-(9 / 10 : ℝ)) := by
          symm
          exact (Real.mul_rpow (z := -(9 / 10 : ℝ))
            (by norm_num : (0 : ℝ) ≤ 2)
            (show (0 : ℝ) ≤ Real.log X by linarith))
    calc
      savingCoeff / 64 * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) =
          (savingCoeff / 16) *
            ((1 / 4 : ℝ) * Real.rpow (Real.log X) (-(9 / 10 : ℝ))) := by ring
      _ ≤ (savingCoeff / 16) *
            Real.rpow (2 * Real.log X) (-(9 / 10 : ℝ)) := by
        have hs : 0 ≤ savingCoeff := savingCoeff_pos.le
        exact mul_le_mul_of_nonneg_left hpow2 (by positivity)
      _ ≤ (savingCoeff / 16) *
            Real.rpow (Real.log (2 * t + 3)) (-(9 / 10 : ℝ)) := by
        have hs : 0 ≤ savingCoeff := savingCoeff_pos.le
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = diskScale (2 * t) := by
        unfold diskScale widthEta
        change savingCoeff / 16 * Real.rpow (Real.log (2 * t + 3))
            (-(9 / 10 : ℝ)) =
          savingCoeff * Real.rpow (Real.log (2 * t + 3))
            (-(9 / 10 : ℝ)) / 16
        ring
  have hdenpos : 0 < 200 * remainderConstant * logBudget D N (2 * t) := by
    have hbudget : 0 < logBudget D N (2 * t) := by
      exact lt_of_lt_of_le zero_lt_one (one_le_logBudget hD N ht2)
    have hC : 0 < remainderConstant :=
      lt_of_lt_of_le zero_lt_one one_le_remainderConstant
    positivity
  have hpowpos : 0 < Real.rpow (Real.log X) (1 / 20 : ℝ) :=
    Real.rpow_pos_of_pos hlogXpos _
  have hC : 0 < remainderConstant :=
    lt_of_lt_of_le zero_lt_one one_le_remainderConstant
  have hs : 0 < savingCoeff := savingCoeff_pos
  have hmain :
      c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
          (200 * remainderConstant * logBudget D N (2 * t)) ≤
        savingCoeff / 64 * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
    have hleft : 0 ≤ c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
        (200 * remainderConstant) := by
      exact mul_nonneg
        (mul_nonneg hc.le (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Real.log X) _))
        (mul_nonneg (by norm_num) hC.le)
    have hmul0 := mul_le_mul_of_nonneg_left hM hleft
    have hmul :
        c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
            (200 * remainderConstant * logBudget D N (2 * t)) ≤
          c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
            (200 * remainderConstant *
              (B * Real.rpow (Real.log X) (1 / 20 : ℝ))) := by
      convert hmul0 using 1 <;> ring
    have hpowmerge :
        Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
            Real.rpow (Real.log X) (1 / 20 : ℝ) =
          Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
      calc
        Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
              Real.rpow (Real.log X) (1 / 20 : ℝ) =
            Real.rpow (Real.log X)
              (-(19 / 20 : ℝ) + (1 / 20 : ℝ)) :=
          (Real.rpow_add hlogXpos _ _).symm
        _ = Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
          congr 1 <;> ring
    calc
      c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
          (200 * remainderConstant * logBudget D N (2 * t)) ≤
      c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
            (200 * remainderConstant *
              (B * Real.rpow (Real.log X) (1 / 20 : ℝ))) := hmul
      _ = savingCoeff / 64 * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
        calc
          c * Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
              (200 * remainderConstant *
                (B * Real.rpow (Real.log X) (1 / 20 : ℝ))) =
              savingCoeff / 64 *
                (Real.rpow (Real.log X) (-(19 / 20 : ℝ)) *
                  Real.rpow (Real.log X) (1 / 20 : ℝ)) := by
            dsimp [c]
            field_simp [ne_of_gt hC, ne_of_gt hB]
            ring
          _ = savingCoeff / 64 * Real.rpow (Real.log X) (-(9 / 10 : ℝ)) := by
            rw [hpowmerge]
  unfold localgap
  apply (le_div_iff₀ hdenpos).2
  exact hmain.trans hscale

end FordScaledGapLogPower
#print axioms FordScaledGapLogPower.gap_ge_log_power
