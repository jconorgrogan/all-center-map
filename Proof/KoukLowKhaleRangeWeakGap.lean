import KoukTheorem12ThreeGlobal

/-!
# The Kouk collar on the part of the Khale high range that is unavailable

If either Khale's fixed startup height or its auxiliary
`q^(1/100000) <= |t|` condition fails, then on a polylogarithmic conductor
range the arithmetic scale is itself polylogarithmic.  Consequently the
reciprocal-log collar from Koukoulopoulos Theorem 12.3 dominates the weak-VK
mesh `log(X)^(-3/4)`.
-/

namespace MAPKoukLowKhaleRangeWeakGap

open Filter Asymptotics
open MAPLocalZeroWindow

noncomputable section

private theorem eventually_loglog_le_threeQuarter_log_rpow :
    ∀ᶠ X : ℝ in atTop,
      Real.log (Real.log X) ≤
        Real.rpow (Real.log X) (3 / 4 : ℝ) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
      (by norm_num : (0 : ℝ) < 3 / 4)).eventuallyLE
  exact Real.tendsto_log_atTop.eventually (by
    filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hL hL1
    have hlog0 : 0 ≤ Real.log L := Real.log_nonneg hL1.le
    have hrpow0 : 0 ≤ Real.rpow L (3 / 4 : ℝ) :=
      Real.rpow_nonneg (zero_lt_one.trans hL1).le _
    have hL' : Real.log L ≤ |Real.rpow L (3 / 4 : ℝ)| := by
      simpa [Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hlog0] using hL
    rwa [abs_of_nonneg hrpow0] at hL')

/-- Exact scalar bridge used in the regular-high split.  No zero-free input
occurs in this theorem. -/
theorem eventually_weakGap_le_koukGap_of_not_khale_high_range
    (K : ℝ) (hK : 0 < K) :
    ∀ᶠ X : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (t : ℝ),
      (q : ℝ) ≤ Real.rpow (Real.log X) K →
      ¬ (Real.exp 11450 ≤ |t| ∧
        Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ |t|) →
      (1 / (100000000000 * (Real.log (Real.exp 11450 + 3) + 2 * K))) *
          Real.rpow (Real.log X) (-(3 / 4 : ℝ)) ≤
        1 / (100000000000 * Real.log (arithmeticScale q t)) := by
  filter_upwards [eventually_loglog_le_threeQuarter_log_rpow,
      eventually_gt_atTop (Real.exp (Real.exp 1))] with
      X hthreeQuarter hX q _inst t hq hnot
  let L := Real.log X
  let P := Real.rpow L K
  let E := Real.exp 11450
  let C := Real.log (E + 3) + 2 * K
  have hXpos : 0 < X := (Real.exp_pos _).trans hX
  have hlogXexp : Real.exp 1 < L := by
    dsimp [L]
    rw [Real.lt_log_iff_exp_lt hXpos]
    exact hX
  have hLone : 1 < L :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).trans hlogXexp
  have hlogLpos : 0 < Real.log L := by
    exact Real.log_pos hLone
  have hPone : 1 ≤ P := by
    dsimp [P]
    exact Real.one_le_rpow hLone.le hK.le
  have hPpos : 0 < P := zero_lt_one.trans_le hPone
  have hqone : (1 : ℝ) ≤ q := by
    exact_mod_cast NeZero.one_le (n := q)
  have hqpos : (0 : ℝ) < q := zero_lt_one.trans_le hqone
  have hqpow : Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ (q : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hqone
      (show (1 / 100000 : ℝ) ≤ 1 by norm_num)
    simpa only [Real.rpow_one] using this
  have ht : |t| ≤ E + (q : ℝ) := by
    by_cases hheight : E ≤ |t|
    · have hqheight : ¬ Real.rpow (q : ℝ) (1 / 100000 : ℝ) ≤ |t| :=
        fun h => hnot ⟨by simpa only [E] using hheight, h⟩
      dsimp [E]
      linarith [hqpow, Real.exp_pos 11450]
    · have hheight' : |t| < E := lt_of_not_ge hheight
      dsimp [E]
      linarith [show (0 : ℝ) ≤ q by positivity]
  have hEP : E + (q : ℝ) + 2 ≤ (E + 3) * P := by
    have hqP : (q : ℝ) ≤ P := by simpa only [P, L] using hq
    have hconst : E + 2 ≤ (E + 2) * P := by
      exact (le_mul_of_one_le_right (by positivity) hPone)
    nlinarith
  have htP : |t| + 2 ≤ (E + 3) * P := by linarith
  have ht2pos : 0 < |t| + 2 := by positivity
  have hEPpos : 0 < (E + 3) * P := by
    dsimp [E]
    positivity
  have hlogq : Real.log (q : ℝ) ≤ K * Real.log L := by
    have hmono : Real.log (q : ℝ) ≤ Real.log P :=
      Real.log_le_log hqpos (by simpa only [P, L] using hq)
    have hpLog : Real.log P = K * Real.log L := by
      dsimp [P]
      exact Real.log_rpow (zero_lt_one.trans hLone) K
    rwa [hpLog] at hmono
  have hlogt : Real.log (|t| + 2) ≤
      Real.log (E + 3) + K * Real.log L := by
    have hmono := Real.log_le_log ht2pos htP
    have hprod : Real.log ((E + 3) * P) =
        Real.log (E + 3) + K * Real.log L := by
      rw [Real.log_mul (by positivity : E + 3 ≠ 0) hPpos.ne']
      congr 1
      dsimp [P]
      exact Real.log_rpow (zero_lt_one.trans hLone) K
    rwa [hprod] at hmono
  have hlogScale : Real.log (arithmeticScale q t) ≤
      Real.log (E + 3) + 2 * K * Real.log L := by
    unfold arithmeticScale
    rw [Real.log_mul hqpos.ne' ht2pos.ne']
    linarith
  have hlogCpos : 0 < Real.log (E + 3) := by
    apply Real.log_pos
    dsimp [E]
    nlinarith [Real.exp_pos 11450]
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hpowPos : 0 < Real.rpow L (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hLone) _
  have hpowOne : 1 ≤ Real.rpow L (3 / 4 : ℝ) :=
    Real.one_le_rpow hLone.le (by norm_num)
  have hlogUpper : Real.log (arithmeticScale q t) ≤
      C * Real.rpow L (3 / 4 : ℝ) := by
    have hconst : Real.log (E + 3) ≤
        Real.log (E + 3) * Real.rpow L (3 / 4 : ℝ) :=
      le_mul_of_one_le_right hlogCpos.le hpowOne
    have hlogL : Real.log L ≤ Real.rpow L (3 / 4 : ℝ) := by
      simpa only [L] using hthreeQuarter
    have hKterm : 2 * K * Real.log L ≤
        2 * K * Real.rpow L (3 / 4 : ℝ) :=
      mul_le_mul_of_nonneg_left hlogL (by positivity)
    have hsum := add_le_add hconst hKterm
    exact hlogScale.trans (by
      dsimp [C]
      rw [add_mul]
      simpa only [mul_assoc] using hsum)
  have hscalePos : 0 < arithmeticScale q t := by
    unfold arithmeticScale
    positivity
  have hlogScalePos : 0 < Real.log (arithmeticScale q t) := by
    have htwo : (2 : ℝ) ≤ arithmeticScale q t := by
      unfold arithmeticScale
      have hfactor : (2 : ℝ) ≤ |t| + 2 := by
        linarith [abs_nonneg t]
      have hm := mul_le_mul hqone hfactor
        (by norm_num : (0 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ q)
      norm_num at hm ⊢
      exact hm
    exact Real.log_pos (one_lt_two.trans_le htwo)
  have hdenUpper :
      100000000000 * Real.log (arithmeticScale q t) ≤
        100000000000 * C * Real.rpow L (3 / 4 : ℝ) := by
    calc
      _ ≤ 100000000000 *
          (C * Real.rpow L (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogUpper (by norm_num)
      _ = _ := by ring
  have hinv :
      1 / (100000000000 * C * Real.rpow L (3 / 4 : ℝ)) ≤
        1 / (100000000000 * Real.log (arithmeticScale q t)) := by
    exact one_div_le_one_div_of_le
      (mul_pos (by norm_num) hlogScalePos) hdenUpper
  have hid :
      (1 / (100000000000 * C)) * Real.rpow L (-(3 / 4 : ℝ)) =
        1 / (100000000000 * C * Real.rpow L (3 / 4 : ℝ)) := by
    have hneg := Real.rpow_neg (zero_lt_one.trans hLone).le (3 / 4 : ℝ)
    calc
      (1 / (100000000000 * C)) * Real.rpow L (-(3 / 4 : ℝ)) =
          (1 / (100000000000 * C)) *
            (Real.rpow L (3 / 4 : ℝ))⁻¹ :=
        congrArg (fun z : ℝ => (1 / (100000000000 * C)) * z) hneg
      _ = _ := by field_simp
  change (1 / (100000000000 * C)) *
    Real.rpow L (-(3 / 4 : ℝ)) ≤ _
  rw [hid]
  exact hinv

end

end MAPKoukLowKhaleRangeWeakGap

#print axioms MAPKoukLowKhaleRangeWeakGap.eventually_weakGap_le_koukGap_of_not_khale_high_range
