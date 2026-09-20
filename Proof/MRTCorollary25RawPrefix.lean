import MRTCorollary25MinSum

/-!
# Raw prefix form of MRT Lemma 2.4(ii)
-/

namespace MAPMRTCorollary25RawPrefix

open scoped BigOperators
open MAPMRTCorollary25 MAPMRTCorollary25PerronCore
open MAPMRTCorollary25TransitionBand MAPMRTCorollary25MinSum
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- The rounded support endpoint and every half-integer prefix inside it remain
within the fixed `C+2` multiple of `X`. -/
theorem halfInteger_prefix_le_supportScale
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X)
    {N : ℕ} (hN : N ≤ Nat.ceil (C * X)) :
    halfIntegerPoint N ≤ (C + 2) * X := by
  have hCX0 : 0 ≤ C * X := mul_nonneg (le_trans zero_lt_one.le hC.le)
    (zero_le_one.trans hX)
  have hceil : ((Nat.ceil (C * X) : ℕ) : ℝ) < C * X + 1 :=
    Nat.ceil_lt_add_one hCX0
  have hcast : (N : ℝ) ≤ Nat.ceil (C * X) := by exact_mod_cast hN
  unfold halfIntegerPoint
  nlinarith [mul_nonneg (by linarith : 0 ≤ C + 1) (by linarith : 0 ≤ X - 1)]

/-- A nonzero supported coefficient lies in the literal source support
interval. -/
theorem support_bounds_of_ne_zero
    {C X : ℝ} {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    {n : ℕ} (hnz : f n ≠ 0) :
    X / C ≤ (n : ℝ) ∧ (n : ℝ) ≤ C * X := by
  constructor
  · by_contra h
    exact hnz (hSupp n (Or.inl (lt_of_not_ge h)))
  · by_contra h
    exact hnz (hSupp n (Or.inr (lt_of_not_ge h)))

/-- Under the source support condition, every relevant Perron ratio has a
fixed `C`-dependent upper bound. -/
theorem halfInteger_ratio_le_supportRatio
    {C X : ℝ} (hC : 1 < C) (hX : 1 ≤ X)
    {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    {N n : ℕ} (hN : N ≤ Nat.ceil (C * X)) (hnz : f n ≠ 0) :
    halfIntegerPoint N / (n : ℝ) ≤ C * (C + 2) := by
  have hb := support_bounds_of_ne_zero hSupp hnz
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (div_pos hXpos hCpos) hb.1
  have hx := halfInteger_prefix_le_supportScale hC hX hN
  apply (div_le_iff₀ hnpos).2
  have hmul := mul_le_mul_of_nonneg_right hb.1 (mul_nonneg hCpos.le (by linarith : 0 ≤ C + 2))
  field_simp [hCpos.ne'] at hmul
  nlinarith

/-- The logarithmic Perron transition is no narrower than the corresponding
half-integer arithmetic transition at scale `(C+2)X`. -/
theorem one_div_T_absLog_le_supportDistance
    {C X T : ℝ} (hC : 1 < C) (hX : 1 ≤ X) (hT : 1 ≤ T)
    {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    {N n : ℕ} (hN : N ≤ Nat.ceil (C * X)) (hnz : f n ≠ 0) :
    1 / (T * |Real.log (halfIntegerPoint N / (n : ℝ))|) ≤
      ((C + 2) * X) /
        (T * |halfIntegerPoint N - (n : ℝ)|) := by
  have hb := support_bounds_of_ne_zero hSupp hnz
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (div_pos hXpos hCpos) hb.1
  have hxpos := halfIntegerPoint_pos N
  have hxBound := halfInteger_prefix_le_supportScale hC hX hN
  have hnBound : (n : ℝ) ≤ (C + 2) * X := by
    nlinarith [hb.2, mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (by linarith : (0 : ℝ) ≤ X)]
  have hmax : max (halfIntegerPoint N) (n : ℝ) ≤ (C + 2) * X :=
    max_le hxBound hnBound
  have hQpos : 0 < (C + 2) * X :=
    mul_pos (by linarith) hXpos
  have hdist : 0 < |halfIntegerPoint N - (n : ℝ)| := by
    rw [abs_pos]
    intro heq
    have htwo : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by
      unfold halfIntegerPoint at heq
      linarith
    have hnat : 2 * N + 1 = 2 * n := by exact_mod_cast htwo
    omega
  have hratioPos : 0 < halfIntegerPoint N / (n : ℝ) := div_pos hxpos hnpos
  have hratioNe : halfIntegerPoint N / (n : ℝ) ≠ 1 := by
    intro h
    have heq : halfIntegerPoint N = (n : ℝ) :=
      (div_eq_one_iff_eq hnpos.ne').mp h
    exact hdist.ne' (abs_eq_zero.mpr (sub_eq_zero.mpr heq))
  have hlogPos : 0 < |Real.log (halfIntegerPoint N / (n : ℝ))| :=
    abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hratioPos hratioNe)
  have hlog := PerronKernel.abs_log_div_ge_abs_sub_div_max hxpos hnpos
  have hmaxpos : 0 < max (halfIntegerPoint N) (n : ℝ) :=
    hxpos.trans_le (le_max_left _ _)
  have hdistOverQ :
      |halfIntegerPoint N - (n : ℝ)| / ((C + 2) * X) ≤
        |Real.log (halfIntegerPoint N / (n : ℝ))| := by
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hmaxpos hmax).trans hlog
  have hcross :
      T * |halfIntegerPoint N - (n : ℝ)| ≤
        ((C + 2) * X) *
          (T * |Real.log (halfIntegerPoint N / (n : ℝ))|) := by
    have := mul_le_mul_of_nonneg_left hdistOverQ hQpos.le
    field_simp [hQpos.ne'] at this
    nlinarith
  apply (div_le_div_iff₀ (mul_pos hTpos hlogPos)
    (mul_pos hTpos hdist)).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcross

/-- Pointwise source transition estimate in literal arithmetic distance. -/
theorem norm_kernel_sub_step_le_supportDistanceMin
    {C X T : ℝ} (hC : 1 < C) (hX : 1 ≤ X) (hT : 1 ≤ T)
    {f : ℕ → ℂ} (hSupp : SupportedNear X C f)
    {N n : ℕ} (hN : N ≤ Nat.ceil (C * X)) (hnz : f n ≠ 0) :
    ‖PerronKernel.kernel (halfIntegerPoint N / (n : ℝ))
        (1 / 2 : ℝ) T -
      (if 1 < halfIntegerPoint N / (n : ℝ) then (1 : ℂ) else 0)‖ ≤
      3 * (1 + Real.sqrt (C * (C + 2))) *
        min 1 (((C + 2) * X) /
          (T * |halfIntegerPoint N - (n : ℝ)|)) := by
  have hb := support_bounds_of_ne_zero hSupp hnz
  have hCpos : 0 < C := lt_trans zero_lt_one hC
  have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (div_pos hXpos hCpos) hb.1
  have hxpos := halfIntegerPoint_pos N
  have hyratio : 0 < halfIntegerPoint N / (n : ℝ) := div_pos hxpos hnpos
  have hyratioNe : halfIntegerPoint N / (n : ℝ) ≠ 1 := by
    intro heq
    have hEq : halfIntegerPoint N = (n : ℝ) := (div_eq_one_iff_eq hnpos.ne').mp heq
    unfold halfIntegerPoint at hEq
    have htwo : (2 : ℝ) * (N : ℝ) + 1 = 2 * (n : ℝ) := by linarith
    have hnat : 2 * N + 1 = 2 * n := by exact_mod_cast htwo
    omega
  have hk := norm_kernel_sub_step_le_transitionMin hyratio hyratioNe
    (halfInteger_ratio_le_supportRatio hC hX hSupp hN hnz) hT
  exact hk.trans (mul_le_mul_of_nonneg_left
    (min_le_min_left 1 (one_div_T_absLog_le_supportDistance
      hC hX hT hSupp hN hnz))
    (mul_nonneg (by norm_num) (by positivity)))

end
end MAPMRTCorollary25RawPrefix

#print axioms MAPMRTCorollary25RawPrefix.one_div_T_absLog_le_supportDistance
#print axioms MAPMRTCorollary25RawPrefix.norm_kernel_sub_step_le_supportDistanceMin
