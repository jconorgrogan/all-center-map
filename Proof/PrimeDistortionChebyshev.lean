import MertensAnalyticLeaf

/-!
# The Chebyshev--Abel prime-distortion leaf in Shiu's Lemma 4

This file proves the coefficient-preserving estimate needed when the Euler
factors at exponent `1` are moved to exponent `1 - ε`.  The constant is the
elementary Chebyshev constant `log 4`.
-/

namespace ShiuPrimeDistortionChebyshev

open Set
open scoped BigOperators

noncomputable section

/-- The finite prime sum `Σ_{p ≤ y} (log p) p^{-δ}`. -/
def primeLogRpowSum (y : ℕ) (δ : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (y + 1)).filter Nat.Prime,
    Real.log p * (p : ℝ) ^ (-δ)

/-- Local integrability of the Chebyshev function times a real power away
from the origin. -/
theorem integrableOn_rpow_mul_theta (δ x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => t ^ (-δ - 1) * Chebyshev.theta t)
      (Set.Icc 2 x) MeasureTheory.volume := by
  conv =>
    arg 1
    ext t
    rw [Chebyshev.theta, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by norm_num) <|
    ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt ?_
  have ht0 : t ≠ 0 := by linarith [ht.1]
  exact Real.continuousAt_rpow_const t (-δ - 1) (Or.inl ht0)

/-- Abel summation for `Σ_{p ≤ y} (log p) p^{-δ}`, with literal endpoints. -/
theorem primeLogRpowSum_eq_theta_mul_add_integral
    {y : ℕ} (hy : 2 ≤ y) (δ : ℝ) :
    primeLogRpowSum y δ =
      (y : ℝ) ^ (-δ) * Chebyshev.theta (y : ℝ) +
        δ * ∫ t in (2 : ℝ)..y,
          t ^ (-δ - 1) * Chebyshev.theta t := by
  let a : ℕ → ℝ := Set.indicator (setOf Nat.Prime) (fun n ↦ Real.log n)
  rw [primeLogRpowSum]
  trans ∑ n ∈ Finset.Icc 0 y, (n : ℝ) ^ (-δ) * a n
  · rw [Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n.Prime
    · simp [a, h, mul_comm]
    · simp [a, h]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) y,
      DifferentiableAt ℝ (fun z : ℝ => z ^ (-δ)) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (Real.hasDerivAt_rpow_const (Or.inl ht0)).differentiableAt
  have hderivfun : deriv (fun z : ℝ => z ^ (-δ)) =
      fun t => (-δ) * t ^ (-δ - 1) := by
    funext t
    exact Real.deriv_rpow_const t (-δ)
  have hint : MeasureTheory.IntegrableOn
      (deriv (fun z : ℝ => z ^ (-δ)))
      (Set.Icc (2 : ℝ) y) := by
    rw [hderivfun]
    exact ContinuousOn.integrableOn_Icc fun t ht =>
      ContinuousAt.continuousWithinAt <|
        continuousAt_const.mul <|
          Real.continuousAt_rpow_const t (-δ - 1) <|
            Or.inl (by linarith [ht.1])
  have habel := sum_mul_eq_sub_integral_mul₁ a (by simp [a]) (by simp [a])
    (y : ℝ) hdiff hint
  rw [Nat.floor_natCast] at habel
  have hsum (u : ℝ) :
      (∑ k ∈ Finset.Icc 0 ⌊u⌋₊, a k) = Chebyshev.theta u := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : n.Prime <;> simp [a, h]
  have hsumy : (∑ k ∈ Finset.Icc 0 y, a k) = Chebyshev.theta (y : ℝ) := by
    simpa using hsum (y : ℝ)
  rw [habel, hsumy, ← intervalIntegral.integral_of_le (by exact_mod_cast hy)]
  simp_rw [hsum]
  rw [hderivfun]
  rw [show (fun t : ℝ => (-δ) * t ^ (-δ - 1) * Chebyshev.theta t) =
      fun t : ℝ => (-δ) * (t ^ (-δ - 1) * Chebyshev.theta t) by
    funext t
    ring]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Chebyshev's bound controls the distorted prime sum with exactly the
factor `1/ε` that is cancelled by the leading `ε`. -/
theorem epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    {y : ℕ} (hy : 2 ≤ y) :
    ε * primeLogRpowSum y (1 - ε) ≤
      Real.log 4 * (y : ℝ) ^ ε := by
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hy)
  have hyreal : (2 : ℝ) ≤ y := by exact_mod_cast hy
  have hδnonneg : 0 ≤ 1 - ε := by linarith
  rw [primeLogRpowSum_eq_theta_mul_add_integral hy (1 - ε)]
  have hsource : IntervalIntegrable
      (fun t : ℝ => t ^ (-(1 - ε) - 1) * Chebyshev.theta t)
      MeasureTheory.volume 2 y := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hyreal,
      ← integrableOn_Icc_iff_integrableOn_Ioc]
    exact integrableOn_rpow_mul_theta (1 - ε) (y : ℝ)
  have htarget : IntervalIntegrable
      (fun t : ℝ => Real.log 4 * t ^ (ε - 1))
      MeasureTheory.volume 2 y := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hyreal] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ContinuousAt.continuousWithinAt
      (continuousAt_const.mul
        (Real.continuousAt_rpow_const t (ε - 1) (Or.inl ht0)))
  have hintegral :
      (∫ t in (2 : ℝ)..y,
          t ^ (-(1 - ε) - 1) * Chebyshev.theta t) ≤
        ∫ t in (2 : ℝ)..y, Real.log 4 * t ^ (ε - 1) := by
    apply intervalIntegral.integral_mono_on hyreal hsource htarget
    intro t ht
    have htpos : 0 < t := by linarith [ht.1]
    have hpow_nonneg : 0 ≤ t ^ (-(1 - ε) - 1) :=
      Real.rpow_nonneg htpos.le _
    calc
      t ^ (-(1 - ε) - 1) * Chebyshev.theta t ≤
          t ^ (-(1 - ε) - 1) * (Real.log 4 * t) :=
        mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x htpos.le) hpow_nonneg
      _ = Real.log 4 * t ^ (ε - 1) := by
        rw [show -(1 - ε) - 1 = (ε - 1) + (-1) by ring,
          Real.rpow_add htpos, Real.rpow_neg_one]
        field_simp
  have hendpoint :
      (y : ℝ) ^ (-(1 - ε)) * Chebyshev.theta (y : ℝ) ≤
        Real.log 4 * (y : ℝ) ^ ε := by
    have hpow_nonneg : 0 ≤ (y : ℝ) ^ (-(1 - ε)) :=
      Real.rpow_nonneg hypos.le _
    calc
      (y : ℝ) ^ (-(1 - ε)) * Chebyshev.theta (y : ℝ) ≤
          (y : ℝ) ^ (-(1 - ε)) * (Real.log 4 * y) :=
        mul_le_mul_of_nonneg_left
          (Chebyshev.theta_le_log4_mul_x hypos.le) hpow_nonneg
      _ = Real.log 4 * (y : ℝ) ^ ε := by
        rw [show -(1 - ε) = ε + (-1) by ring,
          Real.rpow_add hypos, Real.rpow_neg_one]
        field_simp
  have hint_formula :
      (∫ t in (2 : ℝ)..y, Real.log 4 * t ^ (ε - 1)) =
        Real.log 4 * (((y : ℝ) ^ ε - (2 : ℝ) ^ ε) / ε) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow]
    · ring_nf
    · left
      linarith
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htwopow : 0 ≤ (2 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
  have hypow : 0 ≤ (y : ℝ) ^ ε := Real.rpow_nonneg hypos.le _
  calc
    ε * ((y : ℝ) ^ (-(1 - ε)) * Chebyshev.theta (y : ℝ) +
        (1 - ε) * ∫ t in (2 : ℝ)..y,
          t ^ (-(1 - ε) - 1) * Chebyshev.theta t) ≤
      ε * (Real.log 4 * (y : ℝ) ^ ε +
        (1 - ε) * ∫ t in (2 : ℝ)..y,
          Real.log 4 * t ^ (ε - 1)) := by
        gcongr
    _ = ε * (Real.log 4 * (y : ℝ) ^ ε +
        (1 - ε) * (Real.log 4 *
          (((y : ℝ) ^ ε - (2 : ℝ) ^ ε) / ε))) := by rw [hint_formula]
    _ ≤ Real.log 4 * (y : ℝ) ^ ε := by
      field_simp
      nlinarith

/-- The source-range specialization `0 < ε ≤ 1/4`. -/
theorem epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow_of_le_quarter
    {ε : ℝ} (hε : 0 < ε) (hεquarter : ε ≤ 1 / 4)
    {y : ℕ} (hy : 2 ≤ y) :
    ε * primeLogRpowSum y (1 - ε) ≤
      Real.log 4 * (y : ℝ) ^ ε :=
  epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow hε
    (hεquarter.trans (by norm_num)) hy

/-- Closed-endpoint version, useful when Shiu's parameter happens to be
`r = 1` and hence `ε = 0`. -/
theorem epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow_of_nonneg
    {ε : ℝ} (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    {y : ℕ} (hy : 2 ≤ y) :
    ε * primeLogRpowSum y (1 - ε) ≤
      Real.log 4 * (y : ℝ) ^ ε := by
  rcases hε.eq_or_lt with rfl | hεpos
  · simp [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  · exact epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow hεpos hεone hy

/-- The source restriction `y ≤ z^(1/r)` converts `y^ε` into `r^(1/4)`
for Shiu's exact choice `ε = r log r / (4 log z)`. -/
theorem source_scale_rpow_le_quarter_rpow
    {z r ε : ℝ} {y : ℕ}
    (hz : 1 < z) (hr : 1 ≤ r) (hy : 2 ≤ y)
    (hε : ε = r * Real.log r / (4 * Real.log z))
    (hyz : (y : ℝ) ≤ z ^ r⁻¹) :
    (y : ℝ) ^ ε ≤ r ^ (1 / 4 : ℝ) := by
  have hzpos : 0 < z := zero_lt_one.trans hz
  have hrpos : 0 < r := zero_lt_one.trans_le hr
  have hypos : (0 : ℝ) < y := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hy)
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hεnonneg : 0 ≤ ε := by rw [hε]; positivity
  have hylog : Real.log (y : ℝ) ≤ r⁻¹ * Real.log z := by
    have h := Real.log_le_log hypos hyz
    rwa [Real.log_rpow hzpos] at h
  rw [Real.rpow_def_of_pos hypos, Real.rpow_def_of_pos hrpos,
    Real.exp_le_exp]
  calc
    Real.log (y : ℝ) * ε ≤ (r⁻¹ * Real.log z) * ε :=
      mul_le_mul_of_nonneg_right hylog hεnonneg
    _ = Real.log r * (1 / 4 : ℝ) := by
      rw [hε]
      field_simp

/-- The complete Chebyshev-scale distortion estimate in the variables used by
Shiu: the prime distortion is at most `(log 4) r^(1/4)`. -/
theorem shiu_epsilon_mul_primeLogRpowSum_le_quarter_rpow
    {z r : ℝ} {y : ℕ}
    (hz : 1 < z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log z)
    (hy : 2 ≤ y) (hyz : (y : ℝ) ≤ z ^ r⁻¹) :
    let ε := r * Real.log r / (4 * Real.log z)
    ε * primeLogRpowSum y (1 - ε) ≤
      Real.log 4 * r ^ (1 / 4 : ℝ) := by
  dsimp only
  let ε := r * Real.log r / (4 * Real.log z)
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr
  have hεnonneg : 0 ≤ ε := by dsimp [ε]; positivity
  have hεquarter : ε ≤ 1 / 4 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0 < 4 * Real.log z)).2
    nlinarith
  calc
    ε * primeLogRpowSum y (1 - ε) ≤ Real.log 4 * (y : ℝ) ^ ε :=
      epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow_of_nonneg
        hεnonneg (hεquarter.trans (by norm_num)) hy
    _ ≤ Real.log 4 * r ^ (1 / 4 : ℝ) := by
      gcongr
      exact source_scale_rpow_le_quarter_rpow hz hr hy rfl hyz

/-! ## Absorbing the residual quarter-power loss -/

/-- An explicit Young-inequality absorption of a residual `A r^(1/4)` loss
into Shiu's available `(1/40) r log r` exponent.  The constant is deliberately
unoptimized but completely explicit. -/
theorem linear_quarter_rpow_le_constant_add_one_fortieth_mul_log
    {A r : ℝ} (hr : 1 ≤ r) :
    A * r ^ (1 / 4 : ℝ) ≤
      10 * A ^ 2 + 1 / 40 + (1 / 40 : ℝ) * r * Real.log r := by
  let x : ℝ := r ^ (1 / 4 : ℝ)
  have hr0 : 0 ≤ r := by linarith
  have hx0 : 0 ≤ x := Real.rpow_nonneg hr0 _
  have hx4 : x ^ 4 = r := by
    dsimp [x]
    have h := Real.rpow_inv_natCast_pow hr0
      (show (4 : ℕ) ≠ 0 by norm_num)
    norm_num at h
    exact h
  have hyoung : A * x ≤ 10 * A ^ 2 + x ^ 2 / 40 := by
    nlinarith [sq_nonneg (20 * A - x)]
  have hquadratic : x ^ 2 ≤ (1 + x ^ 4) / 2 := by
    nlinarith [sq_nonneg (x ^ 2 - 1)]
  have hlog : r - 1 ≤ r * Real.log r :=
    Real.self_sub_one_le_mul_log hr0
  rw [hx4] at hquadratic
  change A * x ≤
    10 * A ^ 2 + 1 / 40 + (1 / 40 : ℝ) * r * Real.log r
  nlinarith

end
end ShiuPrimeDistortionChebyshev

#print axioms ShiuPrimeDistortionChebyshev.epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow
#print axioms ShiuPrimeDistortionChebyshev.epsilon_mul_primeLogRpowSum_le_log_four_mul_rpow_of_le_quarter
#print axioms ShiuPrimeDistortionChebyshev.shiu_epsilon_mul_primeLogRpowSum_le_quarter_rpow
#print axioms ShiuPrimeDistortionChebyshev.linear_quarter_rpow_le_constant_add_one_fortieth_mul_log
