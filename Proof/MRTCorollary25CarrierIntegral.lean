import MRTCorollary25RawPrefixEstimate

/-!
# Critical-line carrier integral for MRT Corollary 2.5
-/

namespace MAPMRTCorollary25CarrierIntegral

open scoped BigOperators
open MeasureTheory
open MAPMRTCorollary25PerronCore MixedMeanFrontend
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

set_option maxHeartbeats 2000000

theorem norm_halfPerronCarrier_le
    {x : ℝ} (hx : 0 < x) (u : ℝ) :
    ‖PerronKernel.verticalPower x (1 / 2 : ℝ) u /
        (((1 / 2 : ℝ) : ℂ) + Complex.I * u)‖ ≤
      3 * Real.sqrt x / (1 + |u|) := by
  let d : ℂ := (((1 / 2 : ℝ) : ℂ) + Complex.I * u)
  have hdhalf : (1 / 2 : ℝ) ≤ ‖d‖ := by
    calc
      (1 / 2 : ℝ) = |d.re| := by simp [d]
      _ ≤ ‖d‖ := Complex.abs_re_le_norm d
  have hdu : |u| ≤ ‖d‖ := by
    calc
      |u| = |d.im| := by simp [d]
      _ ≤ ‖d‖ := Complex.abs_im_le_norm d
  have hdpos : 0 < ‖d‖ := lt_of_lt_of_le (by norm_num) hdhalf
  have hweight : 1 + |u| ≤ 3 * ‖d‖ := by nlinarith
  have hweightPos : 0 < 1 + |u| := by positivity
  rw [norm_div, PerronKernel.norm_verticalPower hx]
  rw [show x ^ (1 / 2 : ℝ) = Real.sqrt x by
    simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
      (Real.sqrt_eq_rpow x).symm]
  apply (div_le_div_iff₀ hdpos hweightPos).2
  simpa [d, mul_assoc, mul_left_comm] using
    (mul_le_mul_of_nonneg_left hweight (Real.sqrt_nonneg x))

theorem continuous_finiteHalfLinePolynomial
    (S : Finset ℕ) (f : ℕ → ℂ) :
    Continuous (finiteHalfLinePolynomial S f) := by
  unfold finiteHalfLinePolynomial mellinPhase
  fun_prop

/-- Exact norm factorization, separated from the scalar carrier estimate
so Lean does not normalize a large finite sum inside ordered-ring arithmetic. -/
theorem norm_finitePerronPolynomial_eq_carrier
    (S : Finset ℕ) (f : ℕ → ℂ) (t u : ℝ)
    {x : ℝ} (hx : 0 < x) (hS : ∀ n ∈ S, 1 ≤ n) :
    ‖PerronKernel.finitePerronPolynomial S
        (fun n => f n * mellinPhase n t)
        (fun n => x / n) (1 / 2 : ℝ) u‖ =
      ‖PerronKernel.verticalPower x (1 / 2 : ℝ) u /
          (((1 / 2 : ℝ) : ℂ) + Complex.I * u)‖ *
        ‖finiteHalfLinePolynomial S f (t + u)‖ := by
  rw [finitePerronPolynomial_eq_carrier_mul S f t u hx hS, norm_mul]

/-- Scalar consequence of the carrier bound. -/
theorem carrier_norm_mul_le
    {x : ℝ} (hx : 0 < x) (u z : ℝ) (hz : 0 ≤ z) :
    ‖PerronKernel.verticalPower x (1 / 2 : ℝ) u /
        (((1 / 2 : ℝ) : ℂ) + Complex.I * u)‖ * z ≤
      3 * Real.sqrt x * (z / (1 + |u|)) := by
  have hcarr := norm_halfPerronCarrier_le hx u
  calc
    _ ≤ (3 * Real.sqrt x / (1 + |u|)) * z :=
      mul_le_mul_of_nonneg_right hcarr hz
    _ = 3 * Real.sqrt x * (z / (1 + |u|)) := by ring

/-- Pointwise critical-line majorant for the exact finite Perron polynomial. -/
theorem norm_finitePerronPolynomial_le_critical
    (S : Finset ℕ) (f : ℕ → ℂ) (t u : ℝ)
    {x : ℝ} (hx : 0 < x) (hS : ∀ n ∈ S, 1 ≤ n) :
    ‖PerronKernel.finitePerronPolynomial S
        (fun n => f n * mellinPhase n t)
        (fun n => x / n) (1 / 2 : ℝ) u‖ ≤
      3 * Real.sqrt x *
        (‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|)) := by
  rw [norm_finitePerronPolynomial_eq_carrier S f t u hx hS]
  exact carrier_norm_mul_le hx u _ (norm_nonneg _)

/-- Norm bound for the exact prefix carrier integral. -/
theorem norm_kernelPrefixOn_le_criticalIntegral
    (S : Finset ℕ) (N : ℕ) (f : ℕ → ℂ) (t : ℝ)
    {T : ℝ} (hT : 0 ≤ T) (hS : ∀ n ∈ S, 1 ≤ n) :
    ‖kernelPrefixOn S N f t (1 / 2 : ℝ) T‖ ≤
      3 * Real.sqrt (halfIntegerPoint N) *
        ∫ u in (-T)..T,
          ‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|) := by
  have hx : 0 < halfIntegerPoint N := halfIntegerPoint_pos N
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  rw [kernelPrefixOn_eq_integral S N f t hc]
  have hconst : ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    exact (inv_le_one₀ (mul_pos (by norm_num) Real.pi_pos)).2
      (by nlinarith [Real.pi_gt_three])
  have hi : IntervalIntegrable
      (fun u => PerronKernel.finitePerronPolynomial S
        (fun n => f n * mellinPhase n t)
        (fun n => halfIntegerPoint N / n) (1 / 2 : ℝ) u)
      volume (-T) T := by
    have hcont : Continuous (fun u =>
        PerronKernel.finitePerronPolynomial S
          (fun n => f n * mellinPhase n t)
          (fun n => halfIntegerPoint N / n) (1 / 2 : ℝ) u) := by
      unfold PerronKernel.finitePerronPolynomial
      apply continuous_finsetSum
      intro n hn
      exact (PerronKernel.continuous_verticalIntegrand hc).const_mul _
    exact hcont.intervalIntegrable _ _
  have hmajor : IntervalIntegrable
      (fun u => 3 * Real.sqrt (halfIntegerPoint N) *
        (‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|)))
      volume (-T) T := by
    have hp : Continuous (fun u => finiteHalfLinePolynomial S f (t + u)) :=
      (continuous_finiteHalfLinePolynomial S f).comp
        (continuous_const.add continuous_id)
    have hden : Continuous (fun u : ℝ => 1 + |u|) := by fun_prop
    have hdiv : Continuous (fun u : ℝ =>
        ‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|)) :=
      hp.norm.div hden (by intro u; positivity)
    exact (continuous_const.mul hdiv).intervalIntegrable _ _
  calc
    ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ u in (-T)..T,
          PerronKernel.finitePerronPolynomial S
            (fun n => f n * mellinPhase n t)
            (fun n => halfIntegerPoint N / n) (1 / 2 : ℝ) u‖ ≤
      ‖∫ u in (-T)..T,
          PerronKernel.finitePerronPolynomial S
            (fun n => f n * mellinPhase n t)
            (fun n => halfIntegerPoint N / n) (1 / 2 : ℝ) u‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hconst
    _ ≤ ∫ u in (-T)..T,
        ‖PerronKernel.finitePerronPolynomial S
          (fun n => f n * mellinPhase n t)
          (fun n => halfIntegerPoint N / n) (1 / 2 : ℝ) u‖ :=
      intervalIntegral.norm_integral_le_integral_norm (neg_le_self hT)
    _ ≤ ∫ u in (-T)..T,
        3 * Real.sqrt (halfIntegerPoint N) *
          (‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|)) := by
      apply intervalIntegral.integral_mono_on (neg_le_self hT) hi.norm hmajor
      intro u hu
      exact norm_finitePerronPolynomial_le_critical S f t u hx hS
    _ = 3 * Real.sqrt (halfIntegerPoint N) *
        ∫ u in (-T)..T,
          ‖finiteHalfLinePolynomial S f (t + u)‖ / (1 + |u|) := by
      rw [intervalIntegral.integral_const_mul]

end
end MAPMRTCorollary25CarrierIntegral

#print axioms MAPMRTCorollary25CarrierIntegral.norm_finitePerronPolynomial_le_critical
#print axioms MAPMRTCorollary25CarrierIntegral.norm_kernelPrefixOn_le_criticalIntegral
