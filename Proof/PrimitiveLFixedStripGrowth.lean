import MellinDetectorLeaf
import Mathlib.NumberTheory.ZetaValues
import LocalZeroWindowJensen

/-!
# The quantitative primitive-L leaf behind Appendix (A.5)

This file proves the absolutely-convergent side of the fixed-disk argument,
including a uniform quantitative lower bound at the Jensen center.  It also
records the exact real-part range of the optimized outer circle.  No local
zero count and no fixed-strip growth estimate is declared as an axiom.
-/

open Complex LSeries
open scoped ArithmeticFunction.Moebius

namespace MAPPrimitiveLFixedStrip

theorem norm_LSeries_two_add_le_zeta_two
    (f : ℕ → ℂ) (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) (y : ℝ) :
    ‖LSeries f (2 + I * y)‖ ≤ Real.pi ^ 2 / 6 := by
  have hs : 1 < (2 + I * y : ℂ).re := by simp
  have hsum : Summable (LSeries.term f (2 + I * y)) :=
    LSeriesSummable_of_bounded_of_one_lt_re hf hs
  unfold LSeries
  calc
    ‖∑' n : ℕ, LSeries.term f (2 + I * y) n‖ ≤
        ∑' n : ℕ, ‖LSeries.term f (2 + I * y) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
      apply Summable.tsum_le_tsum _ hsum.norm hasSum_zeta_two.summable
      intro n
      rw [LSeries.norm_term_eq]
      split_ifs with hn
      · simp [hn]
      · simpa using div_le_div_of_nonneg_right (hf n hn) (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ))
    _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq

theorem norm_LSeries_two_add_lt_three
    (f : ℕ → ℂ) (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) (y : ℝ) :
    ‖LSeries f (2 + I * y)‖ < 3 := by
  refine (norm_LSeries_two_add_le_zeta_two f hf y).trans_lt ?_
  nlinarith [Real.pi_pos.le, Real.pi_lt_four]

/-- The same absolute-convergence estimate throughout `Re s ≥ 2`. -/
theorem norm_LSeries_lt_three_of_two_le_re
    (f : ℕ → ℂ) (hf : ∀ n ≠ 0, ‖f n‖ ≤ 1) {s : ℂ}
    (hs : 2 ≤ s.re) : ‖LSeries f s‖ < 3 := by
  have htwo : 1 < (2 : ℂ).re := by norm_num
  have hsone : 1 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hsumTwo : Summable (LSeries.term f (2 : ℂ)) :=
    LSeriesSummable_of_bounded_of_one_lt_re hf htwo
  have hsumS : Summable (LSeries.term f s) :=
    LSeriesSummable_of_bounded_of_one_lt_re hf hsone
  have hsumNorm :
      (∑' n : ℕ, ‖LSeries.term f s n‖) ≤ Real.pi ^ 2 / 6 := by
    calc
      (∑' n : ℕ, ‖LSeries.term f s n‖) ≤
          ∑' n : ℕ, ‖LSeries.term f (2 : ℂ) n‖ := by
        exact Summable.tsum_le_tsum
          (fun n => LSeries.norm_term_le_of_re_le_re f hs n)
          hsumS.norm hsumTwo.norm
      _ ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 := by
        apply Summable.tsum_le_tsum _ hsumTwo.norm hasSum_zeta_two.summable
        intro n
        rw [LSeries.norm_term_eq]
        split_ifs with hn
        · simp [hn]
        · simpa using div_le_div_of_nonneg_right (hf n hn)
            (by positivity : 0 ≤ (n : ℝ) ^ (2 : ℝ))
      _ = Real.pi ^ 2 / 6 := hasSum_zeta_two.tsum_eq
  refine (norm_tsum_le_tsum_norm hsumS.norm).trans_lt
    (hsumNorm.trans_lt ?_)
  nlinarith [Real.pi_pos.le, Real.pi_lt_four]

variable {N : ℕ} [NeZero N]

omit [NeZero N] in theorem twist_mu_norm_le_one
    (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖((fun n : ℕ => χ n) * (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))) n‖ ≤ 1 := by
  simp only [Pi.mul_apply, norm_mul, norm_intCast]
  have hχ := χ.norm_le_one n
  have hμ := ArithmeticFunction.abs_moebius_le_one (n := n)
  have hμC : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast hμ
  exact mul_le_one₀ hχ (abs_nonneg _) hμC

theorem one_third_le_norm_LFunction_two_add
    (χ : DirichletCharacter ℂ N) (y : ℝ) :
    (1 / 3 : ℝ) ≤ ‖DirichletCharacter.LFunction χ (2 + I * y)‖ := by
  have hs : 1 < (2 + I * y : ℂ).re := by simp
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  let g : ℕ → ℂ := (fun n : ℕ => χ n) *
    (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ))
  have hginv : LSeries (fun n : ℕ => χ n) (2 + I * y) *
      LSeries g (2 + I * y) = 1 := by
    simpa [g] using DirichletCharacter.LSeries.mul_mu_eq_one χ hs
  have hg : ‖LSeries g (2 + I * y)‖ ≤ 3 :=
    (norm_LSeries_two_add_lt_three g (fun n _ => twist_mu_norm_le_one χ n) y).le
  have hone :
      1 ≤ 3 * ‖LSeries (fun n : ℕ => χ n) (2 + I * y)‖ := by
    calc
      1 = ‖LSeries (fun n : ℕ => χ n) (2 + I * y) *
          LSeries g (2 + I * y)‖ := by rw [hginv, norm_one]
      _ = ‖LSeries g (2 + I * y)‖ *
          ‖LSeries (fun n : ℕ => χ n) (2 + I * y)‖ := by
        rw [norm_mul, mul_comm]
      _ ≤ 3 * ‖LSeries (fun n : ℕ => χ n) (2 + I * y)‖ := by
        gcongr
  linarith

theorem norm_LFunction_lt_three_of_two_le_re
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DirichletCharacter.LFunction χ s‖ < 3 := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ
    (lt_of_lt_of_le (by norm_num) hs)]
  exact norm_LSeries_lt_three_of_two_le_re (fun n : ℕ => χ n)
    (fun n _ => χ.norm_le_one n) hs

end MAPPrimitiveLFixedStrip

namespace MAPPrimitiveLFixedStrip

open DirichletZeros MAPLocalZeroWindow

variable {N : ℕ} [NeZero N]

theorem one_third_le_norm_regularizedLFunction_jensenCenter
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t : ℝ) :
    (1 / 3 : ℝ) ≤ ‖regularizedLFunction χ (jensenCenter t)‖ := by
  rw [regularizedLFunction, if_neg hχ]
  simpa [jensenCenter, mul_comm] using
    one_third_le_norm_LFunction_two_add χ (t + 1 / 2)

theorem jensenOuterCircle_re_mem {t : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|) :
    (3 / 10 : ℝ) ≤ z.re ∧ z.re ≤ 37 / 10 := by
  have hdist : dist z (jensenCenter t) = 17 / 10 := by
    rw [Metric.mem_sphere] at hz
    norm_num [jensenOuterRadius] at hz
    exact hz
  have hre : |z.re - 2| ≤ 17 / 10 := by
    calc
      |z.re - 2| = |(z - jensenCenter t).re| := by simp
      _ ≤ ‖z - jensenCenter t‖ := Complex.abs_re_le_norm _
      _ = 17 / 10 := by simpa [dist_eq_norm] using hdist
  rw [abs_le] at hre
  constructor <;> linarith

theorem one_le_arithmeticScale (t : ℝ) :
    1 ≤ arithmeticScale N t := by
  have hNnat : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast hNnat
  unfold arithmeticScale
  nlinarith [abs_nonneg t]

/-- On the right-hand part of the outer Jensen circle, absolute convergence
already gives a uniform bound.  Thus the only missing growth estimate is on
the left arc `3/10 ≤ Re z < 2`. -/
theorem regularizedLFunction_lt_three_on_outerCircle_right
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {t : ℝ} {z : ℂ}
    (_hz : z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|)
    (hzre : 2 ≤ z.re) :
    ‖regularizedLFunction χ z‖ < 3 := by
  rw [regularizedLFunction, if_neg hχ]
  exact norm_LFunction_lt_three_of_two_le_re χ hzre

/-- Exact reduction of the full outer-circle premise to the genuinely hard
left arc.  This is reusable by the A.4 contour work: no estimate is needed
here for `Re z ≥ 2`. -/
theorem outerCircle_bound_of_leftArc_bound
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {t M : ℝ}
    (hM : 3 ≤ M)
    (hleft : ∀ z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|,
      z.re < 2 → ‖regularizedLFunction χ z‖ ≤ M) :
    ∀ z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|,
      ‖regularizedLFunction χ z‖ ≤ M := by
  intro z hz
  by_cases hre : z.re < 2
  · exact hleft z hz hre
  · exact (regularizedLFunction_lt_three_on_outerCircle_right χ hχ hz
      (le_of_not_gt hre)).le.trans hM

/-- Jensen with the center denominator discharged quantitatively.  The only
analytic premise left is an upper bound on the left arc of the explicit
outer circle. -/
theorem closedUnitWindowCount_le_log_three_mul_of_leftArc_bound
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t M : ℝ}
    (hσ : 1 / 2 ≤ σ) (hM : 3 ≤ M)
    (hleft : ∀ z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|,
      z.re < 2 → ‖regularizedLFunction χ z‖ ≤ M) :
    (closedUnitWindowCount χ σ t : ℝ) ≤
      Real.log (3 * M) /
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
  have hMone : 1 ≤ M := by linarith
  have hcenter := one_third_le_norm_regularizedLFunction_jensenCenter χ hχ t
  have hcenterPos : 0 < ‖regularizedLFunction χ (jensenCenter t)‖ := by
    linarith
  have hratio :
      M / ‖regularizedLFunction χ (jensenCenter t)‖ ≤ 3 * M := by
    apply (div_le_iff₀ hcenterPos).2
    have hone : 1 ≤ 3 * ‖regularizedLFunction χ (jensenCenter t)‖ := by
      linarith
    have := mul_le_mul_of_nonneg_left hone (by linarith : 0 ≤ M)
    nlinarith
  have hlog :
      Real.log (M / ‖regularizedLFunction χ (jensenCenter t)‖) ≤
        Real.log (3 * M) := by
    exact Real.log_le_log (div_pos (by linarith) hcenterPos) hratio
  exact (closedUnitWindowCount_le_jensen χ hσ hMone
    (outerCircle_bound_of_leftArc_bound χ hχ hM hleft)).trans
      (div_le_div_of_nonneg_right hlog jensenDenominator_pos.le)

/-- The literal `O(log(N(|t|+2)))` conclusion once the missing left-arc
polynomial growth estimate is supplied.  The premise is a bound on L itself,
not a renamed zero-count statement. -/
theorem closedUnitWindowCount_le_of_leftArc_polynomial_growth
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {σ t C A : ℝ}
    (hσ : 1 / 2 ≤ σ) (hC : 3 ≤ C) (hA : 0 ≤ A)
    (hleft : ∀ z ∈ Metric.sphere (jensenCenter t) |jensenOuterRadius|,
      z.re < 2 →
        ‖regularizedLFunction χ z‖ ≤ C * (arithmeticScale N t) ^ A) :
    (closedUnitWindowCount χ σ t : ℝ) ≤
      (Real.log 3 + Real.log C + A * Real.log (arithmeticScale N t)) /
        Real.log (jensenOuterRadius / jensenInnerRadius) := by
  have hS : 1 ≤ arithmeticScale N t := one_le_arithmeticScale t
  have hpow : 1 ≤ (arithmeticScale N t) ^ A :=
    Real.one_le_rpow hS hA
  have hM : 3 ≤ C * (arithmeticScale N t) ^ A := by
    calc
      3 ≤ C := hC
      _ ≤ C * (arithmeticScale N t) ^ A := by
        nlinarith
  have hbound := closedUnitWindowCount_le_log_three_mul_of_leftArc_bound
    χ hχ hσ hM hleft
  have hSpos : 0 < arithmeticScale N t := lt_of_lt_of_le zero_lt_one hS
  have hlogeq :
      Real.log (3 * (C * (arithmeticScale N t) ^ A)) =
        Real.log 3 + Real.log C + A * Real.log (arithmeticScale N t) := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (mul_ne_zero (by linarith : C ≠ 0)
        (Real.rpow_pos_of_pos hSpos A).ne'),
      Real.log_mul (by linarith : C ≠ 0)
        (Real.rpow_pos_of_pos hSpos A).ne',
      Real.log_rpow hSpos]
    ring
  rw [hlogeq] at hbound
  exact hbound

end MAPPrimitiveLFixedStrip
