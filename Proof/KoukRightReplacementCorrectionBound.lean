import KoukTheorem113ExactFormula
import VonMangoldtPSeriesBound

/-!
# The endpoint right-edge replacement correction

The correction introduced by replacing `x^s / s` by `(x^s - 1) / s`
is itself the ordinary Perron right line at `x = 1`.  This file records that
identity and bounds the resulting series without taking an absolute value
inside the contour integral.
-/

namespace KoukRightReplacementCorrectionBound

open scoped BigOperators ArithmeticFunction Interval
open PerronKernel PrimitiveExplicitFormulaSpine TruncatedTwistedPerron
open KoukTheorem113ExactFormula

noncomputable section

/-- The literal endpoint replacement correction is the ordinary Perron line
at `x = 1`. -/
theorem endpointRightReplacementCorrection_eq_rightLine_one
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {c T : ℝ} :
    endpointRightReplacementCorrection chi c T =
      rightLineIntegral chi 1 c T := by
  unfold endpointRightReplacementCorrection rightLineIntegral
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [show (2 * Real.pi * Complex.I : ℂ)⁻¹ * Complex.I =
      ((2 * Real.pi : ℝ) : ℂ)⁻¹ by
    field_simp [hpi, Complex.I_ne_zero]
    push_cast
    ring]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  unfold logDerivPerronIntegrand verticalPower
  simp [Real.log_one]

/-- The individual kernel term at `x = 1` is controlled by the ordinary
von Mangoldt Dirichlet-series term, with the sharp `1/T` decay. -/
theorem norm_rightLine_one_kernel_term_le
    {q : ℕ} (chi : DirichletCharacter ℂ q) (n : ℕ)
    {delta T : ℝ} (hdelta : 0 < delta) (hT : 0 < T) :
    ‖twistedMangoldtCoeff chi n *
        PerronKernel.kernel (1 / (n : ℝ)) (1 + delta) T‖ ≤
      (2 / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ (1 + delta)) := by
  by_cases hn0 : n = 0
  · subst n
    simp [twistedMangoldtCoeff]
  by_cases hn1 : n = 1
  · subst n
    simp [twistedMangoldtCoeff]
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnone : 1 < (n : ℝ) := by exact_mod_cast hn2
  have hy : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
  have hy1 : 1 / (n : ℝ) < 1 := (div_lt_one hnpos).2 hnone
  have hkernel := SharpFinitePerronStep.norm_kernel_le_of_lt_one
    hy hy1 (by linarith : 0 < 1 + delta) hT
  have hlogn : (1 / 2 : ℝ) ≤ Real.log (n : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (n : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn
        (by norm_num) hnpos (by exact_mod_cast hn2)
    linarith [Real.log_two_gt_d9]
  have habslog : (1 / 2 : ℝ) ≤
      |Real.log (1 / (n : ℝ))| := by
    have hone : (1 / (n : ℝ)) = (n : ℝ)⁻¹ := by ring
    rw [hone, Real.log_inv, abs_neg, abs_of_nonneg]
    · exact hlogn
    · exact Real.log_nonneg hnone.le
  have hdenpos : 0 < Real.pi * T * (1 / 2 : ℝ) := by positivity
  have hden : Real.pi * T * (1 / 2 : ℝ) ≤
      Real.pi * T * |Real.log (1 / (n : ℝ))| := by
    gcongr
  have hkernel' :
      ‖PerronKernel.kernel (1 / (n : ℝ)) (1 + delta) T‖ ≤
        2 / (Real.pi * T * (n : ℝ) ^ (1 + delta)) := by
    calc
      ‖PerronKernel.kernel (1 / (n : ℝ)) (1 + delta) T‖ ≤
          (1 / (n : ℝ)) ^ (1 + delta) /
            (Real.pi * T * |Real.log (1 / (n : ℝ))|) := hkernel
      _ ≤ (1 / (n : ℝ)) ^ (1 + delta) /
            (Real.pi * T * (1 / 2 : ℝ)) :=
        div_le_div_of_nonneg_left
          (Real.rpow_nonneg (one_div_nonneg.mpr hnpos.le) _) hdenpos hden
      _ = 2 / (Real.pi * T * (n : ℝ) ^ (1 + delta)) := by
        rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hnpos.le]
        simp only [Real.one_rpow]
        field_simp [hnpos.ne', hT.ne', Real.pi_ne_zero,
          (Real.rpow_pos_of_pos hnpos _).ne']
  have hcoeff : ‖twistedMangoldtCoeff chi n‖ ≤
      ArithmeticFunction.vonMangoldt n := norm_twistedMangoldtCoeff_le chi n
  have hvm0 : 0 ≤ ArithmeticFunction.vonMangoldt n :=
    ArithmeticFunction.vonMangoldt_nonneg
  rw [norm_mul]
  calc
    ‖twistedMangoldtCoeff chi n‖ *
        ‖PerronKernel.kernel (1 / (n : ℝ)) (1 + delta) T‖ ≤
      ArithmeticFunction.vonMangoldt n *
        (2 / (Real.pi * T * (n : ℝ) ^ (1 + delta))) :=
      mul_le_mul hcoeff hkernel' (norm_nonneg _) hvm0
    _ = (2 / (Real.pi * T)) *
        (ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ (1 + delta)) := by ring

/-- Summed replacement-correction estimate before inserting the elementary
von Mangoldt p-series bound. -/
theorem norm_endpointRightReplacementCorrection_le_series
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta T : ℝ} (hdelta : 0 < delta) (hT : 0 < T) :
    ‖endpointRightReplacementCorrection chi (1 + delta) T‖ ≤
      (2 / (Real.pi * T)) *
        ∑' n : ℕ, ArithmeticFunction.vonMangoldt n /
          (n : ℝ) ^ (1 + delta) := by
  rw [endpointRightReplacementCorrection_eq_rightLine_one,
    rightLineIntegral_eq_tsum_kernels chi (by norm_num) (by linarith)]
  let f : ℕ → ℂ := fun n =>
    twistedMangoldtCoeff chi n *
      PerronKernel.kernel (1 / (n : ℝ)) (1 + delta) T
  let g : ℕ → ℝ := fun n =>
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + delta)
  let K : ℝ := 2 / (Real.pi * T)
  have hg : Summable g := by
    have hbase : Summable fun n : ℕ =>
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((1 + delta : ℝ) : ℂ) n‖ := by
      apply summable_norm_iff.mpr
      exact ArithmeticFunction.LSeriesSummable_vonMangoldt (by
        simpa using hdelta)
    have hpoint (n : ℕ) : g n =
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((1 + delta : ℝ) : ℂ) n‖ := by
      by_cases hn : n = 0
      · subst n
        simp [g]
      · rw [LSeries.norm_term_eq, if_neg hn]
        simp only [g, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have hfun : g = fun n : ℕ =>
        ‖LSeries.term (fun k : ℕ =>
          (ArithmeticFunction.vonMangoldt k : ℂ))
          ((1 + delta : ℝ) : ℂ) n‖ := by
      funext n
      exact hpoint n
    rw [hfun]
    exact hbase
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hfg (n : ℕ) : ‖f n‖ ≤ K * g n := by
    dsimp only [f, g, K]
    exact norm_rightLine_one_kernel_term_le chi n hdelta hT
  have hKg : Summable fun n => K * g n := hg.mul_left K
  have hf : Summable f := Summable.of_norm_bounded hKg hfg
  change ‖∑' n, f n‖ ≤ K * ∑' n, g n
  calc
    ‖∑' n, f n‖ ≤ ∑' n, ‖f n‖ := norm_tsum_le_tsum_norm hf.norm
    _ ≤ ∑' n, K * g n := hf.norm.tsum_le_tsum hfg hKg
    _ = K * ∑' n, g n := by rw [tsum_mul_left]

/-- Fully explicit character-uniform bound for the endpoint right-edge
replacement correction. -/
theorem norm_endpointRightReplacementCorrection_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {delta T : ℝ} (hdelta : 0 < delta) (hT : 0 < T) :
    ‖endpointRightReplacementCorrection chi (1 + delta) T‖ ≤
      (2 / (Real.pi * T)) *
        ((2 / delta) * (1 + (delta / 2)⁻¹)) := by
  exact (norm_endpointRightReplacementCorrection_le_series chi hdelta hT).trans
    (mul_le_mul_of_nonneg_left
      (VonMangoldtPSeriesBound.tsum_vonMangoldt_div_rpow_le hdelta)
      (by positivity))

#print axioms endpointRightReplacementCorrection_eq_rightLine_one
#print axioms norm_rightLine_one_kernel_term_le
#print axioms norm_endpointRightReplacementCorrection_le_series
#print axioms norm_endpointRightReplacementCorrection_le

end

end KoukRightReplacementCorrectionBound
