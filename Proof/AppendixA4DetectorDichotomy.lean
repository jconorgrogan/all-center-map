import AppendixA4GammaTails
import BudgetedFixedCharacterPoweredLargeValueBridge
import Mathlib.Analysis.SpecificLimits.Normed

namespace MAPAppendixA4DetectorDichotomy

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
  MAPAppendixA4FullContourLimit MAPAppendixA4GammaTails

noncomputable section

variable {q : ℕ} [NeZero q]

/-- At most `U+1` divisor pairs in the detector convolution can survive the
mollifier cutoff on the second coordinate. -/
theorem card_detectorSupport_le (U n : ℕ) :
    ((n.divisorsAntidiagonal).filter (fun p => p.2 ≤ U)).card ≤ U + 1 := by
  calc
    ((n.divisorsAntidiagonal).filter (fun p => p.2 ≤ U)).card ≤
        (Finset.range (U + 1)).card := by
      apply Finset.card_le_card_of_injOn Prod.snd
      · intro p hp
        have hp' := Finset.mem_filter.mp hp
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hp'.2)
      · intro p hp r hr heq
        have hpmem := (Finset.mem_filter.mp hp).1
        have hrmem := (Finset.mem_filter.mp hr).1
        have hpa := Nat.mem_divisorsAntidiagonal.mp hpmem
        have hra := Nat.mem_divisorsAntidiagonal.mp hrmem
        have hspos : 0 < p.2 := by
          by_contra h
          have : p.2 = 0 := Nat.eq_zero_of_not_pos h
          simp [this] at hpa
          exact hpa.2 hpa.1.symm
        apply Prod.ext
        · apply Nat.eq_of_mul_eq_mul_right hspos
          calc
            p.1 * p.2 = n := hpa.1
            _ = r.1 * r.2 := hra.1.symm
            _ = r.1 * p.2 := by rw [heq]
        · exact heq
    _ = U + 1 := Finset.card_range (U + 1)

/-- Uniform elementary coefficient bound for the exact detector coefficient.
It retains the mollifier cutoff and therefore costs `U+1`, not `n`. -/
theorem norm_mollifierCoeff_le (U n : ℕ) :
    ‖mollifierCoeff U n‖ ≤ U + 1 := by
  rw [mollifierCoeff_apply]
  calc
    ‖∑ p ∈ n.divisorsAntidiagonal, truncatedMoebius U p.2‖
        ≤ ∑ p ∈ n.divisorsAntidiagonal, ‖truncatedMoebius U p.2‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ n.divisorsAntidiagonal,
        if p.2 ≤ U then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro p hp
      unfold truncatedMoebius
      split_ifs with h
      · change ‖((ArithmeticFunction.moebius p.2 : ℤ) : ℂ)‖ ≤ 1
        rw [Complex.norm_intCast]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := p.2)
      · simp
    _ = (((n.divisorsAntidiagonal).filter (fun p => p.2 ≤ U)).card : ℝ) := by
      simp
    _ ≤ U + 1 := by exact_mod_cast card_detectorSupport_le U n

/-- The exact exponentially weighted arithmetic detector term has the
uniform coefficient majorant `(U+1)e^{-n/Y}` on every nonnegative beta line. -/
theorem norm_arithmeticDetectorTerm_le
    (chi : DirichletCharacter ℂ q) (U : ℕ) {rho : ℂ}
    (hbeta : 0 ≤ rho.re) {Y : ℝ} (hY : 0 < Y)
    {n : ℕ} (hn : 0 < n) :
    ‖arithmeticDetectorTerm chi U rho Y n‖ ≤
      (U + 1) * Real.exp (-((n : ℝ) / Y)) := by
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 1 ≤ (n : ℝ) ^ rho.re :=
    Real.one_le_rpow hn1 hbeta
  have hchi : ‖chi (n : ZMod q)‖ ≤ 1 := chi.norm_le_one _
  have hcoeff : ‖detectorCoeff chi U n‖ ≤ U + 1 := by
    unfold detectorCoeff
    simp only [Pi.mul_apply, norm_mul]
    exact (mul_le_mul hchi (norm_mollifierCoeff_le U n)
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hterm : ‖LSeries.term (detectorCoeff chi U) rho n‖ ≤ U + 1 := by
    rw [LSeries.norm_term_eq, if_neg (Nat.ne_of_gt hn)]
    have hU0 : 0 ≤ (U + 1 : ℝ) := by positivity
    have hUden : (U + 1 : ℝ) ≤ (U + 1) * (n : ℝ) ^ rho.re := by
      simpa using mul_le_mul_of_nonneg_left hden hU0
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hden)).2
      (hcoeff.trans hUden)
  unfold arithmeticDetectorTerm
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  exact mul_le_mul_of_nonneg_right hterm (Real.exp_nonneg _)

/-- Rewriting of the exponential detector weight as a literal geometric
power. -/
theorem exp_neg_nat_div_eq_pow {Y : ℝ} (n : ℕ) :
    Real.exp (-((n : ℝ) / Y)) = (Real.exp (-(1 / Y))) ^ n := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Quantitative arithmetic tail after `N`: it is a pure geometric tail
because the mollifier cutoff gives a uniform `U+1` coefficient bound. -/
theorem norm_arithmetic_shifted_tail_le
    (chi : DirichletCharacter ℂ q) (U N : ℕ) {rho : ℂ}
    (hbeta : 0 ≤ rho.re) {Y : ℝ} (hY : 0 < Y) :
    ‖∑' k : ℕ, arithmeticDetectorTerm chi U rho Y (k + (N + 1))‖ ≤
      (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
        (1 - Real.exp (-(1 / Y)))⁻¹ := by
  let r : ℝ := Real.exp (-(1 / Y))
  have hneg : -(1 / Y) < 0 := by
    have hinv : 0 < 1 / Y := one_div_pos.mpr hY
    linarith
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hneg
  have hrsum : Summable (fun k : ℕ =>
      (U + 1 : ℝ) * r ^ (k + (N + 1))) := by
    have hg := summable_geometric_of_norm_lt_one
      (show ‖r‖ < 1 by simpa [abs_of_pos hrpos] using hrlt)
    have hscaled := hg.mul_left ((U + 1 : ℝ) * r ^ (N + 1))
    exact hscaled.congr (fun k => by rw [pow_add]; ring)
  have hterm : ∀ k : ℕ,
      ‖arithmeticDetectorTerm chi U rho Y (k + (N + 1))‖ ≤
        (U + 1 : ℝ) * r ^ (k + (N + 1)) := by
    intro k
    have hn : 0 < k + (N + 1) := by omega
    have h := norm_arithmeticDetectorTerm_le chi U hbeta hY hn
    rw [exp_neg_nat_div_eq_pow (Y := Y) (k + (N + 1))] at h
    simpa [r] using h
  have hnormsum : Summable (fun k : ℕ =>
      ‖arithmeticDetectorTerm chi U rho Y (k + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hrsum
  calc
    ‖∑' k : ℕ, arithmeticDetectorTerm chi U rho Y (k + (N + 1))‖
        ≤ ∑' k : ℕ,
          ‖arithmeticDetectorTerm chi U rho Y (k + (N + 1))‖ :=
      norm_tsum_le_tsum_norm hnormsum
    _ ≤ ∑' k : ℕ, (U + 1 : ℝ) * r ^ (k + (N + 1)) :=
      hnormsum.tsum_le_tsum hterm hrsum
    _ = (U + 1) * r ^ (N + 1) * (1 - r)⁻¹ := by
      rw [show (fun k : ℕ => (U + 1 : ℝ) * r ^ (k + (N + 1))) =
          (fun k : ℕ => ((U + 1 : ℝ) * r ^ (N + 1)) * r ^ k) by
        funext k
        rw [pow_add]
        ring]
      rw [tsum_mul_left, tsum_geometric_of_norm_lt_one
        (show ‖r‖ < 1 by simpa [abs_of_pos hrpos] using hrlt)]
    _ = (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
        (1 - Real.exp (-(1 / Y)))⁻¹ := by rfl

/-- Explicit exponential envelope for the actual shifted-line integrand.
The polynomial from Gamma and the fixed-strip L-bound is absorbed into
`exp(|t|/2)` by the third Taylor coefficient of the exponential. -/
theorem norm_gammaLeftIntegrand_le_exp
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖gammaLeftIntegrand chi U rho Y t‖ ≤
      (115200 * (q : ℝ) ^ 2 * (U + 1) *
        Real.exp ((5 + |rho.im|) / 2)) * Real.exp (-|t| / 2) := by
  let a : ℝ := 1 / 2 - rho.re
  let C₀ : ℝ := 5 + |rho.im|
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a ≤ 1 / 2 := by dsimp [a]; linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      12 * (1 + |t|) * Real.exp (-|t|) := by
    have h := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      haLow haHigh ht
    simpa [GammaCompactStripScratch.stripPoint] using h
  have hYpow : ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    exact Real.rpow_le_one_of_one_le_of_nonpos hY (by dsimp [a]; linarith)
  have hslo : -1 ≤ (rho + ((a : ℂ) + t * I)).re := by
    simp [a]
    norm_num
  have hshi : (rho + ((a : ℂ) + t * I)).re ≤ 2 := by
    simp [a]
    norm_num
  have hL0 := PLInteriorGrowth.norm_LFunction_fixedStrip_le chi hchi hslo hshi
  have him : |(rho + ((a : ℂ) + t * I) + 3).im| ≤
      |rho.im| + |t| := by
    simp
    exact abs_add_le rho.im t
  have hre : |(rho + ((a : ℂ) + t * I) + 3).re| ≤ 5 := by
    simp [a]
    norm_num
  have hnormshift : ‖rho + ((a : ℂ) + t * I) + 3‖ ≤ C₀ + |t| := by
    calc
      ‖rho + ((a : ℂ) + t * I) + 3‖ ≤
          |(rho + ((a : ℂ) + t * I) + 3).re| +
            |(rho + ((a : ℂ) + t * I) + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|rho.im| + |t|) := add_le_add hre him
      _ = C₀ + |t| := by dsimp [C₀]; ring
  have hL : ‖DirichletCharacter.LFunction chi
      (rho + ((a : ℂ) + t * I))‖ ≤
      200 * (q : ℝ) ^ 2 * (C₀ + |t|) ^ 2 := by
    exact hL0.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hnormshift 2) (by positivity))
  have hsnonneg : 0 ≤ (rho + ((a : ℂ) + t * I)).re := by simp [a]
  have hM := MAPAppendixA4GammaTails.norm_mollifier_le_card chi U hsnonneg
  have hC₀ : 1 ≤ C₀ := by dsimp [C₀]; linarith [abs_nonneg rho.im]
  have hpoly0 : 1 + |t| ≤ C₀ + |t| := by
    simpa [add_comm] using add_le_add_right hC₀ |t|
  let x : ℝ := (C₀ + |t|) / 2
  have hx : 0 ≤ x := by dsimp [x, C₀]; positivity
  have htaylor := Real.pow_div_factorial_le_exp x hx 3
  have hpolyexp : (C₀ + |t|) ^ 3 ≤ 48 * Real.exp x := by
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num
    rw [hfac] at htaylor
    dsimp [x] at htaylor ⊢
    nlinarith [Real.exp_pos ((C₀ + |t|) / 2)]
  have hexpcombine : Real.exp x * Real.exp (-|t|) =
      Real.exp (C₀ / 2) * Real.exp (-|t| / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  unfold gammaLeftIntegrand MAPMellinDetectorLeaf.gammaMellinWeight
  dsimp only
  rw [norm_mul, norm_mul, norm_mul]
  calc
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ *
        ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ *
        ‖DirichletCharacter.LFunction chi (rho + ((a : ℂ) + t * I))‖ *
        ‖mollifier chi U (rho + ((a : ℂ) + t * I))‖
        ≤ (12 * (1 + |t|) * Real.exp (-|t|)) * 1 *
            (200 * (q : ℝ) ^ 2 * (C₀ + |t|) ^ 2) * (U + 1) := by
          gcongr
    _ = 2400 * (q : ℝ) ^ 2 * (U + 1) *
          (((1 + |t|) * (C₀ + |t|) ^ 2) * Real.exp (-|t|)) := by
      ring
    _ ≤ 2400 * (q : ℝ) ^ 2 * (U + 1) *
          ((C₀ + |t|) ^ 3 * Real.exp (-|t|)) := by
      have hbase : 0 ≤ C₀ + |t| := by positivity
      have hpoly : (1 + |t|) * (C₀ + |t|) ^ 2 ≤
          (C₀ + |t|) ^ 3 := by
        calc
          (1 + |t|) * (C₀ + |t|) ^ 2 ≤
              (C₀ + |t|) * (C₀ + |t|) ^ 2 :=
            mul_le_mul_of_nonneg_right hpoly0 (sq_nonneg _)
          _ = (C₀ + |t|) ^ 3 := by ring
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)) (by positivity)
    _ ≤ 2400 * (q : ℝ) ^ 2 * (U + 1) *
          ((48 * Real.exp x) * Real.exp (-|t|)) := by
      gcongr
    _ = (115200 * (q : ℝ) ^ 2 * (U + 1) *
          Real.exp (C₀ / 2)) * Real.exp (-|t| / 2) := by
      rw [mul_assoc (48 : ℝ), hexpcombine]
      ring
    _ = (115200 * (q : ℝ) ^ 2 * (U + 1) *
          Real.exp ((5 + |rho.im|) / 2)) * Real.exp (-|t| / 2) := by rfl

/-- The two literal shifted-line tails outside `[-B,B]` have an explicit
exponential bound, uniform in `Y ≥ 1` and in the zero real part
`1/2 < Re ρ ≤ 1`.  The half-lines are written separately so that no point or
set normalization is hidden in the quantitative estimate. -/
theorem norm_gammaLeftIntegrand_two_tails_le_exp
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
      460800 * (q : ℝ) ^ 2 * (U + 1) *
        Real.exp ((5 + |rho.im|) / 2) * Real.exp (-B / 2) := by
  let K : ℝ := 115200 * (q : ℝ) ^ 2 * (U + 1) *
    Real.exp ((5 + |rho.im|) / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hupperMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((-1 / 2 : ℝ) * t)) (Set.Ioi B) :=
    (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B).const_mul K
  have hlowerMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((1 / 2 : ℝ) * t)) (Set.Iic (-B)) :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)).const_mul K
  have hupper :
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
          ∫ t : ℝ in Set.Ioi B, K * Real.exp ((-1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hupperMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        change B < t at ht
        have htpos : 0 < t := lt_of_le_of_lt (by linarith : 0 ≤ B) ht
        have htlarge : 1 ≤ |t| := by
          rw [abs_of_pos htpos]
          linarith
        have hpoint := norm_gammaLeftIntegrand_le_exp chi hchi hbetaLow
          hbetaHigh U hY (t := t) htlarge
        rw [abs_of_pos htpos] at hpoint
        simpa [K, div_eq_mul_inv, mul_comm] using hpoint
      _ = K * (-Real.exp ((-1 / 2 : ℝ) * B) / (-1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (-1 / 2 : ℝ) * B = -B / 2 by ring]
        ring
  have hlower :
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ ≤
          ∫ t : ℝ in Set.Iic (-B), K * Real.exp ((1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hlowerMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
        change t ≤ -B at ht
        have htnonpos : t ≤ 0 := by linarith
        have htlarge : 1 ≤ |t| := by
          rw [abs_of_nonpos htnonpos]
          linarith
        have hpoint := norm_gammaLeftIntegrand_le_exp chi hchi hbetaLow
          hbetaHigh U hY (t := t) htlarge
        rw [abs_of_nonpos htnonpos] at hpoint
        simpa [K, div_eq_mul_inv, mul_comm] using hpoint
      _ = K * (Real.exp ((1 / 2 : ℝ) * (-B)) / (1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (1 / 2 : ℝ) * (-B) = -B / 2 by ring]
        ring
  calc
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ ≤
        ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t‖ +
          ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t‖ :=
      norm_add_le _ _
    _ ≤ 2 * K * Real.exp (-B / 2) + 2 * K * Real.exp (-B / 2) :=
      add_le_add hlower hupper
    _ = 460800 * (q : ℝ) ^ 2 * (U + 1) *
        Real.exp ((5 + |rho.im|) / 2) * Real.exp (-B / 2) := by
      dsimp [K]
      ring

/-! ## Exact simultaneous arithmetic/vertical truncation -/

/-- The literal finite arithmetic detector block `U < n ≤ N`. -/
def arithmeticDetectorBlock
    (chi : DirichletCharacter ℂ q) (U N : ℕ) (rho : ℂ) (Y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ico (U + 1) (N + 1),
    arithmeticDetectorTerm chi U rho Y n

/-- The normalized shifted-line integral restricted to `[-B,B]`. -/
def normalizedCentralGammaIntegral
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ)
    (Y B : ℝ) : ℂ :=
  (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y t)

/-- Exact decomposition of the full A.4 identity into the paper's finite
arithmetic block, the arithmetic tail after `N`, the central shifted-line
integral, and its two literal half-line tails. -/
theorem quantitative_detector_decomposition
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) (B : ℝ) :
    (Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chi U N rho Y +
        ∑' k : ℕ, arithmeticDetectorTerm chi U rho Y (k + (N + 1)) =
      normalizedCentralGammaIntegral chi U rho Y B +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ((∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
            ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t)) := by
  let f : ℕ → ℂ := arithmeticDetectorTerm chi U rho Y
  let g : ℝ → ℂ := gammaLeftIntegrand chi U rho Y
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hsum : Summable f := by
    exact summable_arithmeticDetectorTerm chi U hbetaLow hYpos
  have hsplitSum := hsum.sum_add_tsum_nat_add (N + 1)
  have hUN' : U + 1 ≤ N + 1 := by omega
  have hfinite := Finset.sum_range_add_sum_Ico f hUN'
  have hmain :
      ∑ n ∈ Finset.range (U + 1), f n =
        (Real.exp (-(1 / Y)) : ℂ) := by
    simpa [f] using arithmeticDetectorTerm_sum_range_eq_main
      chi hU rho hYpos
  rw [hmain] at hfinite
  have hseries :
      (Real.exp (-(1 / Y)) : ℂ) +
          arithmeticDetectorBlock chi U N rho Y +
          ∑' k : ℕ, arithmeticDetectorTerm chi U rho Y (k + (N + 1)) =
        ∑' n : ℕ, arithmeticDetectorTerm chi U rho Y n := by
    dsimp [arithmeticDetectorBlock, f] at hfinite hsplitSum ⊢
    rw [← hsplitSum, ← hfinite]
  have hg : Integrable g := by
    exact integrable_gammaLeftIntegrand chi hchi hrho hbetaLow hbetaHigh U hY
  have hfull := intervalIntegral.integral_Iic_add_Ioi
    (b := B) hg.integrableOn hg.integrableOn
  have hcenter := intervalIntegral.integral_Iic_sub_Iic
    (a := -B) (b := B) hg.integrableOn hg.integrableOn
  have hintegral :
      (∫ t : ℝ, gammaLeftIntegrand chi U rho Y t) =
        (∫ t : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y t) +
          ((∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
            ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t) := by
    dsimp [g] at hfull hcenter
    rw [← hfull, ← hcenter]
    abel
  have hA4 := literal_A4_full_identity chi hchi hU hrho hbetaLow
    hbetaHigh hY
  have hfullSeries := arithmetic_detector_tsum_eq_main_add_tail
    chi hU hbetaLow hYpos
  rw [← hfullSeries] at hA4
  rw [← hseries, hintegral] at hA4
  dsimp [normalizedCentralGammaIntegral]
  linear_combination hA4

/-- Quantitative norm error after the simultaneous truncation.  Both error
terms are explicit and retain all conductor, mollifier, zero-height, `Y`, `N`,
and `B` dependence. -/
theorem norm_quantitative_detector_truncation_error_le
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U N : ℕ} (hU : 1 ≤ U) (hUN : U ≤ N)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chi U N rho Y -
        normalizedCentralGammaIntegral chi U rho Y B‖ ≤
      (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ +
        (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) *
            Real.exp ((5 + |rho.im|) / 2) * Real.exp (-B / 2)) := by
  let A : ℂ := ∑' k : ℕ,
    arithmeticDetectorTerm chi U rho Y (k + (N + 1))
  let V : ℂ :=
    (∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chi U rho Y t) +
      ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chi U rho Y t
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hdecomp := quantitative_detector_decomposition chi hchi hU hUN hrho
    hbetaLow hbetaHigh hY B
  have herr :
      (Real.exp (-(1 / Y)) : ℂ) +
          arithmeticDetectorBlock chi U N rho Y -
          normalizedCentralGammaIntegral chi U rho Y B = c * V - A := by
    dsimp [A, V, c]
    linear_combination hdecomp
  have hA := norm_arithmetic_shifted_tail_le chi U N
    (le_trans (by norm_num : (0 : ℝ) ≤ 1 / 2) hbetaLow.le)
    (lt_of_lt_of_le zero_lt_one hY)
  have hV := norm_gammaLeftIntegrand_two_tails_le_exp chi hchi hbetaLow
    hbetaHigh U hY hB
  rw [herr]
  calc
    ‖c * V - A‖ ≤ ‖c * V‖ + ‖A‖ := norm_sub_le _ _
    _ = ‖c‖ * ‖V‖ + ‖A‖ := by rw [norm_mul]
    _ ≤ (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) *
            Real.exp ((5 + |rho.im|) / 2) * Real.exp (-B / 2)) +
        ((U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹) := by
      have hc : ‖c‖ = 1 / (2 * Real.pi) := by
        dsimp [c]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        positivity
      rw [hc]
      exact add_le_add (mul_le_mul_of_nonneg_left hV (by positivity)) hA
    _ = (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ +
        (1 / (2 * Real.pi)) *
          (460800 * (q : ℝ) ^ 2 * (U + 1) *
            Real.exp ((5 + |rho.im|) / 2) * Real.exp (-B / 2)) := by
      ring

/-! ## Paper-scale cutoffs and the quantitative detector dichotomy -/

/-- The paper's arithmetic cutoff `N = ceil (Y (log R)^2)`. -/
def detectorArithmeticCutoff (Y R : ℝ) : ℕ :=
  ⌈Y * (Real.log R) ^ 2⌉₊

/-- The paper's vertical cutoff `B = (log R)^2`. -/
def detectorVerticalCutoff (R : ℝ) : ℝ :=
  (Real.log R) ^ 2

/-- Fully explicit error budget after making both paper-scale choices. -/
def detectorTruncationErrorEnvelope
    (q U : ℕ) (rho : ℂ) (Y R : ℝ) : ℝ :=
  (U + 1) * (Real.exp (-(1 / Y))) ^ (detectorArithmeticCutoff Y R + 1) *
      (1 - Real.exp (-(1 / Y)))⁻¹ +
    (1 / (2 * Real.pi)) *
      (460800 * (q : ℝ) ^ 2 * (U + 1) *
        Real.exp ((5 + |rho.im|) / 2) *
          Real.exp (-(detectorVerticalCutoff R) / 2))

/-- Specialization of the literal truncation error to
`N = ceil (Y (log R)^2)` and `B = (log R)^2`. -/
theorem norm_paper_scale_detector_truncation_error_le
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R) :
    ‖(Real.exp (-(1 / Y)) : ℂ) +
        arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y -
        normalizedCentralGammaIntegral chi U rho Y
          (detectorVerticalCutoff R)‖ ≤
      detectorTruncationErrorEnvelope q U rho Y R := by
  simpa [detectorTruncationErrorEnvelope] using
    norm_quantitative_detector_truncation_error_le chi hchi hU hUN hrho
      hbetaLow hbetaHigh hY hB

/-- Stable triangle-inequality form of the detector alternative with a
nonzero certified truncation error. -/
theorem detector_norm_dichotomy_of_error
    {E D I : ℂ} {delta a b : ℝ}
    (herror : ‖E + D - I‖ ≤ delta)
    (hmain : delta + a + b ≤ ‖E‖) :
    a ≤ ‖D‖ ∨ b ≤ ‖I‖ := by
  by_contra h
  push Not at h
  have hE : E = (E + D - I) - D + I := by ring
  have htriangle : ‖E‖ ≤ ‖E + D - I‖ + ‖D‖ + ‖I‖ := by
    calc
      ‖E‖ = ‖(E + D - I) - D + I‖ := congrArg norm hE
      _ ≤ ‖(E + D - I) - D‖ + ‖I‖ := norm_add_le _ _
      _ ≤ (‖E + D - I‖ + ‖D‖) + ‖I‖ :=
        by simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right (norm_sub_le (E + D - I) D) ‖I‖
  have hstrict : ‖E + D - I‖ + ‖D‖ + ‖I‖ < delta + a + b := by
    linarith
  linarith

/-- Quantitative pointwise detector dichotomy after A.5, with the exact
paper-scale arithmetic and vertical cutoffs.  Any budget split `a+b` below the
surviving main term yields either the literal finite Dirichlet block or the
literal normalized critical-line integral. -/
theorem post_A5_quantitative_detector_dichotomy
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : detectorTruncationErrorEnvelope q U rho Y R + a + b ≤
      Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      b ≤ ‖normalizedCentralGammaIntegral chi U rho Y
        (detectorVerticalCutoff R)‖ := by
  apply detector_norm_dichotomy_of_error
    (norm_paper_scale_detector_truncation_error_le chi hchi hU hrho
      hbetaLow hbetaHigh hY hUN hB)
  have hnorm : ‖(Real.exp (-(1 / Y)) : ℂ)‖ =
      Real.exp (-(1 / Y)) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos (-(1 / Y)))]
  rw [hnorm]
  exact hbudget

/-! ## Critical-line point extraction from the Type-II alternative -/

/-- Norm of the Gamma--Mellin kernel on the shifted line, with the critical
`L*M` factor removed. -/
def gammaLeftKernelNorm (rho : ℂ) (Y : ℝ) (t : ℝ) : ℝ :=
  let a : ℝ := 1 / 2 - rho.re
  ‖Complex.Gamma ((a : ℂ) + t * I) *
    (Y : ℂ) ^ ((a : ℂ) + t * I)‖

/-- Norm of the literal critical-line `L*M` product reached from a zero
`rho` by the shifted-line parameter `t`. -/
def criticalLineProductNorm
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (t : ℝ) : ℝ :=
  let a : ℝ := 1 / 2 - rho.re
  ‖DirichletCharacter.LFunction chi (rho + ((a : ℂ) + t * I)) *
    mollifier chi U (rho + ((a : ℂ) + t * I))‖

theorem criticalLineProductNorm_eq
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (t : ℝ) :
    criticalLineProductNorm chi U rho t =
      ‖DirichletCharacter.LFunction chi
          (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) *
        mollifier chi U (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  let a : ℝ := 1 / 2 - rho.re
  have hs : rho + ((a : ℂ) + t * I) =
      (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) := by
    apply Complex.ext <;> simp [a]
  simp only [criticalLineProductNorm]
  rw [hs]

/-- Literal truncated mass of the Gamma--Mellin kernel. -/
def truncatedGammaLeftKernelMass (rho : ℂ) (Y B : ℝ) : ℝ :=
  ∫ t : ℝ in (-B)..B, gammaLeftKernelNorm rho Y t

theorem continuous_gammaLeftKernelNorm
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 0 < Y) :
    Continuous (gammaLeftKernelNorm rho Y) := by
  let a : ℝ := 1 / 2 - rho.re
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a < 0 := by dsimp [a]; linarith
  have hgamma : Continuous (fun t : ℝ =>
      Complex.Gamma ((a : ℂ) + t * I)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hinner : ContinuousAt (fun u : ℝ =>
        ((a : ℂ) + (u : ℂ) * I)) t := by fun_prop
    exact (Complex.continuousAt_Gamma _ (fun n hn => by
      have hre := congrArg Complex.re hn
      simp at hre
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      by_cases hnz : n = 0
      · subst n
        norm_num at hre
        linarith
      · have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnz
        linarith)).comp_of_eq hinner rfl
  have hpow : Continuous (fun t : ℝ =>
      (Y : ℂ) ^ ((a : ℂ) + t * I)) := by
    have hd : Differentiable ℂ (fun z : ℂ => (Y : ℂ) ^ z) :=
      differentiable_id.const_cpow
        (.inl (Complex.ofReal_ne_zero.mpr hY.ne'))
    exact hd.continuous.comp (by fun_prop)
  unfold gammaLeftKernelNorm
  dsimp only
  exact (hgamma.mul hpow).norm

private theorem gammaLeftCompactConstant_le
    {a : ℝ} (haLow : -(1 / 2 : ℝ) ≤ a) (haHigh : a ≤ -(1 / 5 : ℝ)) :
    (1 + ((-a) * (a + 1))⁻¹) *
        (Real.Gamma (a + 2) + Real.Gamma (a + 4)) ≤ 58 := by
  have haNeg : a < 0 := by linarith
  have hcpos : 0 < (-a) * (a + 1) := by
    apply mul_pos <;> linarith
  have hcLower : (4 / 25 : ℝ) ≤ (-a) * (a + 1) := by
    have hprod : 0 ≤ (-a - 1 / 5) * (4 / 5 + a) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hcinv : ((-a) * (a + 1))⁻¹ ≤ (25 / 4 : ℝ) := by
    have h := (inv_le_inv₀ hcpos (by norm_num : (0 : ℝ) < 4 / 25)).2 hcLower
    norm_num at h ⊢
    exact h
  have hfac : 1 + ((-a) * (a + 1))⁻¹ ≤ (29 / 4 : ℝ) := by
    linarith
  have ha2pos : 0 < a + 2 := by linarith
  have ha2one : 1 ≤ a + 2 := by linarith
  have ha3mem : a + 3 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hthreeMem : (3 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa3 : Real.Gamma (a + 3) ≤ Real.Gamma 3 :=
    Real.Gamma_strictMonoOn_Ici.monotoneOn ha3mem hthreeMem (by linarith)
  have hGa2 : Real.Gamma (a + 2) ≤ 2 := by
    calc
      Real.Gamma (a + 2) ≤ (a + 2) * Real.Gamma (a + 2) :=
        (le_mul_iff_one_le_left (Real.Gamma_pos_of_pos ha2pos)).2 ha2one
      _ = Real.Gamma (a + 3) := by
        rw [show a + 3 = (a + 2) + 1 by ring,
          Real.Gamma_add_one (ne_of_gt ha2pos)]
      _ ≤ Real.Gamma 3 := hGa3
      _ = 2 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have ha4mem : a + 4 ∈ Set.Ici (2 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  have hfourMem : (4 : ℝ) ∈ Set.Ici (2 : ℝ) := by norm_num
  have hGa4 : Real.Gamma (a + 4) ≤ 6 := by
    calc
      Real.Gamma (a + 4) ≤ Real.Gamma 4 :=
        Real.Gamma_strictMonoOn_Ici.monotoneOn ha4mem hfourMem (by linarith)
      _ = 6 := by norm_num [Real.Gamma_ofNat_eq_factorial]
  have hsum : Real.Gamma (a + 2) + Real.Gamma (a + 4) ≤ 8 := by
    linarith
  have hsum0 : 0 ≤ Real.Gamma (a + 2) + Real.Gamma (a + 4) :=
    add_nonneg (Real.Gamma_pos_of_pos ha2pos).le
      (Real.Gamma_pos_of_pos (by linarith)).le
  calc
    (1 + ((-a) * (a + 1))⁻¹) *
          (Real.Gamma (a + 2) + Real.Gamma (a + 4))
        ≤ (29 / 4 : ℝ) * 8 := mul_le_mul hfac hsum hsum0 (by norm_num)
    _ = 58 := by norm_num

/-- Uniform pointwise majorant for the Gamma--Mellin kernel on the full
shifted line when `7/10 ≤ Re rho ≤ 1`.  The certified fourth-order Gamma
envelope costs at most `58`; one inverse Cauchy factor is then discarded to
expose the standard integrable kernel. -/
theorem gammaLeftKernelNorm_le_uniform
    {rho : ℂ} (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) (t : ℝ) :
    gammaLeftKernelNorm rho Y t ≤
      58 * Real.rpow Y (1 / 2 - rho.re) * (1 + t ^ 2)⁻¹ := by
  let a : ℝ := 1 / 2 - rho.re
  let Cγ : ℝ :=
    (1 + ((-a) * (a + 1))⁻¹) *
      (Real.Gamma (a + 2) + Real.Gamma (a + 4))
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a ≤ -(1 / 5 : ℝ) := by dsimp [a]; linarith
  have haNeg : a < 0 := by linarith
  have hCγ : Cγ ≤ 58 := gammaLeftCompactConstant_le haLow haHigh
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((a : ℂ) + t * I)‖ ≤
      Cγ * (1 + t ^ 2)⁻¹ ^ 2 := by
    simpa [Cγ] using norm_Gamma_left_vertical_le_inv_sq haLow haNeg
  have hpow : ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ =
      Real.rpow Y a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp
  have hD : 1 ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg t]
  have hinv0 : 0 ≤ (1 + t ^ 2)⁻¹ := by positivity
  have hinv1 : (1 + t ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hD
  have hsquare : (1 + t ^ 2)⁻¹ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
    nlinarith [sq_nonneg ((1 + t ^ 2)⁻¹ - 1 / 2)]
  unfold gammaLeftKernelNorm
  dsimp only [a]
  rw [norm_mul, hpow]
  calc
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ * Real.rpow Y a ≤
        (Cγ * (1 + t ^ 2)⁻¹ ^ 2) * Real.rpow Y a :=
      mul_le_mul_of_nonneg_right hgamma (Real.rpow_nonneg hYpos.le _)
    _ ≤ (58 * (1 + t ^ 2)⁻¹) * Real.rpow Y a := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hYpos.le _)
      calc
        Cγ * (1 + t ^ 2)⁻¹ ^ 2 ≤ 58 * (1 + t ^ 2)⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hCγ (sq_nonneg _)
        _ ≤ 58 * (1 + t ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hsquare (by norm_num)
    _ = 58 * Real.rpow Y (1 / 2 - rho.re) * (1 + t ^ 2)⁻¹ := by
      dsimp [a]
      ring

/-- Literal uniform truncated kernel-mass bound.  It is independent of the
zero height and the truncation width; all beta dependence is retained in the
paper factor `Y^(1/2-Re rho)`. -/
theorem truncatedGammaLeftKernelMass_le_uniform
    {rho : ℂ} (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    truncatedGammaLeftKernelMass rho Y B ≤
      58 * Real.pi * Real.rpow Y (1 / 2 - rho.re) := by
  let K : ℝ := 58 * Real.rpow Y (1 / 2 - rho.re)
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hkernel : IntervalIntegrable (gammaLeftKernelNorm rho Y) volume (-B) B :=
    (continuous_gammaLeftKernelNorm (by linarith) hbetaHigh hYpos).intervalIntegrable _ _
  have hmajor : IntervalIntegrable (fun t : ℝ => K * (1 + t ^ 2)⁻¹)
      volume (-B) B := integrable_inv_one_add_sq.const_mul K |>.intervalIntegrable
  calc
    truncatedGammaLeftKernelMass rho Y B =
        ∫ t : ℝ in (-B)..B, gammaLeftKernelNorm rho Y t := rfl
    _ ≤ ∫ t : ℝ in (-B)..B, K * (1 + t ^ 2)⁻¹ := by
      apply intervalIntegral.integral_mono_on (by linarith) hkernel hmajor
      intro t ht
      simpa [K] using gammaLeftKernelNorm_le_uniform hbetaLow hbetaHigh hY t
    _ = K * ∫ t : ℝ in (-B)..B, (1 + t ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K * Real.pi := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [intervalIntegral.integral_of_le (by linarith)]
      calc
        (∫ t : ℝ in Set.Ioc (-B) B, (1 + t ^ 2)⁻¹) ≤
            ∫ t : ℝ, (1 + t ^ 2)⁻¹ :=
          setIntegral_le_integral integrable_inv_one_add_sq
            (Filter.Eventually.of_forall fun t => by positivity)
        _ = Real.pi := integral_univ_inv_one_add_sq
    _ = 58 * Real.pi * Real.rpow Y (1 / 2 - rho.re) := by
      dsimp [K]
      ring

/-- The normalization occurring in the pointwise Type-II extraction reduces
the kernel mass constant from `58*pi` to `29`. -/
theorem normalized_truncatedGammaLeftKernelMass_le_uniform
    {rho : ℂ} (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B : ℝ} (hY : 1 ≤ Y) (hB : 0 ≤ B) :
    ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) * (U + 1) ≤
      29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
  have hmass := truncatedGammaLeftKernelMass_le_uniform hbetaLow hbetaHigh hY hB
  have hscale : 0 ≤ 1 / (2 * Real.pi) := by positivity
  have hU : 0 ≤ (U + 1 : ℝ) := by positivity
  calc
    ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) * (U + 1) ≤
        ((1 / (2 * Real.pi)) *
          (58 * Real.pi * Real.rpow Y (1 / 2 - rho.re))) * (U + 1) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmass hscale) hU
    _ = 29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
      field_simp [ne_of_gt Real.pi_pos]
      <;> ring

theorem norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (Y t : ℝ) :
    ‖gammaLeftIntegrand chi U rho Y t‖ =
      gammaLeftKernelNorm rho Y t * criticalLineProductNorm chi U rho t := by
  unfold gammaLeftIntegrand gammaLeftKernelNorm criticalLineProductNorm
    MAPMellinDetectorLeaf.gammaMellinWeight
  dsimp only
  simp only [norm_mul]
  ring

theorem continuous_criticalLineProductNorm
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (U : ℕ) (rho : ℂ) :
    Continuous (criticalLineProductNorm chi U rho) := by
  let a : ℝ := 1 / 2 - rho.re
  have hL : Continuous (fun t : ℝ =>
      DirichletCharacter.LFunction chi (rho + ((a : ℂ) + t * I))) :=
    (DirichletCharacter.differentiable_LFunction hchi).continuous.comp (by fun_prop)
  have hM : Continuous (fun t : ℝ =>
      mollifier chi U (rho + ((a : ℂ) + t * I))) := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (MAPAppendixA4Detector.analyticAt_mollifier chi
      (rho + ((a : ℂ) + t * I))).continuousAt.comp_of_eq (by fun_prop) rfl
  unfold criticalLineProductNorm
  dsimp only
  exact (hL.mul hM).norm

theorem truncatedGammaLeftKernelMass_pos
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B : ℝ} (hY : 0 < Y) (hB : 0 < B) :
    0 < truncatedGammaLeftKernelMass rho Y B := by
  let a : ℝ := 1 / 2 - rho.re
  have haLow : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haHigh : a < 0 := by dsimp [a]; linarith
  apply intervalIntegral.integral_pos (by linarith)
    (continuous_gammaLeftKernelNorm hbetaLow hbetaHigh hY).continuousOn
  · intro t ht
    exact norm_nonneg _
  · refine ⟨0, ?_, ?_⟩
    · constructor <;> linarith
    · unfold gammaLeftKernelNorm
      dsimp only [a]
      rw [norm_mul]
      apply mul_pos
      · apply norm_pos_iff.mpr
        apply Complex.Gamma_ne_zero
        intro n hn
        have hre := congrArg Complex.re hn
        simp at hre
        by_cases hnz : n = 0
        · subst n
          norm_num at hre
          linarith
        · have hn1 : 1 ≤ (n : ℝ) := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr hnz
          linarith
      · rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
        positivity

/-- A large normalized central integral forces one actual critical-line point
inside the same truncation window to carry the corresponding weighted large
value.  This is the exact maximum extraction; no averaged or existential
analytic proposition is substituted for the pointwise conclusion. -/
theorem exists_criticalLine_large_value_of_central
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (U : ℕ) {rho : ℂ}
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B b : ℝ} (hY : 0 < Y) (hB : 0 ≤ B)
    (hcentral : b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) :
    ∃ t ∈ Set.Icc (-B) B,
      b ≤ (1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B *
        criticalLineProductNorm chi U rho t := by
  let P : ℝ → ℝ := criticalLineProductNorm chi U rho
  let W : ℝ → ℝ := gammaLeftKernelNorm rho Y
  have hP : Continuous P := continuous_criticalLineProductNorm chi hchi U rho
  have hW : Continuous W :=
    continuous_gammaLeftKernelNorm hbetaLow hbetaHigh hY
  obtain ⟨t₀, ht₀, hmax⟩ := isCompact_uIcc.exists_isMaxOn
    Set.nonempty_uIcc hP.continuousOn
  have huIcc : Set.uIcc (-B) B = Set.Icc (-B) B := by
    rw [Set.uIcc_of_le]
    linarith
  rw [huIcc] at ht₀ hmax
  refine ⟨t₀, ht₀, ?_⟩
  have hkernel : IntervalIntegrable (fun t => W t * P t) volume (-B) B :=
    (hW.mul hP).intervalIntegrable _ _
  have hmajor : IntervalIntegrable (fun t => W t * P t₀) volume (-B) B :=
    (hW.mul continuous_const).intervalIntegrable _ _
  have hraw :
      ‖∫ t : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y t‖ ≤
        ∫ t : ℝ in (-B)..B, W t * P t := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · exact Filter.Eventually.of_forall fun t _ => by
        simpa [W, P] using
          norm_gammaLeftIntegrand_eq_kernel_mul_criticalLineProductNorm
            chi U rho Y t |>.le
    · exact hkernel
  have hmono :
      (∫ t : ℝ in (-B)..B, W t * P t) ≤
        ∫ t : ℝ in (-B)..B, W t * P t₀ := by
    apply intervalIntegral.integral_mono_on (by linarith) hkernel hmajor
    intro t ht
    exact mul_le_mul_of_nonneg_left (hmax ht) (norm_nonneg _)
  have hc : ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ =
      1 / (2 * Real.pi) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  calc
    b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖ := hcentral
    _ = (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ in (-B)..B, gammaLeftIntegrand chi U rho Y t‖ := by
      unfold normalizedCentralGammaIntegral
      rw [norm_mul, hc]
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ in (-B)..B, W t * P t) :=
      mul_le_mul_of_nonneg_left hraw (by positivity)
    _ ≤ (1 / (2 * Real.pi)) *
        (∫ t : ℝ in (-B)..B, W t * P t₀) :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B *
        criticalLineProductNorm chi U rho t₀ := by
      rw [intervalIntegral.integral_mul_const]
      dsimp [truncatedGammaLeftKernelMass, W, P]
      ring

/-- Division form of the preceding extraction. -/
theorem exists_criticalLine_large_value_div_mass_of_central
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    (U : ℕ) {rho : ℂ}
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y B b : ℝ} (hY : 0 < Y) (hB : 0 < B)
    (hcentral : b ≤ ‖normalizedCentralGammaIntegral chi U rho Y B‖) :
    ∃ t ∈ Set.Icc (-B) B,
      b / ((1 / (2 * Real.pi)) * truncatedGammaLeftKernelMass rho Y B) ≤
        criticalLineProductNorm chi U rho t := by
  obtain ⟨t, ht, hlarge⟩ := exists_criticalLine_large_value_of_central
    chi hchi U hbetaLow hbetaHigh hY hB.le hcentral
  refine ⟨t, ht, ?_⟩
  apply (div_le_iff₀ ?_).2
  · simpa [mul_assoc, mul_comm, mul_left_comm] using hlarge
  · exact mul_pos (by positivity)
      (truncatedGammaLeftKernelMass_pos hbetaLow hbetaHigh hY hB)

/-- Remove the finite mollifier at the extracted critical-line point using
its certified uniform `U+1` bound. -/
theorem lFunction_norm_lower_of_criticalLineProduct
    (chi : DirichletCharacter ℂ q) (U : ℕ) (rho : ℂ) (t : ℝ)
    {V : ℝ} (hV : V ≤ criticalLineProductNorm chi U rho t) :
    V / (U + 1) ≤
      ‖DirichletCharacter.LFunction chi
        (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)
  have hsnonneg : 0 ≤ s.re := by dsimp [s]; simp
  have hM := norm_mollifier_le_card chi U hsnonneg
  rw [criticalLineProductNorm_eq] at hV
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < U + 1)).2
  calc
    V ≤ ‖DirichletCharacter.LFunction chi s * mollifier chi U s‖ := by
      simpa [s] using hV
    _ = ‖DirichletCharacter.LFunction chi s‖ * ‖mollifier chi U s‖ :=
      norm_mul _ _
    _ ≤ ‖DirichletCharacter.LFunction chi s‖ * (U + 1) :=
      mul_le_mul_of_nonneg_left hM (norm_nonneg _)

/-- End-to-end quantitative detector alternative at the paper cutoffs.  The
Type-II branch is already converted to one literal point on `Re s = 1/2` in
the same `|t-rho.im| ≤ (log R)^2` window. -/
theorem post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : detectorTruncationErrorEnvelope q U rho Y R + a + b ≤
      Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        b / ((1 / (2 * Real.pi)) *
            truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) ≤
          ‖DirichletCharacter.LFunction chi
              (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) *
            mollifier chi U
              (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases post_A5_quantitative_detector_dichotomy chi hchi hU hrho
    hbetaLow hbetaHigh hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ :=
      exists_criticalLine_large_value_div_mass_of_central chi hchi U
        hbetaLow hbetaHigh (lt_of_lt_of_le zero_lt_one hY) (lt_of_lt_of_le zero_lt_one hB)
        hII
    refine ⟨t, ht, ?_⟩
    simpa only [criticalLineProductNorm_eq] using htlarge

/-- Final L-function-only form of the pointwise Type-II extraction. -/
theorem post_A5_quantitative_detector_dichotomy_with_LFunction_large_value
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R a b : ℝ} (hY : 1 ≤ Y)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget : detectorTruncationErrorEnvelope q U rho Y R + a + b ≤
      Real.exp (-(1 / Y))) :
    a ≤ ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        b / (((1 / (2 * Real.pi)) *
            truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) *
              (U + 1)) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  rcases post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value
    chi hchi hU hrho hbetaLow hbetaHigh hY hUN hB hbudget with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    refine ⟨t, ht, ?_⟩
    have hL := lFunction_norm_lower_of_criticalLineProduct chi U rho t
      (V := b / ((1 / (2 * Real.pi)) *
        truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)))
      (by simpa only [criticalLineProductNorm_eq] using htlarge)
    simpa only [div_div] using hL

/-- Bridge-facing detector alternative at the exact reserved loss used by the
budgeted fixed-character powered argument.  The Type-I branch supplies the
weighted detector block at `R^(-inputLoss kappa eta)`, ready for the subsequent
Abel/common-dyadic transfer.  The Type-II branch supplies an actual critical-
line `L`-value at the same threshold.  Thus the kernel normalization no longer
appears in the consumer-facing conclusion. -/
theorem post_A5_budgeted_fixedCharacter_detector_to_largeValue
    (chi : DirichletCharacter ℂ q) (hchi : chi ≠ 1)
    {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η)
    {U : ℕ} (hU : 1 ≤ U)
    {rho : ℂ} (hrho : DirichletCharacter.LFunction chi rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y R : ℝ} (hY : 1 ≤ Y) (hR : 0 < R)
    (hUN : U ≤ detectorArithmeticCutoff Y R)
    (hB : 1 ≤ detectorVerticalCutoff R)
    (hbudget :
      detectorTruncationErrorEnvelope q U rho Y R +
          Real.rpow R (-CGLProofDAG.inputLoss κ η) +
          29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) *
            Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
        Real.exp (-(1 / Y))) :
    Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
        ‖arithmeticDetectorBlock chi U (detectorArithmeticCutoff Y R) rho Y‖ ∨
      ∃ t ∈ Set.Icc (-(detectorVerticalCutoff R)) (detectorVerticalCutoff R),
        Real.rpow R (-CGLProofDAG.inputLoss κ η) ≤
          ‖DirichletCharacter.LFunction chi
            (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ := by
  let V : ℝ := Real.rpow R (-CGLProofDAG.inputLoss κ η)
  let D : ℝ :=
    ((1 / (2 * Real.pi)) *
      truncatedGammaLeftKernelMass rho Y (detectorVerticalCutoff R)) * (U + 1)
  have hbetaHalf : 1 / 2 < rho.re := by linarith
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hBpos : 0 < detectorVerticalCutoff R := lt_of_lt_of_le zero_lt_one hB
  have hmasspos : 0 < truncatedGammaLeftKernelMass rho Y
      (detectorVerticalCutoff R) :=
    truncatedGammaLeftKernelMass_pos hbetaHalf hbetaHigh hYpos hBpos
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (mul_pos (by positivity) hmasspos) (by positivity)
  have hDle : D ≤ 29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) := by
    dsimp [D]
    exact normalized_truncatedGammaLeftKernelMass_le_uniform
      hbetaLow hbetaHigh U hY (by linarith)
  have hVpos : 0 < V := by
    dsimp [V]
    exact Real.rpow_pos_of_pos hR _
  rcases post_A5_quantitative_detector_dichotomy_with_LFunction_large_value
    chi hchi hU hrho hbetaHalf hbetaHigh hY hUN hB
      (a := V)
      (b := 29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V)
      (by simpa [V] using hbudget) with hI | hII
  · exact Or.inl hI
  · right
    obtain ⟨t, ht, htlarge⟩ := hII
    refine ⟨t, ht, ?_⟩
    apply (show V ≤
        (29 * Real.rpow Y (1 / 2 - rho.re) * (U + 1) * V) / D by
      rw [le_div_iff₀ hDpos]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hDle hVpos.le) |>.trans
    simpa [V, D] using htlarge

end
end MAPAppendixA4DetectorDichotomy

#print axioms MAPAppendixA4DetectorDichotomy.norm_mollifierCoeff_le
#print axioms MAPAppendixA4DetectorDichotomy.norm_gammaLeftIntegrand_le_exp
#print axioms MAPAppendixA4DetectorDichotomy.norm_gammaLeftIntegrand_two_tails_le_exp
#print axioms MAPAppendixA4DetectorDichotomy.quantitative_detector_decomposition
#print axioms MAPAppendixA4DetectorDichotomy.norm_quantitative_detector_truncation_error_le
#print axioms MAPAppendixA4DetectorDichotomy.norm_paper_scale_detector_truncation_error_le
#print axioms MAPAppendixA4DetectorDichotomy.post_A5_quantitative_detector_dichotomy
#print axioms MAPAppendixA4DetectorDichotomy.truncatedGammaLeftKernelMass_pos
#print axioms MAPAppendixA4DetectorDichotomy.exists_criticalLine_large_value_div_mass_of_central
#print axioms MAPAppendixA4DetectorDichotomy.post_A5_quantitative_detector_dichotomy_with_criticalLine_large_value
#print axioms MAPAppendixA4DetectorDichotomy.post_A5_quantitative_detector_dichotomy_with_LFunction_large_value
#print axioms MAPAppendixA4DetectorDichotomy.gammaLeftKernelNorm_le_uniform
#print axioms MAPAppendixA4DetectorDichotomy.truncatedGammaLeftKernelMass_le_uniform
#print axioms MAPAppendixA4DetectorDichotomy.normalized_truncatedGammaLeftKernelMass_le_uniform
#print axioms MAPAppendixA4DetectorDichotomy.post_A5_budgeted_fixedCharacter_detector_to_largeValue
