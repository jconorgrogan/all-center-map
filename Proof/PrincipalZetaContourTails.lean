import PrincipalZetaPoleContour
import AppendixA4RecenteredGammaRepair

/-!
# Literal contour tails for the principal zeta detector

This file discharges the vertical-integrability and horizontal-decay leaves
left by `PrincipalZetaPoleContour`.  It uses the certified polynomial
fixed-strip bound for `(s-1) zeta(s)` and the exponential Gamma envelope.
No zero-density estimate enters.
-/

namespace MAPPrincipalZetaContourTails

open Set MeasureTheory Complex Filter
open scoped Topology ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPMellinDetectorLeaf
open MAPAppendixA4FullContourLimit MAPAppendixA4GammaEndpoint
open MAPAppendixA4GammaTails MAPPrincipalZetaDetectorPoleRemoval
open MAPPrincipalZetaPoleContour

noncomputable section

set_option maxHeartbeats 800000

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- The raw principal detector on the right line is the already-certified
modulus-one Dirichlet detector. -/
theorem principalRawDetector_right_eq_gammaRight
    (rho : ℂ) (U : ℕ) (Y t : ℝ) :
    principalRawDetector rho U Y (((1 / 2 : ℝ) : ℂ) + t * I) =
      gammaRightIntegrand chiOne U rho Y t := by
  unfold principalRawDetector gammaRightIntegrand
  rw [DirichletCharacter.LFunction_modOne_eq]
  unfold gammaMellinWeight
  ring

/-- The right vertical line is integrable premise-free. -/
theorem integrable_principalRawDetector_right
    {rho : ℂ} (hbeta : 1 / 2 < rho.re) (U : ℕ)
    {Y : ℝ} (hY : 0 < Y) :
    Integrable (fun t : ℝ =>
      principalRawDetector rho U Y (((1 / 2 : ℝ) : ℂ) + t * I)) := by
  have h := MAPAppendixA4FullContourLimit.integrable_gammaRightIntegrand
    chiOne U hbeta hY
  exact h.congr (Filter.Eventually.of_forall fun t =>
    (principalRawDetector_right_eq_gammaRight rho U Y t).symm)

/-- Coarse degree-six zeta bound on the critical line.  The factor two is
the exact cost of undoing the regularization at real distance `1/2` from the
pole. -/
theorem norm_riemannZeta_criticalLine_le (u : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + u * I)‖ ≤
      3200 * (4 + |u|) ^ 6 := by
  let s : ℂ := (((1 / 2 : ℝ) : ℂ) + u * I)
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [s] at hre
  have hreg := MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
    (z := s) (by simp [s]; norm_num) (by simp [s]; norm_num)
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    have hre := Complex.abs_re_le_norm (s - 1)
    norm_num [s] at hre ⊢
    exact hre
  have hshift : ‖s + 3‖ ≤ 4 + |u| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = 7 / 2 + |u| := by simp [s]; norm_num
      _ ≤ 4 + |u| := by linarith
  have heq : principalF s = (s - 1) * riemannZeta s :=
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs1
  change ‖riemannZeta s‖ ≤ _
  calc
    ‖riemannZeta s‖ ≤ 2 * (‖s - 1‖ * ‖riemannZeta s‖) := by
      nlinarith [mul_nonneg (norm_nonneg (s - 1))
        (norm_nonneg (riemannZeta s))]
    _ = 2 * ‖principalF s‖ := by rw [heq, norm_mul]
    _ ≤ 2 * (1600 * ‖s + 3‖ ^ 6) := by gcongr
    _ ≤ 2 * (1600 * (4 + |u|) ^ 6) := by gcongr
    _ = 3200 * (4 + |u|) ^ 6 := by ring

/-- The critical-line zeta bound separated into a polynomial in the zero
height and a polynomial in the displacement. -/
theorem norm_riemannZeta_recentered_le
    (rho : ℂ) (t : ℝ) :
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ ≤
      3200 * (4 + |rho.im|) ^ 6 * (1 + |t|) ^ 6 := by
  have h0 := norm_riemannZeta_criticalLine_le (rho.im + t)
  have h :
      ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ ≤
        3200 * (4 + |rho.im + t|) ^ 6 := by
    simpa only [Complex.ofReal_add] using h0
  have hbase : 4 + |rho.im + t| ≤
      (4 + |rho.im|) * (1 + |t|) := by
    have hadd := abs_add_le rho.im t
    have hr : 1 ≤ 4 + |rho.im| := by linarith [abs_nonneg rho.im]
    nlinarith [abs_nonneg t]
  calc
    ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I)‖ ≤
        3200 * (4 + |rho.im + t|) ^ 6 := h
    _ ≤ 3200 * ((4 + |rho.im|) * (1 + |t|)) ^ 6 := by gcongr
    _ = 3200 * (4 + |rho.im|) ^ 6 * (1 + |t|) ^ 6 := by ring

/-- Exponential tail for the literal shifted principal detector.  The larger
degree seven (rather than degree three in the nonprincipal A.4 proof) is
absorbed only in the displacement variable, so dependence on the zero height
remains polynomial. -/
theorem norm_principalRawDetector_left_le_exp_polynomial_height
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) {t : ℝ} (ht : 1 ≤ |t|) :
    ‖principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)‖ ≤
      (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
          (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
        Real.exp (-|t| / 2) := by
  let a : ℝ := 1 / 2 - rho.re
  let C : ℝ := 4 + |rho.im|
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
  have hs : rho + ((a : ℂ) + t * I) =
      (((1 / 2 : ℝ) : ℂ) + (rho.im + t) * I) := by
    apply Complex.ext <;> simp [a]
  have hzeta : ‖riemannZeta (rho + ((a : ℂ) + t * I))‖ ≤
      3200 * C ^ 6 * (1 + |t|) ^ 6 := by
    rw [hs]
    simpa [C] using norm_riemannZeta_recentered_le rho t
  have hmoll : ‖mollifier chiOne U (rho + ((a : ℂ) + t * I))‖ ≤ U + 1 := by
    apply norm_mollifier_le_card
    rw [hs]
    norm_num
  let x : ℝ := (1 + |t|) / 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have htaylor := Real.pow_div_factorial_le_exp x hx 7
  have hpolyexp : (1 + |t|) ^ 7 ≤
      (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp x := by
    have hpow : (1 + |t|) ^ 7 = (2 : ℝ) ^ 7 * x ^ 7 := by
      dsimp [x]
      ring
    have hxpow0 : x ^ 7 ≤ Real.exp x * (Nat.factorial 7 : ℝ) :=
      (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 7)).mp htaylor
    have hxpow : x ^ 7 ≤ (Nat.factorial 7 : ℝ) * Real.exp x := by
      simpa [mul_comm] using hxpow0
    rw [hpow]
    calc
      (2 : ℝ) ^ 7 * x ^ 7 ≤
          (2 : ℝ) ^ 7 * ((Nat.factorial 7 : ℝ) * Real.exp x) :=
        mul_le_mul_of_nonneg_left hxpow (by positivity)
      _ = (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp x := by ring
  have hexpcombine : Real.exp x * Real.exp (-|t|) =
      Real.exp (1 / 2) * Real.exp (-|t| / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [x]
    ring
  unfold principalRawDetector gammaMellinWeight
  change ‖Complex.Gamma ((a : ℂ) + t * I) *
      (Y : ℂ) ^ ((a : ℂ) + t * I) *
      riemannZeta (rho + ((a : ℂ) + t * I)) *
      mollifier chiOne U (rho + ((a : ℂ) + t * I))‖ ≤ _
  repeat' rw [norm_mul]
  calc
    ‖Complex.Gamma ((a : ℂ) + t * I)‖ *
          ‖(Y : ℂ) ^ ((a : ℂ) + t * I)‖ *
          ‖riemannZeta (rho + ((a : ℂ) + t * I))‖ *
          ‖mollifier chiOne U (rho + ((a : ℂ) + t * I))‖ ≤
        (12 * (1 + |t|) * Real.exp (-|t|)) * 1 *
          (3200 * C ^ 6 * (1 + |t|) ^ 6) * (U + 1) := by
      gcongr
    _ = (12 * 3200 * (U + 1) * C ^ 6) *
          ((1 + |t|) ^ 7 * Real.exp (-|t|)) := by ring
    _ ≤ (12 * 3200 * (U + 1) * C ^ 6) *
          (((2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp x) *
            Real.exp (-|t|)) := by
      gcongr
    _ = (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
          (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
        Real.exp (-|t| / 2) := by
      calc
        (12 * 3200 * (U + 1) * C ^ 6) *
              (((2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp x) *
                Real.exp (-|t|)) =
            (12 * 3200 * (U + 1) * C ^ 6 * (2 : ℝ) ^ 7 *
              (Nat.factorial 7 : ℝ)) *
                (Real.exp x * Real.exp (-|t|)) := by ring
        _ = (12 * 3200 * (U + 1) * C ^ 6 * (2 : ℝ) ^ 7 *
              (Nat.factorial 7 : ℝ)) *
                (Real.exp (1 / 2) * Real.exp (-|t| / 2)) := by
          rw [hexpcombine]
        _ = _ := by dsimp [C]; ring

/-- Continuity of the raw principal detector on the shifted line.  We use the
certified pole subtraction, so continuity at the ordinate aligned with the
zeta pole does not require treating a meromorphic expression as analytic. -/
theorem continuous_principalRawDetector_left
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 0 < Y) :
    Continuous (fun t : ℝ =>
      principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) := by
  let a : ℝ := 1 / 2 - rho.re
  have hfun : (fun t : ℝ =>
      principalRawDetector rho U Y ((a : ℂ) + t * I)) =
      (fun t : ℝ =>
        principalPoleRemovedDetector rho U Y ((a : ℂ) + t * I) +
          principalDetectorResidue rho U Y *
            (((a : ℂ) + t * I) - principalPoleLocation rho)⁻¹) := by
    funext t
    apply principalRawDetector_eq_poleRemoved_add hrho
    · intro hz
      have hre := congrArg Complex.re hz
      simp [a] at hre
      linarith
    · intro hp
      have hre := congrArg Complex.re hp
      simp [a, principalPoleLocation] at hre
  rw [show (fun t : ℝ => principalRawDetector rho U Y
      (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) =
      (fun t : ℝ => principalRawDetector rho U Y ((a : ℂ) + t * I)) by
        rfl, hfun]
  apply Continuous.add
  · rw [continuous_iff_continuousAt]
    intro t
    have hstrip : ((a : ℂ) + t * I) ∈
        MAPAppendixA4Detector.contourStrip := by
      change -1 < (((a : ℂ) + t * I).re)
      simp [a]
      linarith
    exact (analyticAt_principalPoleRemovedDetector hY hbetaHigh hstrip).continuousAt.comp_of_eq
      (by fun_prop) rfl
  · apply continuous_const.mul
    apply Continuous.inv₀ (by fun_prop)
    intro t ht
    have hre := congrArg Complex.re ht
    simp [a, principalPoleLocation] at hre
    norm_num at hre

/-- The shifted left vertical line is integrable premise-free once `rho` is a
zero of the regularized principal function. -/
theorem integrable_principalRawDetector_left
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Integrable (fun t : ℝ =>
      principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) := by
  let f : ℝ → ℂ := fun t => principalRawDetector rho U Y
    (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)
  let K : ℝ := 12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
    (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hcont : Continuous f := by
    simpa [f] using continuous_principalRawDetector_left hrho hbetaLow
      hbetaHigh U (lt_of_lt_of_le zero_lt_one hY)
  have hupperMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((-1 / 2 : ℝ) * t)) (Set.Ioi 1) :=
    (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) 1).const_mul K
  have hlowerMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((1 / 2 : ℝ) * t)) (Set.Iic (-1)) :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-1)).const_mul K
  have hupper : IntegrableOn f (Set.Ioi 1) := by
    apply Integrable.mono' hupperMajor hcont.aestronglyMeasurable.restrict
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := lt_trans zero_lt_one ht
    have htlarge : 1 ≤ |t| := by rw [abs_of_pos htpos]; exact ht.le
    have hp := norm_principalRawDetector_left_le_exp_polynomial_height
      hbetaLow hbetaHigh U hY (t := t) htlarge
    rw [abs_of_pos htpos] at hp
    simpa [f, K, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp
  have hlower : IntegrableOn f (Set.Iic (-1)) := by
    apply Integrable.mono' hlowerMajor hcont.aestronglyMeasurable.restrict
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
    change t ≤ -1 at ht
    have htnonpos : t ≤ 0 := by linarith
    have htlarge : 1 ≤ |t| := by rw [abs_of_nonpos htnonpos]; linarith
    have hp := norm_principalRawDetector_left_le_exp_polynomial_height
      hbetaLow hbetaHigh U hY (t := t) htlarge
    rw [abs_of_nonpos htnonpos] at hp
    simpa [f, K, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp
  have hmiddle : IntegrableOn f (Set.Icc (-1) 1) := hcont.integrableOn_Icc
  have htoOne := hlower.union hmiddle
  rw [Set.Iic_union_Icc (by norm_num : min (-1 : ℝ) 1 ≤ -1),
    max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)] at htoOne
  have hall := htoOne.union hupper
  rw [Set.Iic_union_Ioi] at hall
  exact MeasureTheory.integrableOn_univ.mp hall

/-- On the shifted line the modulus-one Dirichlet `L`-function is literally
zeta, so the shared post-A.5 critical-line integral can be reused unchanged. -/
theorem principalRawDetector_left_eq_gammaLeft
    (rho : ℂ) (U : ℕ) (Y t : ℝ) :
    principalRawDetector rho U Y
        (((1 / 2 - rho.re : ℝ) : ℂ) + t * I) =
      gammaLeftIntegrand chiOne U rho Y t := by
  unfold principalRawDetector gammaLeftIntegrand
  dsimp only
  rw [DirichletCharacter.LFunction_modOne_eq]

/-- Quantitative two-tail estimate for the principal shifted line. -/
theorem norm_principalGammaLeft_two_tails_le_exp_polynomial_height
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B : ℝ} (hY : 1 ≤ Y) (hB : 1 ≤ B) :
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t‖ ≤
      4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-B / 2) := by
  let K : ℝ := 12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
    (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hupperMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((-1 / 2 : ℝ) * t)) (Set.Ioi B) :=
    (integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B).const_mul K
  have hlowerMajor : IntegrableOn
      (fun t : ℝ => K * Real.exp ((1 / 2 : ℝ) * t)) (Set.Iic (-B)) :=
    (integrableOn_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)).const_mul K
  have hupper :
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t‖ ≤
          ∫ t : ℝ in Set.Ioi B, K * Real.exp ((-1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hupperMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        change B < t at ht
        have htpos : 0 < t := lt_of_le_of_lt (by linarith : 0 ≤ B) ht
        have htlarge : 1 ≤ |t| := by rw [abs_of_pos htpos]; linarith
        have hp := norm_principalRawDetector_left_le_exp_polynomial_height
          hbetaLow hbetaHigh U hY (t := t) htlarge
        rw [principalRawDetector_left_eq_gammaLeft, abs_of_pos htpos] at hp
        simpa [K, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp
      _ = K * (-Real.exp ((-1 / 2 : ℝ) * B) / (-1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) B]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (-1 / 2 : ℝ) * B = -B / 2 by ring]
        ring
  have hlower :
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t‖ ≤
        2 * K * Real.exp (-B / 2) := by
    calc
      ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t‖ ≤
          ∫ t : ℝ in Set.Iic (-B), K * Real.exp ((1 / 2 : ℝ) * t) := by
        apply MeasureTheory.norm_integral_le_of_norm_le hlowerMajor
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
        change t ≤ -B at ht
        have htnonpos : t ≤ 0 := by linarith
        have htlarge : 1 ≤ |t| := by
          rw [abs_of_nonpos htnonpos]
          linarith
        have hp := norm_principalRawDetector_left_le_exp_polynomial_height
          hbetaLow hbetaHigh U hY (t := t) htlarge
        rw [principalRawDetector_left_eq_gammaLeft, abs_of_nonpos htnonpos] at hp
        simpa [K, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp
      _ = K * (Real.exp ((1 / 2 : ℝ) * (-B)) / (1 / 2 : ℝ)) := by
        rw [MeasureTheory.integral_const_mul,
          integral_exp_mul_Iic (a := (1 / 2 : ℝ)) (by norm_num) (-B)]
      _ = 2 * K * Real.exp (-B / 2) := by
        rw [show (1 / 2 : ℝ) * (-B) = -B / 2 by ring]
        ring
  calc
    ‖(∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t) +
        ∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t‖ ≤
        ‖∫ t : ℝ in Set.Iic (-B), gammaLeftIntegrand chiOne U rho Y t‖ +
          ‖∫ t : ℝ in Set.Ioi B, gammaLeftIntegrand chiOne U rho Y t‖ :=
      norm_add_le _ _
    _ ≤ 2 * K * Real.exp (-B / 2) + 2 * K * Real.exp (-B / 2) :=
      add_le_add hlower hupper
    _ = 4 * (12 * 3200 * (U + 1) * (4 + |rho.im|) ^ 6 *
        (2 : ℝ) ^ 7 * (Nat.factorial 7 : ℝ) * Real.exp (1 / 2)) *
          Real.exp (-B / 2) := by
      dsimp [K]
      ring

/-- Principal zeta on either horizontal side.  Once the side lies at least
unit distance in ordinate from the pole, undoing `(s-1)zeta(s)` costs no
power of the height. -/
theorem norm_riemannZeta_principal_horizontal_le
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {x t : ℝ} (hxLow : 1 / 2 - rho.re ≤ x) (hxHigh : x ≤ 1 / 2)
    (ht : 1 ≤ |rho.im + t|) :
    ‖riemannZeta (rho + ((x : ℂ) + t * I))‖ ≤
      1600 * (5 + |rho.im| + |t|) ^ 6 := by
  let s : ℂ := rho + ((x : ℂ) + t * I)
  have hs1 : s ≠ 1 := by
    intro h
    have him := congrArg Complex.im h
    simp [s] at him
    rw [him, abs_zero] at ht
    norm_num at ht
  have hslo : -1 ≤ s.re := by simp [s]; linarith
  have hshi : s.re ≤ 2 := by simp [s]; linarith
  have hreg := MAPPrincipalZetaFixedStrip.norm_principalRegularized_fixedStrip_le
    (z := s) hslo hshi
  have hden : 1 ≤ ‖s - 1‖ := by
    have him := Complex.abs_im_le_norm (s - 1)
    have himEq : |(s - 1).im| = |rho.im + t| := by simp [s]
    rw [himEq] at him
    exact ht.trans him
  have him : |(s + 3).im| ≤ |rho.im| + |t| := by
    simp [s]
    exact abs_add_le rho.im t
  have hre : |(s + 3).re| ≤ 5 := by
    simp [s]
    rw [abs_of_nonneg] <;> linarith
  have hshift : ‖s + 3‖ ≤ 5 + |rho.im| + |t| := by
    calc
      ‖s + 3‖ ≤ |(s + 3).re| + |(s + 3).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 5 + (|rho.im| + |t|) := add_le_add hre him
      _ = 5 + |rho.im| + |t| := by ring
  have heq : principalF s = (s - 1) * riemannZeta s :=
    MAPPrincipalZetaFixedStrip.principalRegularized_apply_of_ne_one hs1
  change ‖riemannZeta s‖ ≤ _
  calc
    ‖riemannZeta s‖ ≤ ‖s - 1‖ * ‖riemannZeta s‖ := by
      nlinarith [mul_nonneg (norm_nonneg (s - 1))
        (norm_nonneg (riemannZeta s))]
    _ = ‖principalF s‖ := by rw [heq, norm_mul]
    _ ≤ 1600 * ‖s + 3‖ ^ 6 := hreg
    _ ≤ 1600 * (5 + |rho.im| + |t|) ^ 6 := by gcongr

/-- Common literal envelope for the two principal horizontal sides. -/
def principalHorizontalEnvelope (U : ℕ) (rho : ℂ) (Y B : ℝ) : ℝ :=
  (12 * (1 + B) * Real.exp (-B)) * Y ^ (1 / 2 : ℝ) *
    (1600 * (5 + |rho.im| + B) ^ 6) * (U + 1)

theorem norm_principalRawDetector_upper_le_envelope
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B x : ℝ} (hY : 1 ≤ Y)
    (hB : |rho.im| + 1 ≤ B)
    (hx : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2)) :
    ‖principalRawDetector rho U Y ((x : ℂ) + B * I)‖ ≤
      principalHorizontalEnvelope U rho Y B := by
  have hac : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
  have hx' : 1 / 2 - rho.re < x ∧ x ≤ 1 / 2 := by
    rw [Set.uIoc_of_le hac] at hx
    exact hx
  have hB1 : 1 ≤ B := by linarith [abs_nonneg rho.im]
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((x : ℂ) + B * I)‖ ≤
      12 * (1 + B) * Real.exp (-B) := by
    have hg := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      (a := x) (t := B) (by linarith [hx'.1]) hx'.2
      (by simpa [abs_of_nonneg hB0] using hB1)
    simpa [GammaCompactStripScratch.stripPoint, abs_of_nonneg hB0] using hg
  have hYpow : ‖(Y : ℂ) ^ ((x : ℂ) + B * I)‖ ≤ Y ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero, add_zero]
    exact Real.rpow_le_rpow_of_exponent_le hY hx'.2
  have hord : 1 ≤ |rho.im + B| := by
    have htri := abs_add_le (rho.im + B) (-rho.im)
    have hrewrite : (rho.im + B) + (-rho.im) = B := by ring
    have : B ≤ |rho.im + B| + |rho.im| := by
      rw [hrewrite, abs_of_nonneg hB0, abs_neg] at htri
      exact htri
    linarith
  have hzeta0 := norm_riemannZeta_principal_horizontal_le hbetaLow hbetaHigh
    hx'.1.le hx'.2 hord
  have hzeta : ‖riemannZeta (rho + ((x : ℂ) + B * I))‖ ≤
      1600 * (5 + |rho.im| + B) ^ 6 := by
    simpa [abs_of_nonneg hB0] using hzeta0
  have hmoll : ‖mollifier chiOne U (rho + ((x : ℂ) + B * I))‖ ≤ U + 1 := by
    apply norm_mollifier_le_card
    simp
    linarith [hx'.1]
  unfold principalRawDetector gammaMellinWeight principalHorizontalEnvelope
  repeat' rw [norm_mul]
  gcongr

theorem norm_principalRawDetector_lower_le_envelope
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y B x : ℝ} (hY : 1 ≤ Y)
    (hB : |rho.im| + 1 ≤ B)
    (hx : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2)) :
    ‖principalRawDetector rho U Y ((x : ℂ) - B * I)‖ ≤
      principalHorizontalEnvelope U rho Y B := by
  have hac : 1 / 2 - rho.re ≤ (1 / 2 : ℝ) := by linarith
  have hx' : 1 / 2 - rho.re < x ∧ x ≤ 1 / 2 := by
    rw [Set.uIoc_of_le hac] at hx
    exact hx
  have hB1 : 1 ≤ B := by linarith [abs_nonneg rho.im]
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  have hgamma : ‖Complex.Gamma ((x : ℂ) - B * I)‖ ≤
      12 * (1 + B) * Real.exp (-B) := by
    have hg := GammaCompactStripScratch.norm_Gamma_compactStrip_le_exp
      (a := x) (t := -B) (by linarith [hx'.1]) hx'.2
      (by simpa [abs_of_nonneg hB0] using hB1)
    simpa [GammaCompactStripScratch.stripPoint, abs_of_nonneg hB0, sub_eq_add_neg] using hg
  have hYpow : ‖(Y : ℂ) ^ ((x : ℂ) - B * I)‖ ≤ Y ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul,
      sub_zero]
    exact Real.rpow_le_rpow_of_exponent_le hY hx'.2
  have hord : 1 ≤ |rho.im - B| := by
    have htri := abs_add_le (rho.im - B) (-rho.im)
    have hrewrite : (rho.im - B) + (-rho.im) = -B := by ring
    have : B ≤ |rho.im - B| + |rho.im| := by
      rw [hrewrite, abs_neg, abs_of_nonneg hB0, abs_neg] at htri
      exact htri
    linarith
  have hzeta0 := norm_riemannZeta_principal_horizontal_le hbetaLow hbetaHigh
    (t := -B) hx'.1.le hx'.2 (by simpa [sub_eq_add_neg] using hord)
  have hzeta : ‖riemannZeta (rho + ((x : ℂ) - B * I))‖ ≤
      1600 * (5 + |rho.im| + B) ^ 6 := by
    simpa [sub_eq_add_neg, abs_of_nonneg hB0] using hzeta0
  have hmoll : ‖mollifier chiOne U (rho + ((x : ℂ) - B * I))‖ ≤ U + 1 := by
    apply norm_mollifier_le_card
    simp
    linarith [hx'.1]
  unfold principalRawDetector gammaMellinWeight principalHorizontalEnvelope
  repeat' rw [norm_mul]
  simpa [sub_eq_add_neg] using
    (show ‖Complex.Gamma ((x : ℂ) - B * I)‖ *
        ‖(Y : ℂ) ^ ((x : ℂ) - B * I)‖ *
        ‖riemannZeta (rho + ((x : ℂ) - B * I))‖ *
        ‖mollifier chiOne U (rho + ((x : ℂ) - B * I))‖ ≤
      (12 * (1 + B) * Real.exp (-B)) * Y ^ (1 / 2 : ℝ) *
        (1600 * (5 + |rho.im| + B) ^ 6) * (U + 1) by
      gcongr)

/-- The common principal horizontal envelope tends to zero. -/
theorem tendsto_principalHorizontalEnvelope_zero
    (U : ℕ) (rho : ℂ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (principalHorizontalEnvelope U rho Y) atTop (𝓝 0) := by
  let C : ℝ := 5 + |rho.im|
  let K : ℝ := 12 * Y ^ (1 / 2 : ℝ) * 1600 * (U + 1)
  let G : ℝ → ℝ := fun B =>
    K * Real.exp C * ((B + C) ^ 7 * Real.exp (-(B + C)))
  have hshift : Tendsto (fun B : ℝ => B + C) atTop atTop :=
    tendsto_atTop_add_const_right atTop C tendsto_id
  have hpoly : Tendsto (fun B : ℝ =>
      (B + C) ^ 7 * Real.exp (-(B + C))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 7).comp hshift
  have hG : Tendsto G atTop (𝓝 0) := by
    simpa [G] using hpoly.const_mul (K * Real.exp C)
  apply squeeze_zero' (g := G)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    unfold principalHorizontalEnvelope
    positivity
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    have hC : 1 ≤ C := by dsimp [C]; linarith [abs_nonneg rho.im]
    have hbase : 0 ≤ C + B := by linarith
    have hone : 1 + B ≤ C + B := by linarith
    have hpow : (1 + B) * (C + B) ^ 6 ≤ (C + B) ^ 7 := by
      calc
        (1 + B) * (C + B) ^ 6 ≤ (C + B) * (C + B) ^ 6 :=
          mul_le_mul_of_nonneg_right hone (by positivity)
        _ = (C + B) ^ 7 := by ring
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hexp : 0 ≤ Real.exp (-B) := Real.exp_pos _ |>.le
    have hrewrite : Real.exp C * Real.exp (-(B + C)) = Real.exp (-B) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      principalHorizontalEnvelope U rho Y B =
          K * ((1 + B) * (C + B) ^ 6 * Real.exp (-B)) := by
        dsimp [principalHorizontalEnvelope, C, K]
        ring
      _ ≤ K * ((C + B) ^ 7 * Real.exp (-B)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpow hexp) hK
      _ = G B := by
        rw [← hrewrite]
        dsimp [G]
        ring
  · exact hG

theorem tendsto_principalRawDetector_upper_horizontal_zero
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        principalRawDetector rho U Y (x + B * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let W : ℝ := |(1 / 2 : ℝ) - (1 / 2 - rho.re)|
  have henv := (tendsto_principalHorizontalEnvelope_zero U rho hY).mul_const W
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (|rho.im| + 1)] with B hB
    exact MAPAppendixA4Detector.horizontal_segment_norm_le
      (principalRawDetector rho U Y)
      (B := B) (M := principalHorizontalEnvelope U rho Y B)
      (fun x hx => norm_principalRawDetector_upper_le_envelope
        hbetaLow hbetaHigh U hY hB hx)
  · simpa [W] using henv

theorem tendsto_principalRawDetector_lower_horizontal_zero
    {rho : ℂ} (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    Tendsto (fun B : ℝ =>
      ∫ x : ℝ in (1 / 2 - rho.re)..(1 / 2),
        principalRawDetector rho U Y (x - B * I)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let W : ℝ := |(1 / 2 : ℝ) - (1 / 2 - rho.re)|
  have henv := (tendsto_principalHorizontalEnvelope_zero U rho hY).mul_const W
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun B => norm_nonneg _
  · filter_upwards [eventually_ge_atTop (|rho.im| + 1)] with B hB
    simpa [sub_eq_add_neg] using
      (MAPAppendixA4Detector.horizontal_segment_norm_le
        (principalRawDetector rho U Y)
        (B := -B) (M := principalHorizontalEnvelope U rho Y B)
        (fun x hx => by
          have hx' : x ∈ Set.uIoc (1 / 2 - rho.re) (1 / 2) := by
            simpa only [one_div, sub_eq_add_neg] using hx
          have hb := norm_principalRawDetector_lower_le_envelope
            hbetaLow hbetaHigh U hY hB hx'
          simpa [sub_eq_add_neg] using hb))
  · simpa [W] using henv

/-- Premise-free infinite principal contour shift with the exact crossed-pole
residue. -/
theorem principalRawDetector_full_vertical_identity_unconditional
    {rho : ℂ} (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    (U : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    (∫ t : ℝ,
        principalRawDetector rho U Y (((1 / 2 : ℝ) : ℂ) + t * I)) =
      (∫ t : ℝ,
        principalRawDetector rho U Y
          (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) +
        2 * Real.pi * principalDetectorResidue rho U Y := by
  apply principalRawDetector_full_vertical_identity hrho hbetaLow hbetaHigh
    (lt_of_lt_of_le zero_lt_one hY)
  · exact integrable_principalRawDetector_left hrho hbetaLow hbetaHigh U hY
  · exact integrable_principalRawDetector_right (by linarith) U
      (lt_of_lt_of_le zero_lt_one hY)
  · exact tendsto_principalRawDetector_lower_horizontal_zero
      hbetaLow hbetaHigh U hY
  · exact tendsto_principalRawDetector_upper_horizontal_zero
      hbetaLow hbetaHigh U hY

/-- Complete principal Appendix A.4 identity.  Relative to the nonprincipal
formula there is exactly one additional term: the displayed zeta-pole
residue. -/
theorem literal_principal_A4_full_identity
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 1 / 2 < rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          arithmeticDetectorTerm chiOne U rho Y n =
      principalDetectorResidue rho U Y +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, principalRawDetector rho U Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + t * I)) := by
  have hright := MAPAppendixA4GammaEndpoint.literal_A4_right_line_identity
    chiOne hU (by linarith : 1 / 2 < rho.re)
      (lt_of_lt_of_le zero_lt_one hY)
  have hrightEq :
      (∫ t : ℝ, gammaRightIntegrand chiOne U rho Y t) =
        ∫ t : ℝ, principalRawDetector rho U Y
          (((1 / 2 : ℝ) : ℂ) + t * I) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun t =>
      (principalRawDetector_right_eq_gammaRight rho U Y t).symm
  have hshift := principalRawDetector_full_vertical_identity_unconditional
    hrho hbetaLow hbetaHigh U hY
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscalar : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (2 * Real.pi * principalDetectorResidue rho U Y)) =
        principalDetectorResidue rho U Y := by
    push_cast
    field_simp [hpi]
  rw [hright, hrightEq, hshift, mul_add, hscalar, add_comm]

end
end MAPPrincipalZetaContourTails

#print axioms MAPPrincipalZetaContourTails.integrable_principalRawDetector_right
#print axioms MAPPrincipalZetaContourTails.norm_riemannZeta_criticalLine_le
#print axioms MAPPrincipalZetaContourTails.integrable_principalRawDetector_left
#print axioms MAPPrincipalZetaContourTails.tendsto_principalRawDetector_upper_horizontal_zero
#print axioms MAPPrincipalZetaContourTails.tendsto_principalRawDetector_lower_horizontal_zero
#print axioms MAPPrincipalZetaContourTails.literal_principal_A4_full_identity
