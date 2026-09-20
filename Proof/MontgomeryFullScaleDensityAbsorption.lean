import MontgomeryPrincipalFullScaleThinning
import MontgomeryFullStripFourier
import MontgomeryMixedMomentLowStrip
import PostA5LongSpacingAssembly
import RamachandraTheorem6ShiftedStripSource
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Full-scale Montgomery density envelope normalization

These are scalar and asymptotic bounds for the explicit Type-I / mixed
Type-II budgets. No zero-count estimate is assumed as a density theorem.
The source logarithms, imprimitive conductor exponential, and thinning
height loss remain visible until the final polylogarithmic absorption.
-/
namespace MAPMontgomeryFullScaleDensityAbsorption
open Filter
open MAPMontgomeryLowStrip MAPMontgomeryMixedMomentLowStrip
open MAPMontgomeryPoweredSourceExponentLedger
open ZeroDensityArithmetic
open RamachandraTheorem6ShiftedStripSource
open scoped BigOperators
noncomputable section

theorem fullScale_log_envelope_absorption_at_scale
    {K eta kappa T sigma : ℝ} {q : ℕ} [NeZero q] (m : ℕ)
    (hK : 0 < K) (heta : 0 < eta) (hT : Real.exp 1 ≤ T)
    (hq : (q : ℝ) ≤ Real.rpow (Real.log T) K)
    (hthreshold : K ≤ Real.log (Real.log T))
    (hpoly : Real.rpow (Real.log T) (K+(m:ℝ)+1) ≤ Real.rpow T (eta/2))
    (hkappa : kappa ≤ eta/2)
    (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10) :
    Real.rpow T kappa * Real.rpow ((q : ℝ)*T) (inghamExponent sigma) *
      (1+Real.log ((q : ℝ)*T))^m * Real.exp (Real.sqrt (Real.log (q : ℝ))) ≤
      (K+2)^m * Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  have hTp : 0 < T := (Real.exp_pos _).trans_le hT
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hlog1 : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hT
    simpa using h
  have hlogp : 0 < Real.log T := zero_lt_one.trans_le hlog1
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hSp : 0 < (q:ℝ)*T := mul_pos (lt_of_lt_of_le zero_lt_one hq1) hTp
  have hS1 : 1 ≤ (q:ℝ)*T := one_le_mul_of_one_le_of_one_le hq1 hT1
  have ha0 := inghamExponent_nonneg hslo hshi
  have ha1 := inghamExponent_le_one hslo hshi
  have hlog := log_conductor_mul_height_le hK hT hq
  have hlogBound : 1+Real.log ((q:ℝ)*T) ≤ (K+2)*Real.log T := by nlinarith
  have hlog0 : 0 ≤ 1+Real.log ((q:ℝ)*T) := by linarith [Real.log_nonneg hS1]
  have hlogpow : (1+Real.log ((q:ℝ)*T))^m ≤ (K+2)^m * (Real.log T)^m := by
    simpa only [mul_pow] using pow_le_pow_left₀ hlog0 hlogBound m
  have hexp := exp_sqrt_log_conductor_le_log hK.le
    (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) hT) hthreshold hq
  have hscale : Real.rpow ((q:ℝ)*T) (inghamExponent sigma) ≤
      Real.rpow (Real.log T) K * Real.rpow T (inghamExponent sigma) := by
    calc
      _ = Real.rpow (q:ℝ) (inghamExponent sigma) * Real.rpow T (inghamExponent sigma) :=
        Real.mul_rpow (by positivity) hTp.le
      _ ≤ (q:ℝ)*Real.rpow T (inghamExponent sigma) :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hq1 ha1)
          (Real.rpow_nonneg hTp.le _)
      _ ≤ _ := mul_le_mul_of_nonneg_right hq (Real.rpow_nonneg hTp.le _)
  have hlogCombine : Real.rpow (Real.log T) K * (Real.log T)^m * Real.log T =
      Real.rpow (Real.log T) (K+(m:ℝ)+1) := by
    rw [← Real.rpow_natCast (Real.log T) m]
    calc
      _ = Real.rpow (Real.log T) (K+(m:ℝ)) * Real.rpow (Real.log T) 1 := by
        simp only [Real.rpow_eq_pow]
        rw [Real.rpow_add hlogp]; norm_num
      _ = _ := (Real.rpow_add hlogp _ _).symm
  have hsmall : Real.rpow T kappa * Real.rpow (Real.log T) (K+(m:ℝ)+1) ≤
      Real.rpow T eta := by
    calc
      _ ≤ Real.rpow T kappa * Real.rpow T (eta/2) :=
        mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hTp.le _)
      _ = Real.rpow T (kappa+eta/2) := (Real.rpow_add hTp _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hT1 (by linarith)
  calc
    _ ≤ (Real.rpow T kappa *
        (Real.rpow (Real.log T) K * Real.rpow T (inghamExponent sigma))) *
        ((K+2)^m*(Real.log T)^m) * Real.log T := by
      apply mul_le_mul _ hexp (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg hTp.le _)
          (mul_nonneg (Real.rpow_nonneg hlogp.le _) (Real.rpow_nonneg hTp.le _)))
          (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg hlogp.le _)))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hscale (Real.rpow_nonneg hTp.le _))
        hlogpow (pow_nonneg hlog0 _)
        (mul_nonneg (Real.rpow_nonneg hTp.le _)
          (mul_nonneg (Real.rpow_nonneg hlogp.le _) (Real.rpow_nonneg hTp.le _)))
    _ = (K+2)^m * Real.rpow T (inghamExponent sigma) *
        (Real.rpow T kappa * Real.rpow (Real.log T) (K+(m:ℝ)+1)) := by
      rw [← hlogCombine]; ring
    _ ≤ (K+2)^m * Real.rpow T (inghamExponent sigma) * Real.rpow T eta :=
      mul_le_mul_of_nonneg_left hsmall
        (mul_nonneg (pow_nonneg (by linarith) _) (Real.rpow_nonneg hTp.le _))
    _ = (K+2)^m * Real.rpow T (inghamExponent sigma+eta) := by
      rw [mul_assoc]; congr 1; exact (Real.rpow_add hTp _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT1 (inghamExponent_le_uniformExponent hslo hshi))
      (pow_nonneg (by linarith) _)

/-- Uniform arbitrary-fixed-log absorption, including the complete source
`exp(sqrt(log q))` loss and a separately budgeted Fourier thinning power. -/
theorem eventually_fullScale_log_envelope_absorption
    {K eta : ℝ} (hK : 0 < K) (heta : 0 < eta) (m : ℕ) :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma kappa : ℝ),
      (q:ℝ) ≤ Real.rpow (Real.log T) K → kappa ≤ eta/2 →
      1/2 ≤ sigma → sigma ≤ 7/10 →
      Real.rpow T kappa * Real.rpow ((q:ℝ)*T) (inghamExponent sigma) *
        (1+Real.log ((q:ℝ)*T))^m * Real.exp (Real.sqrt (Real.log (q:ℝ))) ≤
        (K+2)^m * Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    eventually_ge_atTop (Real.exp (Real.exp K)),
    polylog_absorption (K+(m:ℝ)+1) (eta/2) (by linarith)] with T hT hTT hp
  intro q _ sigma kappa hq hk hslo hshi
  exact fullScale_log_envelope_absorption_at_scale m hK heta hT hq
    (loglog_threshold_of_exp_exp_le hTT) hp hk hslo hshi

/-- Full-scale cutoff powers normalize to the Ingham exponent. -/
theorem cutoff_rpow_le_fullScale
    {S sigma L N : ℝ} (hS : 1 ≤ S) (hL : 1 ≤ L)
    (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10) (hN0 : 0 ≤ N)
    (hN : N ≤ 2 * Real.rpow S (sourceYExponent sigma) * L^2) :
    Real.rpow N (2*(1-sigma)) ≤
      2 * Real.rpow S (inghamExponent sigma) * L^2 := by
  let p := 2*(1-sigma)
  let Y := Real.rpow S (sourceYExponent sigma)
  have hp0 : 0 ≤ p := by dsimp [p]; linarith
  have hp1 : p ≤ 1 := by dsimp [p]; linarith
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hLp : 0 ≤ L := by linarith
  have hYp : Real.rpow Y p = Real.rpow S (inghamExponent sigma) := by
    calc
      _ = Real.rpow S (sourceYExponent sigma * (2*(1-sigma))) :=
        (Real.rpow_mul (by linarith) _ _).symm
      _ = _ := by rw [powered_length_exponent_eq_ingham (by linarith)]
  calc
    _ ≤ Real.rpow (2*Y*L^2) p := Real.rpow_le_rpow hN0 hN hp0
    _ = Real.rpow 2 p * Real.rpow Y p * Real.rpow (L^2) p := by
      simp only [Real.rpow_eq_pow]
      rw [Real.mul_rpow (mul_nonneg (by norm_num) hY0) (sq_nonneg _),
        Real.mul_rpow (by norm_num : (0:ℝ)≤2) hY0]
    _ ≤ 2 * Real.rpow Y p * L^2 := by
      apply mul_le_mul _ (Real.rpow_le_self_of_one_le (one_le_pow₀ hL) hp1)
        (Real.rpow_nonneg (sq_nonneg _) _) (mul_nonneg (by norm_num) (Real.rpow_nonneg hY0 _))
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le (by norm_num : (1:ℝ)≤2) hp1)
        (Real.rpow_nonneg hY0 _)
    _ = _ := by rw [hYp]

/-- Exact Type-I finite budget, including both occurrences of the dyadic
count and the retained Fourier constant. -/
theorem typeI_count_normalization
    {S sigma L N J A D R : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10)
    (hN0 : 0 ≤ N) (hN : N ≤ 2*Real.rpow S (sourceYExponent sigma)*L^2)
    (hJ : 0 < J) (hJL : J ≤ L) (hA : 0 < A) (hD : 0 ≤ D)
    (hlog0 : 0 ≤ 1+Real.log (2*N)) (hlog : 1+Real.log (2*N) ≤ L)
    (hcount : R*((1/8:ℝ)/(4*A*J))^2 ≤
      J^2*D*Real.rpow N (2*(1-sigma))*(1+Real.log (2*N))^4) :
    R ≤ (2048*A^2*D)*Real.rpow S (inghamExponent sigma)*L^10 := by
  have hinv : ((1/8:ℝ)/(4*A*J))^2 * (32*A*J)^2 = 1 := by
    field_simp; ring
  have hNp0 : 0 ≤ Real.rpow N (2*(1-sigma)) := Real.rpow_nonneg hN0 _
  have hn := cutoff_rpow_le_fullScale hS hL hslo hshi hN0 hN
  have hE0 : 0 ≤ Real.rpow S (inghamExponent sigma) := Real.rpow_nonneg (by linarith) _
  have hL0 : 0 ≤ L := by linarith
  calc
    R = (R*((1/8:ℝ)/(4*A*J))^2)*(32*A*J)^2 := by rw [mul_assoc, hinv, mul_one]
    _ ≤ (J^2*D*Real.rpow N (2*(1-sigma))*(1+Real.log (2*N))^4)*(32*A*J)^2 :=
      mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = (1024*A^2*D)*J^4*Real.rpow N (2*(1-sigma))*(1+Real.log (2*N))^4 := by ring
    _ ≤ (1024*A^2*D)*L^4*(2*Real.rpow S (inghamExponent sigma)*L^2)*L^4 := by
      gcongr
    _ = _ := by ring

/-- Taking the cube root pays 135 logarithms for the literal 400-log
fourth-moment source, its second-moment logarithms and the weight mass. -/
theorem cubic_count_normalization
    {R E L F C : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E) (hL : 1 ≤ L)
    (hF : 1 ≤ F) (hC : 0 ≤ C)
    (hcount : R^3 ≤ C * E^3 * L^404 * F) :
    R ≤ (C+1)*E*L^135*F := by
  have hL0 : 0 ≤ L := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hCp : C ≤ (C+1)^3 := by nlinarith [sq_nonneg C, mul_nonneg hC (sq_nonneg C)]
  have hLp : L^404 ≤ L^405 := pow_le_pow_right₀ hL (by norm_num)
  have hFp : F ≤ F^3 := by
    have h := pow_le_pow_right₀ hF (show 1≤3 by norm_num)
    simpa using h
  apply (pow_le_pow_iff_left₀ hR (by positivity) (show (3:ℕ)≠0 by decide)).mp
  calc
    R^3 ≤ C*E^3*L^404*F := hcount
    _ ≤ (C+1)^3*E^3*L^405*F^3 := by gcongr
    _ = ((C+1)*E*L^135*F)^3 := by ring

/-- Literal mixed Type-II budget normalized before any conductor or
logarithmic absorption. All scalar inputs are visible. -/
theorem typeII_count_normalization
    {S sigma L U S2 mass G C6 R : ℝ}
    (hS : 1 ≤ S) (hL : 1 ≤ L) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10)
    (hU0 : 0 ≤ U) (hU : U ≤ 11*S) (hS20 : 1 ≤ S2) (hS2 : S2 ≤ 2*S)
    (hm0 : 0 ≤ mass) (hm : mass ≤ L^2) (hG : 0 ≤ G) (hC6 : 0 ≤ C6)
    (hl20 : 0 ≤ Real.log S2) (hl2 : Real.log S2 ≤ L)
    (hlU0 : 0 ≤ 1+Real.log U) (hlU : 1+Real.log U ≤ L)
    {F : ℝ} (hF : 1 ≤ F) (hR : 0 ≤ R)
    (hcount : R^3*(1/8:ℝ)^4 ≤
      (G*Real.rpow (Real.rpow S (sourceYExponent sigma)) (1/2-sigma))^4 * mass *
      (C6*S2*(Real.log S2)^400*F) * ((2*S2+8*Real.pi*U)*(1+Real.log U))^2) :
    R ≤ (8192*G^4*C6*(4+88*Real.pi)^2+1)*
      Real.rpow S (inghamExponent sigma)*L^135*F := by
  have hS0 : 0 ≤ S := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hYp : 0 < Real.rpow S (sourceYExponent sigma) := Real.rpow_pos_of_pos (by linarith) _
  have hsecond : (2*S2+8*Real.pi*U)*(1+Real.log U) ≤ (4+88*Real.pi)*S*L := by
    have hfirst : 2*S2+8*Real.pi*U ≤ (4+88*Real.pi)*S := by nlinarith [Real.pi_pos]
    calc
      _ ≤ ((4+88*Real.pi)*S)*L := mul_le_mul hfirst hlU hlU0 (by positivity)
      _ = _ := by ring
  have hsecond0 : 0 ≤ (2*S2+8*Real.pi*U)*(1+Real.log U) := by positivity
  have hnorm :
      (G*Real.rpow (Real.rpow S (sourceYExponent sigma)) (1/2-sigma))^4 * mass *
      (C6*S2*(Real.log S2)^400*F) * ((2*S2+8*Real.pi*U)*(1+Real.log U))^2 ≤
      2*G^4*C6*(4+88*Real.pi)^2 *
        (Real.rpow S (inghamExponent sigma))^3 * L^404 * F := by
    calc
      _ ≤ (G*Real.rpow (Real.rpow S (sourceYExponent sigma)) (1/2-sigma))^4 * L^2 *
        (C6*(2*S)*L^400*F) * ((4+88*Real.pi)*S*L)^2 := by
          gcongr
      _ = 2*G^4*C6*(4+88*Real.pi)^2 *
        ((Real.rpow (Real.rpow S (sourceYExponent sigma)) (1/2-sigma))^4*S^3)*L^404*F := by ring
      _ = _ := by
        have hp : (Real.rpow (Real.rpow S (sourceYExponent sigma)) (1/2-sigma))^4 =
            Real.rpow (Real.rpow S (sourceYExponent sigma)) (2-4*sigma) := by
          calc
            _ = Real.rpow (Real.rpow S (sourceYExponent sigma)) ((1/2-sigma)*4) :=
              (Real.rpow_mul_natCast hYp.le (1/2-sigma) 4).symm
            _ = _ := by congr 1; ring
        rw [hp, fullScale_typeII_power_balance (by linarith) (by linarith)]
  apply cubic_count_normalization hR (Real.rpow_nonneg hS0 _) hL hF (by positivity)
  have h := hcount.trans hnorm
  simp only [Real.rpow_eq_pow] at h ⊢
  nlinarith only [h]

open MAPAppendixA4PostA5SetAdapter PostA5CrowdingDeterministic PostA5LongSpacingAssembly

/-- The full mollifier ceiling has no hidden conductor multiplier. -/
theorem full_mollifier_ceiling_bounds {S : ℝ} (hS : 1 ≤ S) :
    (1:ℝ) ≤ (⌈10*S⌉₊ : ℝ) ∧ (⌈10*S⌉₊ : ℝ) ≤ 11*S := by
  have h0 : 0 ≤ 10*S := by linarith
  have hlo := Nat.le_ceil (10*S)
  have hhi := Nat.ceil_lt_add_one h0
  constructor <;> linarith

/-- The exact detector ceiling, including its unit endpoint, is controlled
by the source Y power and two logarithms. -/
theorem full_detector_ceiling_bounds {S sigma : ℝ}
    (hS : Real.exp 1 ≤ S) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10) :
    let Y := Real.rpow S (sourceYExponent sigma)
    let N := ⌈Y*(Real.log S)^2⌉₊
    (1:ℝ) ≤ N ∧ (N:ℝ) ≤ 2*Y*(1+Real.log S)^2 ∧
      1+Real.log (2*(N:ℝ)) ≤ 7*(1+Real.log S) := by
  dsimp only
  let Y := Real.rpow S (sourceYExponent sigma)
  let N := ⌈Y*(Real.log S)^2⌉₊
  let L := 1+Real.log S
  have hS1 : 1 ≤ S := (Real.one_le_exp (by norm_num)).trans hS
  have hSp : 0 < S := zero_lt_one.trans_le hS1
  have hlog1 : 1 ≤ Real.log S := by
    have h := Real.log_le_log (Real.exp_pos 1) hS
    simpa using h
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hLp : 0 < L := by linarith
  have ha0 : 0 ≤ sourceYExponent sigma := by
    unfold sourceYExponent; apply div_nonneg (by norm_num); linarith
  have ha2 : sourceYExponent sigma ≤ 2 := by
    unfold sourceYExponent
    apply (div_le_iff₀ (by linarith : 0 < 2*(2-sigma))).mpr
    linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow hS1 ha0
  have hYp : 0 < Y := by linarith
  have hbase1 : 1 ≤ Y*(Real.log S)^2 :=
    one_le_mul_of_one_le_of_one_le hY1 (one_le_pow₀ hlog1)
  have hnlo : (1:ℝ) ≤ N := hbase1.trans (Nat.le_ceil _)
  have hnhi : (N:ℝ) ≤ 2*Y*L^2 := by
    have hn := Nat.ceil_lt_add_one (zero_le_one.trans hbase1)
    have hll : (Real.log S)^2 ≤ L^2 := by dsimp [L]; nlinarith
    have hyll : Y*(Real.log S)^2 ≤ Y*L^2 := mul_le_mul_of_nonneg_left hll hYp.le
    have hyl1 : 1 ≤ Y*L^2 := one_le_mul_of_one_le_of_one_le hY1 (one_le_pow₀ hL1)
    dsimp [N] at hn ⊢
    nlinarith
  refine ⟨hnlo, hnhi, ?_⟩
  change 1+Real.log (2*(N:ℝ)) ≤ 7*L
  have hnpos : (0:ℝ)<N := zero_lt_one.trans_le hnlo
  have hlogN : Real.log (2*(N:ℝ)) ≤ Real.log (4*Y*L^2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogY : Real.log Y = sourceYExponent sigma * Real.log S :=
    Real.log_rpow hSp _
  have hlogL := Real.log_le_sub_one_of_pos hLp
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4)
    norm_num at h; exact h
  rw [Real.log_mul (mul_pos (by norm_num) hYp).ne' (pow_pos hLp 2).ne',
    Real.log_mul (by norm_num : (4:ℝ)≠0) hYp.ne', Real.log_pow, hlogY] at hlogN
  have hmul := mul_le_mul_of_nonneg_right ha2 (by linarith : 0 ≤ Real.log S)
  dsimp [L] at *
  norm_num at hlogN
  linarith

/-- Real logarithmic control of the literal dyadic shell count. -/
theorem detectorDyadicCount_le_two_log {N : ℕ} (hN : 1 ≤ N) :
    (detectorDyadicCount N : ℝ) ≤ 2*(1+Real.log (2*(N:ℝ))) := by
  have hn1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hnp : (0:ℝ)<N := by linarith
  have hm : (N-1).log2 ≤ N.log2 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.log_mono_right (by omega)
  have hlog := Real.log2_le_logb N
  rw [Real.logb] at hlog
  have hlog2 : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogN : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hn1
  have hlogN2 : Real.log (N:ℝ) ≤ Real.log (2*(N:ℝ)) :=
    Real.log_le_log hnp (by linarith)
  have hdiv : Real.log (N:ℝ)/Real.log 2 ≤ 2*Real.log (N:ℝ) := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 2)).mpr
    nlinarith
  have hmR : ((N-1).log2:ℝ) ≤ (N.log2:ℝ) := by exact_mod_cast hm
  unfold detectorDyadicCount
  push_cast
  linarith

/-- Complete finite log certificates for the actual full-scale cutoffs. -/
theorem fullScale_parameter_log_certificates {S sigma : ℝ}
    (hS : Real.exp 1 ≤ S) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10) :
    let U := ⌈10*S⌉₊
    let N := ⌈Real.rpow S (sourceYExponent sigma)*(Real.log S)^2⌉₊
    let L := 20*(1+Real.log S)
    1 ≤ U ∧ 1 ≤ N ∧
      (U:ℝ) ≤ 11*S ∧
      (N:ℝ) ≤ 2*Real.rpow S (sourceYExponent sigma)*L^2 ∧
      (detectorDyadicCount N:ℝ) ≤ L ∧
      1+Real.log (2*(N:ℝ)) ≤ L ∧ 1+Real.log (U:ℝ) ≤ L := by
  dsimp only
  let U := ⌈10*S⌉₊
  let N := ⌈Real.rpow S (sourceYExponent sigma)*(Real.log S)^2⌉₊
  let L0 := 1+Real.log S
  have hS1 : 1 ≤ S := (Real.one_le_exp (by norm_num)).trans hS
  have hlog0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  have hL0 : 1 ≤ L0 := by dsimp [L0]; linarith
  obtain ⟨hU1,hUhi⟩ := full_mollifier_ceiling_bounds hS1
  obtain ⟨hN1,hNhi,hNlog⟩ := full_detector_ceiling_bounds hS hslo hshi
  have hUn : 1 ≤ U := by exact_mod_cast hU1
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hJ := detectorDyadicCount_le_two_log hNn
  have hUlog : Real.log (U:ℝ) ≤ Real.log 11 + Real.log S := by
    have h := Real.log_le_log (zero_lt_one.trans_le hU1) hUhi
    rwa [Real.log_mul (by norm_num : (11:ℝ)≠0) (by linarith : S≠0)] at h
  have h11 : Real.log 11 ≤ 10 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<11)
    norm_num at h; exact h
  refine ⟨hUn,hNn,hUhi,?_,?_,?_,?_⟩
  · apply hNhi.trans
    apply mul_le_mul_of_nonneg_left
    · apply pow_le_pow_left₀ (by linarith : 0 ≤ 1+Real.log S)
      linarith
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith : 0≤S) _)
  · change (detectorDyadicCount N:ℝ) ≤ 20*L0
    change 1+Real.log (2*(N:ℝ)) ≤ 7*L0 at hNlog
    linarith
  · change 1+Real.log (2*(N:ℝ)) ≤ 20*L0
    change 1+Real.log (2*(N:ℝ)) ≤ 7*L0 at hNlog
    linarith
  · dsimp [L0] at *
    linarith

def crowdingScaleConstant : ℝ :=
  (Real.log 3+Real.log 3200+2*Real.log 4+2)/Real.log (17/16)

theorem crowdingScaleConstant_pos : 0 < crowdingScaleConstant := by
  unfold crowdingScaleConstant
  apply div_pos
  · have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have h3200 : 0 < Real.log 3200 := Real.log_pos (by norm_num)
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  · exact Real.log_pos (by norm_num)

theorem crowdingEnvelope_fullScale_bound {q : ℕ} [NeZero q] {T : ℝ}
    (hT : 1 ≤ T) :
    0 ≤ certifiedA5CrowdingEnvelope q T ∧
      certifiedA5CrowdingEnvelope q T ≤ crowdingScaleConstant*(1+Real.log ((q:ℝ)*T)) := by
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqp : (0:ℝ)<q := by linarith
  have hTp : 0<T := by linarith
  have hS1 : 1 ≤ (q:ℝ)*T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hlogS0 : 0 ≤ Real.log ((q:ℝ)*T) := Real.log_nonneg hS1
  have hlogarg1 : 1 ≤ (q:ℝ)*(T+3) := by nlinarith
  have hlogarg0 := Real.log_nonneg hlogarg1
  have h3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h3200 : 0 < Real.log 3200 := Real.log_pos (by norm_num)
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hden : 0 < Real.log (17/16) := Real.log_pos (by norm_num)
  have hlog : Real.log ((q:ℝ)*(T+3)) ≤ Real.log 4 + Real.log ((q:ℝ)*T) := by
    have h := Real.log_le_log (mul_pos hqp (by linarith))
      (show (q:ℝ)*(T+3) ≤ 4*((q:ℝ)*T) by nlinarith)
    rwa [Real.log_mul (by norm_num : (4:ℝ)≠0) (mul_pos hqp hTp).ne'] at h
  constructor
  · unfold certifiedA5CrowdingEnvelope
    exact div_nonneg (by linarith) hden.le
  · unfold certifiedA5CrowdingEnvelope crowdingScaleConstant
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hden]
    nlinarith

theorem fullScale_thinning_envelope_bound {q : ℕ} [NeZero q] {T kappa : ℝ}
    (hT : 1 ≤ T) (hk : 0 ≤ kappa) :
    certifiedA5CrowdingEnvelope q T *
      ((longSpacingColorCount ((Real.log ((q:ℝ)*T))^2+2*(2*Real.pi*Real.rpow T kappa)+1) : ℝ) *
        (certifiedA5CrowdingNatCap q T : ℝ)) ≤
      (crowdingScaleConstant*(crowdingScaleConstant+1)*(8+12*Real.pi))*
        Real.rpow T kappa * (1+Real.log ((q:ℝ)*T))^4 := by
  let L := 1+Real.log ((q:ℝ)*T)
  let H := Real.rpow T kappa
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hS1 : 1 ≤ (q:ℝ)*T := one_le_mul_of_one_le_of_one_le hq1 hT
  have hlog0 := Real.log_nonneg hS1
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hH1 : 1 ≤ H := Real.one_le_rpow hT hk
  have hH0 : 0 ≤ H := by linarith
  obtain ⟨he0,he⟩ := crowdingEnvelope_fullScale_bound (q:=q) hT
  have hcap : (certifiedA5CrowdingNatCap q T : ℝ) ≤ (crowdingScaleConstant+1)*L := by
    have hh := Nat.ceil_lt_add_one he0
    unfold certifiedA5CrowdingNatCap
    rw [max_eq_right he0]
    dsimp [L] at *
    nlinarith
  have hB0 : 0 ≤ (Real.log ((q:ℝ)*T))^2+2*(2*Real.pi*H)+1 := by positivity
  have hc := Nat.ceil_lt_add_one
    (show 0 ≤ 3*((Real.log ((q:ℝ)*T))^2+2*(2*Real.pi*H)+1)+1 by positivity)
  have hLsq : (Real.log ((q:ℝ)*T))^2 ≤ L^2 := by dsimp [L]; nlinarith
  have hcolor : (longSpacingColorCount ((Real.log ((q:ℝ)*T))^2+2*(2*Real.pi*H)+1) : ℝ) ≤
      (8+12*Real.pi)*H*L^2 := by
    have hh1 : 1 ≤ L^2 := one_le_pow₀ hL1
    have hhl : H ≤ H*L^2 := le_mul_of_one_le_right hH0 hh1
    have hlh : L^2 ≤ H*L^2 := le_mul_of_one_le_left (sq_nonneg _) hH1
    have hhl1 : 1 ≤ H*L^2 := one_le_mul_of_one_le_of_one_le hH1 hh1
    unfold longSpacingColorCount
    nlinarith [Real.pi_pos]
  have hD0 := crowdingScaleConstant_pos.le
  have hcap0 : 0 ≤ (certifiedA5CrowdingNatCap q T : ℝ) := by positivity
  calc
    _ ≤ (crowdingScaleConstant*L)*(((8+12*Real.pi)*H*L^2)*((crowdingScaleConstant+1)*L)) := by
      apply mul_le_mul he _ (by positivity) (mul_nonneg hD0 hL0)
      exact mul_le_mul hcolor hcap hcap0 (by positivity)
    _ = _ := by dsimp [L,H]; ring

/-- The two normalized branches and the exact four-log thinning loss
combine without introducing an analytic count premise. -/
theorem combine_normalized_branches
    {RI RII thin CI CII D H E L F : ℝ}
    (hRI0 : 0 ≤ RI) (hRII0 : 0 ≤ RII) (hthin0 : 0 ≤ thin)
    (hCI : 0 ≤ CI) (hCII : 0 ≤ CII) (hD : 0 ≤ D) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hL : 1 ≤ L) (hF : 1 ≤ F)
    (hRI : RI ≤ CI*E*(20*L)^10)
    (hRII : RII ≤ CII*E*(20*L)^135*F)
    (hthin : thin ≤ D*H*L^4) :
    thin*(RI+RII) ≤ (D*(CI+CII)*20^135)*H*E*L^139*F := by
  have hL0 : 0 ≤ L := by linarith
  have hF0 : 0 ≤ F := by linarith
  have hp : (20*L)^10 ≤ (20*L)^135 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hi : RI ≤ CI*E*(20*L)^135*F := by
    calc
      _ ≤ CI*E*(20*L)^10 := hRI
      _ ≤ CI*E*(20*L)^135 := mul_le_mul_of_nonneg_left hp (mul_nonneg hCI hE)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hF
  have hsum : RI+RII ≤ (CI+CII)*E*(20*L)^135*F := by linarith [hRII]
  calc
    _ ≤ (D*H*L^4)*((CI+CII)*E*(20*L)^135*F) :=
      mul_le_mul hthin hsum (add_nonneg hRI0 hRII0) (by positivity)
    _ = _ := by ring

open MeasureTheory MAPMRTCorollary25Minkowski

private theorem perronMass_le_two {B : ℝ} (hB : 0 ≤ B) :
    (∫ u in (-B)..B, perronWeight u) ≤ 2*B := by
  have h : (∫ u in (-B)..B, perronWeight u) ≤ ∫ _u in (-B)..B, (1:ℝ) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (continuous_perronWeight.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _)
    intro u hu
    unfold perronWeight
    exact (div_le_one (by positivity)).mpr (by linarith [abs_nonneg u])
  simpa [two_mul] using h

def fullScaleCountConstant (A G C6 : ℝ) : ℝ :=
  (crowdingScaleConstant*(crowdingScaleConstant+1)*(8+12*Real.pi)) *
    (2048*A^2*(3*(2+8*Real.pi)) + (8192*G^4*C6*(4+88*Real.pi)^2+1)) * 20^135

/-- Direct arithmetic weld of the literal two count budgets, actual ceiling
cutoffs, Perron mass, and exact long-spacing/multiplicity thinning factor. -/
theorem fullScale_finite_count_envelope
    {q : ℕ} [NeZero q] {T sigma kappa A G C6 RI RII : ℝ}
    (hT : Real.exp 1 ≤ T) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10)
    (hk : 0 ≤ kappa) (hA : 0 < A) (hG : 0 ≤ G) (hC6 : 0 ≤ C6)
    (hRI0 : 0 ≤ RI) (hRII0 : 0 ≤ RII)
    (hB : (Real.log ((q:ℝ)*T))^2 ≤ T) :
    let S := (q:ℝ)*T
    let B := (Real.log S)^2
    let Y := Real.rpow S (sourceYExponent sigma)
    let U := ⌈10*S⌉₊
    let N := ⌈Y*B⌉₊
    let J : ℝ := detectorDyadicCount N
    let S2 := (q:ℝ)*(T+B)
    RI*((1/8:ℝ)/(4*A*J))^2 ≤
        J^2*(3*(2+8*Real.pi))*Real.rpow (N:ℝ) (2*(1-sigma))*(1+Real.log (2*(N:ℝ)))^4 →
    RII^3*(1/8:ℝ)^4 ≤
      (G*Real.rpow Y (1/2-sigma))^4 * (∫ u in (-B)..B, perronWeight u) *
      (C6*S2*(Real.log S2)^400*Real.exp (Real.sqrt (Real.log (q:ℝ)))) *
      ((2*S2+8*Real.pi*(U:ℝ))*(1+Real.log (U:ℝ)))^2 →
    certifiedA5CrowdingEnvelope q T *
      ((longSpacingColorCount (B+2*(2*Real.pi*Real.rpow T kappa)+1) : ℝ) *
        (certifiedA5CrowdingNatCap q T : ℝ)) * (RI+RII) ≤
      fullScaleCountConstant A G C6 * Real.rpow T kappa *
        Real.rpow S (inghamExponent sigma) * (1+Real.log S)^139 *
        Real.exp (Real.sqrt (Real.log (q:ℝ))) := by
  dsimp only
  intro hI hII
  let S := (q:ℝ)*T
  let B := (Real.log S)^2
  let Y := Real.rpow S (sourceYExponent sigma)
  let U := ⌈10*S⌉₊
  let N := ⌈Y*B⌉₊
  let L0 := 1+Real.log S
  let L := 20*L0
  let S2 := (q:ℝ)*(T+B)
  let F := Real.exp (Real.sqrt (Real.log (q:ℝ)))
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hST : T ≤ S := le_mul_of_one_le_left (by linarith) hq1
  have hSexp : Real.exp 1 ≤ S := hT.trans hST
  have hS1 : 1 ≤ S := hT1.trans hST
  have hS0 : 0 ≤ S := by linarith
  have hlog0 := Real.log_nonneg hS1
  have hL01 : 1 ≤ L0 := by dsimp [L0]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hB0 : 0 ≤ B := sq_nonneg _
  have hF1 : 1 ≤ F := Real.one_le_exp (Real.sqrt_nonneg _)
  obtain ⟨hUn,hNn,hU,hN,hJ,hlogN,hlogU⟩ :=
    fullScale_parameter_log_certificates hSexp hslo hshi
  have hUR : (1:ℝ) ≤ U := by exact_mod_cast hUn
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hNn
  have hJR : (0:ℝ) < (detectorDyadicCount N:ℝ) := by
    unfold detectorDyadicCount
    positivity
  have hlogN0 : 0 ≤ 1+Real.log (2*(N:ℝ)) := by
    have h := Real.log_nonneg (show 1≤2*(N:ℝ) by linarith)
    linarith
  have hlogU0 : 0 ≤ 1+Real.log (U:ℝ) := by linarith [Real.log_nonneg hUR]
  have hS21 : 1 ≤ S2 := by
    have hh := mul_le_mul_of_nonneg_left (show T ≤ T+B by linarith only [hB0])
      (show (0:ℝ) ≤ q by positivity)
    exact hS1.trans (by simpa only [S,S2] using hh)
  have hS2 : S2 ≤ 2*S := by
    have hBT : B ≤ T := hB
    calc
      S2 ≤ (q:ℝ)*(2*T) := mul_le_mul_of_nonneg_left
        (show T+B ≤ 2*T by linarith only [hBT]) (by positivity)
      _ = 2*S := by dsimp [S]; ring
  have hlogS20 : 0 ≤ Real.log S2 := Real.log_nonneg hS21
  have hlogS2 : Real.log S2 ≤ L := by
    have h := Real.log_le_log (by linarith : 0<S2) hS2
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by linarith : S≠0)] at h
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    dsimp [L,L0]
    norm_num at hl2
    linarith
  have hm0 : 0 ≤ ∫ u in (-B)..B, perronWeight u :=
    intervalIntegral.integral_nonneg (by linarith) (fun u hu => (perronWeight_pos u).le)
  have hm : (∫ u in (-B)..B, perronWeight u) ≤ L^2 := by
    apply (perronMass_le_two hB0).trans
    dsimp [L,L0,B]
    nlinarith [sq_nonneg (Real.log S)]
  have hi := typeI_count_normalization hS1 hL1 hslo hshi
    (zero_le_one.trans hNR) hN hJR hJ hA
    (show 0 ≤ 3*(2+8*Real.pi) by positivity) hlogN0 hlogN hI
  have hii := typeII_count_normalization hS1 hL1 hslo hshi
    (zero_le_one.trans hUR) hU hS21 hS2 hm0 hm hG hC6 hlogS20 hlogS2
    hlogU0 hlogU hF1 hRII0 hII
  have hthin := fullScale_thinning_envelope_bound (q:=q) hT1 hk
  have he0 := (crowdingEnvelope_fullScale_bound (q:=q) hT1).1
  have hC0 := crowdingScaleConstant_pos.le
  exact combine_normalized_branches hRI0 hRII0 (by positivity)
    (by positivity) (by positivity) (by positivity)
    (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hS0 _) hL01 hF1 hi hii hthin

/-- The literal envelope has only a fixed logarithmic loss. Its bound is
uniform in the conductor and real part, with explicit Fourier power slack. -/
theorem eventually_fullScale_count_envelope_absorption
    {K eta A G C6 : ℝ} (hK : 0 < K) (heta : 0 < eta)
    (hA : 0 ≤ A) (hG : 0 ≤ G) (hC6 : 0 ≤ C6) :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma kappa : ℝ),
      (q:ℝ) ≤ Real.rpow (Real.log T) K → kappa ≤ eta/2 →
      1/2 ≤ sigma → sigma ≤ 7/10 →
      fullScaleCountConstant A G C6 * Real.rpow T kappa *
        Real.rpow ((q:ℝ)*T) (inghamExponent sigma) *
        (1+Real.log ((q:ℝ)*T))^139 * Real.exp (Real.sqrt (Real.log (q:ℝ))) ≤
      (fullScaleCountConstant A G C6 * (K+2)^139) *
        Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  filter_upwards [eventually_fullScale_log_envelope_absorption hK heta 139] with T hT
  intro q _ sigma kappa hq hk hslo hshi
  have hc : 0 ≤ fullScaleCountConstant A G C6 := by
    have := crowdingScaleConstant_pos.le
    unfold fullScaleCountConstant
    positivity
  have h := mul_le_mul_of_nonneg_left (hT q sigma kappa hq hk hslo hshi) hc
  simpa only [mul_assoc] using h

/-- The literal squared-log central window is eventually below the height,
uniformly over every conductor in the polylogarithmic range. -/
theorem eventually_fullScale_window_le_height {K : ℝ} (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q],
      (q:ℝ) ≤ Real.rpow (Real.log T) K → (Real.log ((q:ℝ)*T))^2 ≤ T := by
  filter_upwards [eventually_ge_atTop (16:ℝ),
    polylog_absorption K 1 (by norm_num), polylog_absorption 2 (1/2) (by norm_num)]
    with T hT hpK hp2
  intro q _ hq
  have hT1 : 1 ≤ T := by linarith
  have hTp : 0 < T := by linarith
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqp : (0:ℝ)<q := by linarith
  have hqT : (q:ℝ) ≤ T := by
    have h := hq.trans hpK
    simpa using h
  have hlogT0 := Real.log_nonneg hT1
  have hlog0 := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 hT1)
  have hlog : Real.log ((q:ℝ)*T) ≤ 2*Real.log T := by
    rw [Real.log_mul hqp.ne' hTp.ne']
    have h := Real.log_le_log hqp hqT
    linarith
  have hp : (Real.log T)^2 ≤ Real.sqrt T := by
    simpa [Real.sqrt_eq_rpow] using hp2
  have hsqrt : 4 ≤ Real.sqrt T := by
    have h := Real.sqrt_le_sqrt hT
    norm_num at h; exact h
  have hsquare := Real.sq_sqrt hTp.le
  calc
    (Real.log ((q:ℝ)*T))^2 ≤ (2*Real.log T)^2 := pow_le_pow_left₀ hlog0 hlog 2
    _ = 4*(Real.log T)^2 := by ring
    _ ≤ 4*Real.sqrt T := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ T := by nlinarith

/-- The Fourier collar is also below T for any exponent at most one half;
the full mollifier then covers the exact hybrid sampling height. -/
theorem fullScale_collar_and_mollifier_cover {q : ℕ} [NeZero q] {T kappa : ℝ}
    (hT : 1 ≤ T) (hTpi : (2*Real.pi)^2 ≤ T) (hk : kappa ≤ 1/2) :
    2*Real.pi*Real.rpow T kappa ≤ T ∧
      (q:ℝ)*(2*(T+2*Real.pi*Real.rpow T kappa)+1) ≤ (⌈10*((q:ℝ)*T)⌉₊ : ℝ) := by
  have hTp : 0<T := by linarith
  have hpow : Real.rpow T kappa ≤ Real.sqrt T := by
    simpa [Real.sqrt_eq_rpow] using Real.rpow_le_rpow_of_exponent_le hT hk
  have hsqrt : 2*Real.pi ≤ Real.sqrt T := by
    have h := Real.sqrt_le_sqrt hTpi
    simpa [Real.sqrt_sq (by positivity : 0≤2*Real.pi)] using h
  have hsq := Real.sq_sqrt hTp.le
  have hc : 2*Real.pi*Real.rpow T kappa ≤ T := by
    have h := mul_le_mul_of_nonneg_left hpow (show 0≤2*Real.pi by positivity)
    nlinarith [Real.sqrt_nonneg T]
  refine ⟨hc,?_⟩
  have hq0 : (0:ℝ) ≤ q := by positivity
  have h := mul_le_mul_of_nonneg_left
    (show 2*(T+2*Real.pi*Real.rpow T kappa)+1 ≤ 10*T by linarith only [hc,hT]) hq0
  exact h.trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using Nat.le_ceil (10*((q:ℝ)*T)))


theorem fullScaleCountConstant_pos {A G C6 : ℝ} (hC6 : 0 ≤ C6) :
    0 < fullScaleCountConstant A G C6 := by
  have hD := crowdingScaleConstant_pos
  unfold fullScaleCountConstant
  positivity

/-- Crude but uniform cutoff control for the Fourier tail: both the actual
ceiling cutoff and its shell count are below T squared. -/
theorem eventually_fullScale_cutoff_le_height_sq {K : ℝ} (hK : 0 < K) :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma : ℝ),
      (q:ℝ) ≤ Real.rpow (Real.log T) K → 1/2 ≤ sigma → sigma ≤ 7/10 →
      let N := ⌈Real.rpow ((q:ℝ)*T) (sourceYExponent sigma)*(Real.log ((q:ℝ)*T))^2⌉₊
      1 ≤ N ∧ (N:ℝ) ≤ T^2 ∧ (detectorDyadicCount N:ℝ) ≤ T^2 := by
  have hlarge : ∀ᶠ T : ℝ in atTop, 18 ≤ Real.rpow T (1/8) := by
    simpa only [Real.rpow_eq_pow] using
      (tendsto_rpow_atTop (show (0:ℝ)<1/8 by norm_num)).eventually (eventually_ge_atTop 18)
  filter_upwards [eventually_ge_atTop (Real.exp 1),
    polylog_absorption K (1/8) (by norm_num),
    polylog_absorption 2 (1/8) (by norm_num), hlarge] with T hT hpK hp2 hlargeT
  intro q _ sigma hq hslo hshi
  dsimp only
  let S := (q:ℝ)*T
  let Y := Real.rpow S (sourceYExponent sigma)
  let N := ⌈Y*(Real.log S)^2⌉₊
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hTp : 0<T := by linarith
  have hq1 : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hqp : (0:ℝ)<q := by linarith
  have hST : T ≤ S := le_mul_of_one_le_left hTp.le hq1
  have hSexp : Real.exp 1 ≤ S := hT.trans hST
  have hS1 : 1 ≤ S := hT1.trans hST
  have hSp : 0<S := by linarith
  have hqpow : (q:ℝ) ≤ Real.rpow T (1/8) := hq.trans hpK
  have hqT : (q:ℝ) ≤ T := hqpow.trans
    (Real.rpow_le_self_of_one_le hT1 (by norm_num))
  have hlogT1 : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hT
    simpa using h
  have hlogS0 := Real.log_nonneg hS1
  have hlogS : Real.log S ≤ 2*Real.log T := by
    dsimp [S]
    rw [Real.log_mul hqp.ne' hTp.ne']
    have h := Real.log_le_log hqp hqT
    linarith
  have hSupper : S ≤ Real.rpow T (9/8) := by
    calc
      S ≤ Real.rpow T (1/8)*T := mul_le_mul_of_nonneg_right hqpow hTp.le
      _ = Real.rpow T (9/8) := by
        have h := Real.rpow_add hTp (1/8) 1
        norm_num at h
        exact h.symm
  have ha : sourceYExponent sigma ≤ 4/3 := by
    unfold sourceYExponent
    apply (div_le_iff₀ (by linarith : 0<2*(2-sigma))).mpr
    linarith
  have hYupper : Y ≤ Real.rpow T (3/2) := by
    calc
      Y ≤ Real.rpow S (4/3) := Real.rpow_le_rpow_of_exponent_le hS1 ha
      _ ≤ Real.rpow (Real.rpow T (9/8)) (4/3) :=
        Real.rpow_le_rpow hSp.le hSupper (by norm_num)
      _ = Real.rpow T (3/2) := by
        have h := (Real.rpow_mul hTp.le (9/8) (4/3)).symm
        norm_num at h
        exact h
  have hlogs : 2*(1+Real.log S)^2 ≤ Real.rpow T (1/4) := by
    have hll : 1+Real.log S ≤ 3*Real.log T := by linarith
    have h2 : (Real.log T)^2 ≤ Real.rpow T (1/8) := by simpa using hp2
    calc
      2*(1+Real.log S)^2 ≤ 2*(3*Real.log T)^2 := by gcongr
      _ = 18*(Real.log T)^2 := by ring
      _ ≤ 18*Real.rpow T (1/8) := mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ ≤ Real.rpow T (1/8)*Real.rpow T (1/8) :=
        mul_le_mul_of_nonneg_right hlargeT (Real.rpow_nonneg hTp.le _)
      _ = Real.rpow T (1/4) := by
        have h := (Real.rpow_add hTp (1/8) (1/8)).symm
        norm_num at h
        exact h
  obtain ⟨hN1,hNupper,hNlog⟩ := full_detector_ceiling_bounds hSexp hslo hshi
  have hNn : 1 ≤ N := by exact_mod_cast hN1
  have hY0 : 0 ≤ Y := Real.rpow_nonneg hSp.le _
  have hNbound : (N:ℝ) ≤ T^2 := by
    calc
      (N:ℝ) ≤ 2*Y*(1+Real.log S)^2 := hNupper
      _ = Y*(2*(1+Real.log S)^2) := by ring
      _ ≤ Real.rpow T (3/2)*Real.rpow T (1/4) :=
        mul_le_mul hYupper hlogs (by positivity) (Real.rpow_nonneg hTp.le _)
      _ = Real.rpow T (7/4) := by
        have h := (Real.rpow_add hTp (3/2) (1/4)).symm
        norm_num at h
        exact h
      _ ≤ T^2 := by
        have h := Real.rpow_le_rpow_of_exponent_le hT1 (show (7/4:ℝ)≤2 by norm_num)
        simpa using h
  have hJN : detectorDyadicCount N ≤ N := by
    unfold detectorDyadicCount
    have h := Nat.log_le_self 2 (N-1)
    rw [← Nat.log2_eq_log_two] at h
    omega
  exact ⟨hNn,hNbound,(by exact_mod_cast hJN : (detectorDyadicCount N:ℝ)≤(N:ℝ)).trans hNbound⟩

/-- Choosing one fixed Fourier derivative order closes the actual numerical
tail budget uniformly in conductor and real part. Ck is any fixed finite
constant at that selected order, so this accepts the certified Fourier
moment constants directly. -/
theorem exists_eventually_fullScale_fourier_tail_budget
    {K kappa : ℝ} (hK : 0 < K) (hk : 0 < kappa) (C : ℕ → ℝ)
    (hC : ∀ k, 0 ≤ C k) :
    ∃ k : ℕ, 6 < kappa*(k:ℝ) ∧
      ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma : ℝ),
        (q:ℝ) ≤ Real.rpow (Real.log T) K → 1/2 ≤ sigma → sigma ≤ 7/10 →
        let N := ⌈Real.rpow ((q:ℝ)*T) (sourceYExponent sigma)*(Real.log ((q:ℝ)*T))^2⌉₊
        2*(N:ℝ)^2*Real.rpow (Real.rpow T kappa) (-(k:ℝ))*C k ≤
          (1/8:ℝ)/(2*(detectorDyadicCount N:ℝ)) := by
  obtain ⟨k,hklarge⟩ := exists_nat_gt (6/kappa)
  have hkk : 6 < kappa*(k:ℝ) := by
    have h := (div_lt_iff₀ hk).mp hklarge
    simpa only [mul_comm] using h
  refine ⟨k,hkk,?_⟩
  have hp : 0 < kappa*(k:ℝ)-6 := by linarith
  have hlarge : ∀ᶠ T : ℝ in atTop, 32*C k ≤ Real.rpow T (kappa*(k:ℝ)-6) := by
    simpa only [Real.rpow_eq_pow] using
      (tendsto_rpow_atTop hp).eventually (eventually_ge_atTop (32*C k))
  filter_upwards [eventually_ge_atTop (1:ℝ),
    eventually_fullScale_cutoff_le_height_sq hK,hlarge] with T hT hNall hlargeT
  intro q _ sigma hq hslo hshi
  dsimp only
  let N := ⌈Real.rpow ((q:ℝ)*T) (sourceYExponent sigma)*(Real.log ((q:ℝ)*T))^2⌉₊
  let J : ℝ := detectorDyadicCount N
  obtain ⟨hN1,hN,hJ⟩ := hNall q sigma hq hslo hshi
  have hJp : 0 < J := by dsimp [J,detectorDyadicCount]; positivity
  have hTp : 0<T := by linarith
  have hweight : 0 ≤ Real.rpow (Real.rpow T kappa) (-(k:ℝ)) :=
    Real.rpow_nonneg (Real.rpow_nonneg hTp.le _) _
  have hcancel : T^6 * Real.rpow (Real.rpow T kappa) (-(k:ℝ)) *
      Real.rpow T (kappa*(k:ℝ)-6) = 1 := by
    calc
      _ = Real.rpow T 6 * Real.rpow T (kappa*(-(k:ℝ))) *
          Real.rpow T (kappa*(k:ℝ)-6) := by
        apply congrArg (fun z => z * Real.rpow T (kappa*(k:ℝ)-6))
        exact congrArg₂ (· * ·) (Real.rpow_natCast T 6).symm
          (Real.rpow_mul hTp.le kappa (-(k:ℝ))).symm
      _ = Real.rpow T ((6+kappa*(-(k:ℝ)))+(kappa*(k:ℝ)-6)) := by
        simp only [Real.rpow_eq_pow]
        rw [← Real.rpow_add hTp, ← Real.rpow_add hTp]
      _ = 1 := by ring_nf; exact Real.rpow_zero T
  have hsmall : 32*C k*T^6*Real.rpow (Real.rpow T kappa) (-(k:ℝ)) ≤ 1 := by
    calc
      _ = (T^6*Real.rpow (Real.rpow T kappa) (-(k:ℝ)))*(32*C k) := by ring
      _ ≤ (T^6*Real.rpow (Real.rpow T kappa) (-(k:ℝ)))*
          Real.rpow T (kappa*(k:ℝ)-6) :=
        mul_le_mul_of_nonneg_left hlargeT (mul_nonneg (pow_nonneg hTp.le _) hweight)
      _ = 1 := hcancel
  have hNJ : (N:ℝ)^2*J ≤ T^6 := by
    calc
      _ ≤ (T^2)^2*T^2 := mul_le_mul (pow_le_pow_left₀ (by positivity) hN 2)
        hJ (by dsimp [J]; positivity) (by positivity)
      _ = T^6 := by ring
  have hproduct : (2*(N:ℝ)^2*Real.rpow (Real.rpow T kappa) (-(k:ℝ))*C k)*(2*J) ≤ 1/8 := by
    have h := mul_le_mul_of_nonneg_left hNJ
      (show 0 ≤ 32*C k*Real.rpow (Real.rpow T kappa) (-(k:ℝ)) from
        mul_nonneg (mul_nonneg (by norm_num) (hC k)) hweight)
    nlinarith only [h,hsmall]
  exact (le_div_iff₀ (by positivity : 0<2*J)).mpr hproduct


/-- Exact Fourier-tail interface consumed by the finite source count. -/
theorem exists_eventually_fullScale_fourier_tail {K kappa : ℝ}
    (hK : 0 < K) (hk : 0 < kappa) :
    ∃ k : ℕ, ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ) [NeZero q] (sigma : ℝ),
      (q:ℝ) ≤ Real.rpow (Real.log T) K → 1/2 ≤ sigma → sigma ≤ 7/10 →
      let S := (q:ℝ)*T
      let Y := Real.rpow S (sourceYExponent sigma)
      let N := ⌈Y*(Real.log S)^2⌉₊
      let J : ℝ := detectorDyadicCount N
      2*(N:ℝ)^2*((Real.rpow T kappa)^k)⁻¹*
        MAPMontgomeryFullStripFourier.detectorFourierMomentConstant k ≤ ((1/8:ℝ)/J)/2 := by
  obtain ⟨k,hk6,hkT⟩ := exists_eventually_fullScale_fourier_tail_budget hK hk
    MAPMontgomeryFullStripFourier.detectorFourierMomentConstant
    MAPMontgomeryFullStripFourier.detectorFourierMomentConstant_nonneg
  refine ⟨k,?_⟩
  filter_upwards [hkT, eventually_ge_atTop (1:ℝ)] with T hT hTone
  intro q _ sigma hq hslo hshi
  have h := hT q sigma hq hslo hshi
  dsimp only at h ⊢
  have hp : Real.rpow (Real.rpow T kappa) (-(k:ℝ)) = ((Real.rpow T kappa)^k)⁻¹ := by
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_neg (Real.rpow_nonneg (by linarith : 0≤T) _), Real.rpow_natCast]
  rw [hp] at h
  convert h using 1 <;> ring

open MAPMontgomeryPrincipalFullScaleThinning
local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

/-- The principal thinning factor is bounded by an absolute multiple of
the already certified conductor-one crowding factor. -/
theorem principalThinningFactor_le_fullScale_thinning {T B : ℝ}
    (hT : Real.exp 1 ≤ T) :
    (principalThinningFactor T B : ℝ) ≤
      3368*(certifiedA5CrowdingEnvelope 1 T *
        ((longSpacingColorCount B : ℝ)*(certifiedA5CrowdingNatCap 1 T : ℝ))) := by
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hlog1 : 1 ≤ Real.log (T+3) := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ T+3 by linarith)
    simpa using h
  have hden : 0 < Real.log (17/16) := Real.log_pos (by norm_num)
  have hden1 : Real.log (17/16) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<17/16)
    linarith
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h3200 : 0 ≤ Real.log 3200 := Real.log_nonneg (by norm_num)
  have hlogPhi : Real.log (T+3) ≤ certifiedA5CrowdingEnvelope 1 T := by
    unfold certifiedA5CrowdingEnvelope
    norm_num
    apply (le_div_iff₀ hden).mpr
    nlinarith
  have hPhi1 : 1 ≤ certifiedA5CrowdingEnvelope 1 T := hlog1.trans hlogPhi
  have hPhi0 : 0 ≤ certifiedA5CrowdingEnvelope 1 T := zero_le_one.trans hPhi1
  have hcap1 : (1:ℝ) ≤ certifiedA5CrowdingNatCap 1 T := by
    unfold certifiedA5CrowdingNatCap
    rw [max_eq_right hPhi0]
    exact hPhi1.trans (Nat.le_ceil _)
  have hc : (⌈1683*Real.log (T+3)⌉₊ : ℝ) ≤ 1684*certifiedA5CrowdingEnvelope 1 T := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ 1683*Real.log (T+3) by linarith)
    linarith
  unfold principalThinningFactor
  push_cast
  calc
    _ ≤ 2*(1684*certifiedA5CrowdingEnvelope 1 T)*(longSpacingColorCount B:ℝ) := by gcongr
    _ = 3368*(certifiedA5CrowdingEnvelope 1 T*(longSpacingColorCount B:ℝ)) := by ring
    _ ≤ 3368*((certifiedA5CrowdingEnvelope 1 T*(longSpacingColorCount B:ℝ))*
        (certifiedA5CrowdingNatCap 1 T:ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact le_mul_of_one_le_right (by positivity) hcap1
    _ = _ := by ring

def principalScaleCountConstant (A G C6 : ℝ) : ℝ :=
  3368*(fullScaleCountConstant A G C6 +
    crowdingScaleConstant*(crowdingScaleConstant+1)*(8+12*Real.pi))

theorem principalScaleCountConstant_pos {A G C6 : ℝ} (hC6 : 0 ≤ C6) :
    0 < principalScaleCountConstant A G C6 := by
  have h := fullScaleCountConstant_pos (A:=A) (G:=G) hC6
  have hD := crowdingScaleConstant_pos
  unfold principalScaleCountConstant
  positivity

/-- Exact principal budget adapter. The additive one from deleting the
principal low-height representative is paid by the same positive scale. -/
theorem fullScale_finite_principal_count_envelope
    {T sigma kappa A G C6 RI RII : ℝ}
    (hT : Real.exp 1 ≤ T) (hslo : 1/2 ≤ sigma) (hshi : sigma ≤ 7/10)
    (hk : 0 ≤ kappa) (hA : 0 < A) (hG : 0 ≤ G) (hC6 : 0 ≤ C6)
    (hRI0 : 0 ≤ RI) (hRII0 : 0 ≤ RII) (hB : (Real.log T)^2 ≤ T) :
    let B := (Real.log T)^2
    let Y := Real.rpow T (sourceYExponent sigma)
    let U := ⌈10*T⌉₊
    let N := ⌈Y*B⌉₊
    let J : ℝ := detectorDyadicCount N
    RI*((1/8:ℝ)/(4*A*J))^2 ≤
        J^2*(3*(2+8*Real.pi))*Real.rpow (N:ℝ) (2*(1-sigma))*(1+Real.log (2*(N:ℝ)))^4 →
    RII^3*(1/8:ℝ)^4 ≤
      (G*Real.rpow Y (1/2-sigma))^4 * (∫ u in (-B)..B, perronWeight u) *
      (C6*(T+B)*(Real.log (T+B))^400) *
      ((2*(T+B)+8*Real.pi*(U:ℝ))*(1+Real.log (U:ℝ)))^2 →
    (principalThinningFactor T (B+2*(2*Real.pi*Real.rpow T kappa)+1) : ℝ) * (RI+RII+1) ≤
      principalScaleCountConstant A G C6 * Real.rpow T kappa *
        Real.rpow T (inghamExponent sigma) * (1+Real.log T)^139 := by
  dsimp only
  intro hI hII
  let Bthin := (Real.log T)^2+2*(2*Real.pi*Real.rpow T kappa)+1
  let thin := certifiedA5CrowdingEnvelope 1 T *
    ((longSpacingColorCount Bthin : ℝ)*(certifiedA5CrowdingNatCap 1 T : ℝ))
  let H := Real.rpow T kappa
  let E := Real.rpow T (inghamExponent sigma)
  let L := 1+Real.log T
  let D := crowdingScaleConstant*(crowdingScaleConstant+1)*(8+12*Real.pi)
  have hT1 : 1 ≤ T := (Real.one_le_exp (by norm_num)).trans hT
  have hE1 : 1 ≤ E := Real.one_le_rpow hT1 (inghamExponent_nonneg hslo hshi)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg hT1]
  have hH0 : 0 ≤ H := Real.rpow_nonneg (by linarith) _
  have hD0 : 0 ≤ D := by have := crowdingScaleConstant_pos.le; dsimp [D]; positivity
  have hraw := fullScale_finite_count_envelope (q:=1) hT hslo hshi hk hA hG hC6
    hRI0 hRII0 (by simpa using hB)
  simp only [Nat.cast_one,one_mul,Real.log_one,Real.sqrt_zero,Real.exp_zero,mul_one] at hraw
  have hnp : thin*(RI+RII) ≤ fullScaleCountConstant A G C6*H*E*L^139 := hraw hI hII
  have hthin : thin ≤ D*H*L^4 := by
    simpa only [Nat.cast_one,one_mul] using fullScale_thinning_envelope_bound (q:=1) hT1 hk
  have hthinFull : thin ≤ D*H*E*L^139 := by
    calc
      thin ≤ D*H*L^4 := hthin
      _ ≤ D*H*L^139 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hL1 (by norm_num)) (mul_nonneg hD0 hH0)
      _ ≤ D*H*E*L^139 := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith) _)
        exact le_mul_of_one_le_right (mul_nonneg hD0 hH0) hE1
  have hprincipal := principalThinningFactor_le_fullScale_thinning (B:=Bthin) hT
  have h := mul_le_mul_of_nonneg_right hprincipal (show 0 ≤ RI+RII+1 by linarith)
  change (principalThinningFactor T Bthin:ℝ)*(RI+RII+1) ≤ _
  calc
    _ ≤ 3368*thin*(RI+RII+1) := h
    _ = 3368*(thin*(RI+RII)+thin) := by ring
    _ ≤ 3368*(fullScaleCountConstant A G C6*H*E*L^139+D*H*E*L^139) :=
      mul_le_mul_of_nonneg_left (add_le_add hnp hthinFull) (by norm_num)
    _ = _ := by dsimp [principalScaleCountConstant,D,H,E,L]; ring

/-- Uniform principal scale absorption, including the additive low-height
representative. No conductor parameter is needed at conductor one. -/
theorem eventually_fullScale_principal_count_envelope_absorption
    {eta A G C6 : ℝ} (heta : 0 < eta) (hC6 : 0 ≤ C6) :
    ∀ᶠ T : ℝ in atTop, ∀ (sigma kappa : ℝ),
      kappa ≤ eta/2 → 1/2 ≤ sigma → sigma ≤ 7/10 →
      principalScaleCountConstant A G C6 * Real.rpow T kappa *
        Real.rpow T (inghamExponent sigma) * (1+Real.log T)^139 ≤
      (principalScaleCountConstant A G C6 * 3^139) *
        Real.rpow T (uniformCoeff*(1-sigma)+eta) := by
  filter_upwards [eventually_fullScale_log_envelope_absorption (K:=1) (by norm_num) heta 139,
    eventually_ge_atTop (Real.exp 1)] with T hT hlarge
  intro sigma kappa hk hslo hshi
  have hlog1 : 1 ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos 1) hlarge
    simpa using h
  have h := hT 1 sigma kappa (by simpa using hlog1) hk hslo hshi
  simp only [Nat.cast_one,one_mul,Real.log_one,Real.sqrt_zero,Real.exp_zero,mul_one] at h
  have hc := (principalScaleCountConstant_pos (A:=A) (G:=G) hC6).le
  have hh := mul_le_mul_of_nonneg_left h hc
  rw [show (1:ℝ)+2=3 by norm_num] at hh
  simpa only [mul_assoc] using hh

end
end MAPMontgomeryFullScaleDensityAbsorption

#print axioms MAPMontgomeryFullScaleDensityAbsorption.fullScale_finite_count_envelope
#print axioms MAPMontgomeryFullScaleDensityAbsorption.eventually_fullScale_count_envelope_absorption

#print axioms MAPMontgomeryFullScaleDensityAbsorption.exists_eventually_fullScale_fourier_tail

#print axioms MAPMontgomeryFullScaleDensityAbsorption.fullScale_finite_principal_count_envelope
#print axioms MAPMontgomeryFullScaleDensityAbsorption.eventually_fullScale_principal_count_envelope_absorption
