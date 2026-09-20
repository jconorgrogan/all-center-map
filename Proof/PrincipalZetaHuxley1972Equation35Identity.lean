import PrincipalZetaContourTails

/-!
# Huxley 1972, equation (3.5): exact principal contour identity

This module identifies the repository's premise-free principal Gamma detector
with Huxley's notation.  The arithmetic coefficient is exactly

`b_U(n) = sum_{d|n, d≤U} mu(d)`,

and the contour shift crosses precisely Huxley's residue at `z=1-rho`.
Thus (3.5), including its principal-pole correction, is no longer an analytic
leaf of the terminal classifier.
-/

namespace MAPPrincipalZetaHuxley1972Equation35Identity

open scoped ArithmeticFunction LSeries.notation BigOperators
open MAPMollifierCoefficientIdentity MAPAppendixA4GammaEndpoint
open MAPPrincipalZetaDetectorPoleRemoval MAPPrincipalZetaPoleContour
open MAPPrincipalZetaContourTails

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩
local notation "chiOne" => (1 : DirichletCharacter ℂ 1)
local notation "principalF" => MAPPrincipalZetaFixedStrip.principalRegularized

/-- Huxley's coefficient `b(m)` in (3.3)--(3.4). -/
def huxleyCoefficient (U n : ℕ) : ℂ := mollifierCoeff U n

/-- The exact divisor formula printed in Huxley (3.4). -/
theorem huxleyCoefficient_apply (U n : ℕ) :
    huxleyCoefficient U n =
      ∑ p ∈ n.divisorsAntidiagonal, truncatedMoebius U p.2 := by
  exact mollifierCoeff_apply U n

/-- The `n`th arithmetic term on the right of (3.5). -/
def huxleyArithmeticTerm
    (U : ℕ) (rho : ℂ) (Y : ℝ) (n : ℕ) : ℂ :=
  LSeries.term (huxleyCoefficient U) rho n *
    (Real.exp (-((n : ℝ) / Y)) : ℂ)

private theorem principalCharacter_apply (n : ℕ) : chiOne n = 1 := by
  apply MulChar.one_apply
  rw [show (n : ZMod 1) = 1 from Subsingleton.elim _ _]
  exact isUnit_one

private theorem one_sub_exp_neg_inv_le_exp_mul
    {Y : ℝ} (hY : 1 ≤ Y) :
    (1 - Real.exp (-(1 / Y)))⁻¹ ≤ Real.exp 1 * Y := by
  have hYpos : 0 < Y := zero_lt_one.trans_le hY
  let x : ℝ := 1 / Y
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxle : x ≤ 1 := by
    dsimp [x]
    exact (div_le_one hYpos).2 hY
  have hexpLower : Real.exp (-1) ≤ Real.exp (-x) :=
    Real.exp_le_exp.mpr (by linarith)
  have hbasic : x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp x)
      (Real.exp_pos (-x)).le
    rw [mul_add, ← Real.exp_add] at h
    have hcancel : Real.exp (-x + x) = 1 := by simp
    rw [hcancel] at h
    nlinarith
  have hdenpos : 0 < 1 - Real.exp (-x) := by
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  change (1 - Real.exp (-x))⁻¹ ≤ Real.exp 1 * Y
  rw [inv_le_iff_one_le_mul₀ hdenpos]
  calc
    1 = (Real.exp 1 * Y) * (x * Real.exp (-1)) := by
      dsimp [x]
      field_simp
      rw [← Real.exp_add]
      norm_num
    _ ≤ (Real.exp 1 * Y) * (x * Real.exp (-x)) := by
      gcongr
    _ ≤ (Real.exp 1 * Y) * (1 - Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hbasic (by positivity)

/-- For the conductor-one character, the Appendix-A.4 detector term is
literally Huxley's `b(m)m^{-rho}exp(-m/Y)` term. -/
theorem arithmeticDetectorTerm_eq_huxleyArithmeticTerm
    (U : ℕ) (rho : ℂ) (Y : ℝ) (n : ℕ) :
    arithmeticDetectorTerm chiOne U rho Y n =
      huxleyArithmeticTerm U rho Y n := by
  unfold arithmeticDetectorTerm huxleyArithmeticTerm huxleyCoefficient
    detectorCoeff
  have hcoeff :
      ((fun n : ℕ => chiOne n) * mollifierCoeff U) = mollifierCoeff U := by
    funext m
    simp only [Pi.mul_apply]
    rw [principalCharacter_apply]
    exact one_mul _
  rw [hcoeff]

/-- Source-facing form of Huxley (3.5) after moving the contour to
`Re z = 1/2-beta`.  The right side is the literal smoothed `b(m)` tail; the
left side is the crossed zeta-pole residue plus the critical-line integral.
All convergence and horizontal-boundary limits are already discharged by
`literal_principal_A4_full_identity`. -/
theorem huxleyEquation35_full_identity
    {U : ℕ} (hU : 1 ≤ U) {rho : ℂ}
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    {Y : ℝ} (hY : 1 ≤ Y) :
    (Real.exp (-(1 / Y)) : ℂ) +
        ∑' n : {n // n ∉ Finset.range (U + 1)},
          huxleyArithmeticTerm U rho Y n =
      principalDetectorResidue rho U Y +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, principalRawDetector rho U Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I)) := by
  have hsource := literal_principal_A4_full_identity
    hU hrho (by linarith) hbetaHigh hY
  calc
    (Real.exp (-(1 / Y)) : ℂ) +
          ∑' n : {n // n ∉ Finset.range (U + 1)},
            huxleyArithmeticTerm U rho Y n =
        (Real.exp (-(1 / Y)) : ℂ) +
          ∑' n : {n // n ∉ Finset.range (U + 1)},
            arithmeticDetectorTerm chiOne U rho Y n := by
      congr 1
      apply tsum_congr
      intro n
      exact (arithmeticDetectorTerm_eq_huxleyArithmeticTerm
        U rho Y n).symm
    _ = principalDetectorResidue rho U Y +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          ∫ t : ℝ, principalRawDetector rho U Y
            (((1 / 2 - rho.re : ℝ) : ℂ) + t * Complex.I)) := hsource

/-- Huxley's residue estimate (3.8), with the source scale assumptions made
explicit.  The high-ordinate cutoff `100 log T`, `U+1≤2Y`, and `Y≤T²`
overwhelm the crossed-pole residue by a fixed `1/10` already for `T≥480`.
This is a direct specialization of the certified residue formula, not an
asymptotic premise. -/
theorem huxleyEquation38_residue_le_oneTenth
    {T Y : ℝ} {U : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hYone : 1 ≤ Y)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 100 * Real.log T ≤ |rho.im|) :
    ‖principalDetectorResidue rho U Y‖ ≤ 1 / 10 := by
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := hTpos.le
  have hE : Real.exp 1 ≤ T := by
    exact (show Real.exp 1 ≤ 3 by
      exact Real.exp_one_lt_d9.le.trans (by norm_num)) |>.trans
      (by linarith)
  have hlogOne : 1 ≤ Real.log T := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log T := Real.log_le_log (Real.exp_pos 1) hE
  have himOne : 1 ≤ |rho.im| := by linarith
  have hrhoOne : rho ≠ 1 := by
    intro h
    subst rho
    simpa using hrho
  have hYpos : 0 < Y := zero_lt_one.trans_le hYone
  have hres := norm_principalDetectorResidue_le (U := U) hrho hrhoOne
    (by linarith) hbetaHigh himOne hYpos
  have hratio : (1 + |rho.im|) * (1 / |rho.im|) ≤ 2 := by
    have himpos : 0 < |rho.im| := zero_lt_one.trans_le himOne
    simpa [div_eq_mul_inv] using
      ((div_le_iff₀ himpos).2 (show 1 + |rho.im| ≤ 2 * |rho.im| by
        linarith))
  have hexp : Real.exp (-|rho.im|) ≤ Real.rpow T (-100 : ℝ) := by
    calc
      Real.exp (-|rho.im|) ≤ Real.exp (-100 * Real.log T) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.rpow T (-100 : ℝ) := by
        change Real.exp (-100 * Real.log T) = T ^ (-100 : ℝ)
        rw [Real.rpow_def_of_pos hTpos]
        congr 1
        ring
  have hYpow : Real.rpow Y (1 - rho.re) ≤ Real.rpow T 1 := by
    have hbeta : 1 - rho.re ≤ (1 / 2 : ℝ) := by linarith
    have hfirst : Real.rpow Y (1 - rho.re) ≤ Real.rpow Y (1 / 2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hYone hbeta
    have hTpow : T ^ 2 = Real.rpow T (2 : ℝ) := by
      exact (Real.rpow_natCast T 2).symm
    have hsecond : Real.rpow Y (1 / 2 : ℝ) ≤
        Real.rpow (T ^ 2) (1 / 2 : ℝ) :=
      Real.rpow_le_rpow hYpos.le hYT (by norm_num)
    have heval : Real.rpow (T ^ 2) (1 / 2 : ℝ) = Real.rpow T 1 := by
      rw [hTpow]
      calc
        Real.rpow (Real.rpow T (2 : ℝ)) (1 / 2 : ℝ) =
            Real.rpow T ((2 : ℝ) * (1 / 2 : ℝ)) :=
          (Real.rpow_mul hT0 _ _).symm
        _ = Real.rpow T 1 := by norm_num
    exact hfirst.trans (hsecond.trans_eq heval)
  have hUscale : (U + 1 : ℝ) ≤ 2 * Real.rpow T (2 : ℝ) := by
    calc
      (U + 1 : ℝ) ≤ 2 * Y := hUY
      _ ≤ 2 * T ^ 2 := mul_le_mul_of_nonneg_left hYT (by norm_num)
      _ = 2 * Real.rpow T (2 : ℝ) := by
        exact congrArg (fun x : ℝ => 2 * x) (Real.rpow_natCast T 2).symm
  have hraw : ‖principalDetectorResidue rho U Y‖ ≤
      48 * Real.rpow T (-97 : ℝ) := by
    calc
      ‖principalDetectorResidue rho U Y‖ ≤
          12 * (1 + |rho.im|) * Real.exp (-|rho.im|) *
            (1 / |rho.im|) * Real.rpow Y (1 - rho.re) * (U + 1) := hres
      _ = 12 * ((1 + |rho.im|) * (1 / |rho.im|)) *
          Real.exp (-|rho.im|) * Real.rpow Y (1 - rho.re) * (U + 1) := by ring
      _ ≤ 12 * 2 * Real.exp (-|rho.im|) *
          Real.rpow Y (1 - rho.re) * (U + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hratio (by norm_num))
              (Real.exp_nonneg _))
            (Real.rpow_nonneg hYpos.le _))
          (by positivity)
      _ ≤ 12 * 2 * Real.rpow T (-100 : ℝ) *
          Real.rpow Y (1 - rho.re) * (U + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hexp (by norm_num))
            (Real.rpow_nonneg hYpos.le _))
          (by positivity)
      _ ≤ 12 * 2 * Real.rpow T (-100 : ℝ) *
          Real.rpow T 1 * (U + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hYpow
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _)))
          (by positivity)
      _ ≤ 12 * 2 * Real.rpow T (-100 : ℝ) *
          Real.rpow T 1 * (2 * Real.rpow T (2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hUscale
          (mul_nonneg
            (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0 _))
            (Real.rpow_nonneg hT0 _))
      _ = 48 * Real.rpow T (-97 : ℝ) := by
        have hmerge : Real.rpow T (-100 : ℝ) * Real.rpow T 1 *
            Real.rpow T (2 : ℝ) = Real.rpow T (-97 : ℝ) := by
          change T ^ (-100 : ℝ) * T ^ (1 : ℝ) * T ^ (2 : ℝ) =
            T ^ (-97 : ℝ)
          rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          norm_num
        rw [show 12 * 2 * Real.rpow T (-100 : ℝ) *
            Real.rpow T 1 * (2 * Real.rpow T (2 : ℝ)) =
            48 * (Real.rpow T (-100 : ℝ) * Real.rpow T 1 *
              Real.rpow T (2 : ℝ)) by ring,
          hmerge]
  have hpow : Real.rpow T (-97 : ℝ) ≤ Real.rpow T (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hTone (by norm_num)
  have hinv : Real.rpow T (-1 : ℝ) = T⁻¹ := by
    simpa using Real.rpow_neg_one T
  calc
    ‖principalDetectorResidue rho U Y‖ ≤
        48 * Real.rpow T (-97 : ℝ) := hraw
    _ ≤ 48 * Real.rpow T (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ = 48 / T := by rw [hinv, div_eq_mul_inv]
    _ ≤ 1 / 10 := by
      exact (div_le_iff₀ hTpos).2 (by nlinarith)

/-- Literal equation-(3.7) wrapper for the preceding residue estimate.
The logarithmic source assumptions `log U ≤ log Y ≤ 2 log T` imply exactly
the two scale inequalities used above. -/
theorem huxleyEquation38_residue_le_oneTenth_of_equation37
    {T Y : ℝ} {U : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hU : 1 ≤ U) (hYpos : 0 < Y)
    (hlogUY : Real.log U ≤ Real.log Y)
    (hlogYT : Real.log Y ≤ 2 * Real.log T)
    (hrho : principalF rho = 0)
    (hbetaLow : 7 / 10 ≤ rho.re) (hbetaHigh : rho.re ≤ 1)
    (hgamma : 100 * Real.log T ≤ |rho.im|) :
    ‖principalDetectorResidue rho U Y‖ ≤ 1 / 10 := by
  have hTpos : 0 < T := by linarith
  have hURpos : (0 : ℝ) < U := by exact_mod_cast (zero_lt_one.trans_le hU)
  have hUY : (U : ℝ) ≤ Y := by
    have h := Real.exp_le_exp.mpr hlogUY
    rw [Real.exp_log hURpos, Real.exp_log hYpos] at h
    exact h
  have hUreal : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hYone : 1 ≤ Y := hUreal.trans hUY
  have hUYtwo : (U + 1 : ℝ) ≤ 2 * Y := by
    linarith
  have hYT : Y ≤ T ^ 2 := by
    have h := Real.exp_le_exp.mpr hlogYT
    rw [Real.exp_log hYpos] at h
    calc
      Y ≤ Real.exp (2 * Real.log T) := h
      _ = T ^ 2 := by
        rw [show 2 * Real.log T = Real.log T + Real.log T by ring,
          Real.exp_add, Real.exp_log hTpos]
        ring
  exact huxleyEquation38_residue_le_oneTenth hT hYone hUYtwo hYT
    hrho hbetaLow hbetaHigh hgamma

/-- Huxley's far arithmetic tail (3.10).  Here `N` is any integer cutoff
with `N+1 ≥ 100 Y log T`; taking `N=floor(100 Y log T)` gives the printed
range.  The proof uses the exact detector coefficient bound and sums the
resulting geometric series. -/
theorem huxleyEquation310_farTail_le_oneTenth
    {T Y : ℝ} {U N : ℕ} {rho : ℂ}
    (hT : 480 ≤ T) (hYone : 1 ≤ Y)
    (hUY : (U + 1 : ℝ) ≤ 2 * Y) (hYT : Y ≤ T ^ 2)
    (hbeta : 0 ≤ rho.re)
    (hcut : 100 * Y * Real.log T ≤ (N + 1 : ℕ)) :
    ‖∑' k : ℕ, huxleyArithmeticTerm U rho Y (k + (N + 1))‖ ≤
      1 / 10 := by
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hT0 : 0 ≤ T := hTpos.le
  have hYpos : 0 < Y := zero_lt_one.trans_le hYone
  have htail := MAPAppendixA4DetectorDichotomy.norm_arithmetic_shifted_tail_le
    chiOne U N hbeta hYpos
  have hsumEq :
      (∑' k : ℕ, huxleyArithmeticTerm U rho Y (k + (N + 1))) =
        ∑' k : ℕ, arithmeticDetectorTerm chiOne U rho Y (k + (N + 1)) := by
    apply tsum_congr
    intro k
    exact (arithmeticDetectorTerm_eq_huxleyArithmeticTerm
      U rho Y (k + (N + 1))).symm
  have hcutDiv : 100 * Real.log T ≤ (N + 1 : ℕ) / Y := by
    rw [le_div_iff₀ hYpos]
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcut
  have hpow : (Real.exp (-(1 / Y))) ^ (N + 1) ≤
      Real.rpow T (-100 : ℝ) := by
    rw [← MAPAppendixA4DetectorDichotomy.exp_neg_nat_div_eq_pow
      (Y := Y) (N + 1)]
    calc
      Real.exp (-((N + 1 : ℕ) / Y)) ≤
          Real.exp (-100 * Real.log T) := by
        exact Real.exp_le_exp.mpr (by linarith)
      _ = Real.rpow T (-100 : ℝ) := by
        change Real.exp (-100 * Real.log T) = T ^ (-100 : ℝ)
        rw [Real.rpow_def_of_pos hTpos]
        congr 1
        ring
  have hinv := one_sub_exp_neg_inv_le_exp_mul hYone
  have hinv0 : 0 ≤ (1 - Real.exp (-(1 / Y)))⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (by have := one_div_pos.mpr hYpos; linarith))
  have hpow0 : 0 ≤ (Real.exp (-(1 / Y))) ^ (N + 1) := by positivity
  have hYsq : Y ^ 2 ≤ T ^ 4 := by
    have hT2nonneg : 0 ≤ T ^ 2 := sq_nonneg T
    calc
      Y ^ 2 ≤ (T ^ 2) ^ 2 := by gcongr
      _ = T ^ 4 := by ring
  have hT4 : T ^ 4 = Real.rpow T (4 : ℝ) :=
    (Real.rpow_natCast T 4).symm
  have hmerge : Real.rpow T (4 : ℝ) * Real.rpow T (-100 : ℝ) =
      Real.rpow T (-96 : ℝ) := by
    change T ^ (4 : ℝ) * T ^ (-100 : ℝ) = T ^ (-96 : ℝ)
    rw [← Real.rpow_add hTpos]
    norm_num
  calc
    ‖∑' k : ℕ, huxleyArithmeticTerm U rho Y (k + (N + 1))‖ =
        ‖∑' k : ℕ,
          arithmeticDetectorTerm chiOne U rho Y (k + (N + 1))‖ := by
      rw [hsumEq]
    _ ≤ (U + 1) * (Real.exp (-(1 / Y))) ^ (N + 1) *
          (1 - Real.exp (-(1 / Y)))⁻¹ := htail
    _ ≤ (2 * Y) * Real.rpow T (-100 : ℝ) * (Real.exp 1 * Y) := by
      exact mul_le_mul
        (mul_le_mul hUY hpow hpow0 (by positivity)) hinv
        hinv0
        (mul_nonneg (by positivity) (Real.rpow_nonneg hT0 _))
    _ = 2 * Real.exp 1 * (Y ^ 2 * Real.rpow T (-100 : ℝ)) := by ring
    _ ≤ 2 * 3 * (Real.rpow T (4 : ℝ) *
          Real.rpow T (-100 : ℝ)) := by
      have hE : Real.exp 1 ≤ 3 :=
        Real.exp_one_lt_d9.le.trans (by norm_num)
      rw [← hT4]
      gcongr
      · exact mul_nonneg (sq_nonneg Y) (Real.rpow_nonneg hT0 _)
      · exact Real.rpow_nonneg hT0 _
    _ = 6 * Real.rpow T (-96 : ℝ) := by rw [hmerge]; ring
    _ ≤ 6 * Real.rpow T (-1 : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hTone (by norm_num)) (by norm_num)
    _ = 6 / T := by
      have hinvT : Real.rpow T (-1 : ℝ) = T⁻¹ := by
        simpa using Real.rpow_neg_one T
      rw [hinvT, div_eq_mul_inv]
    _ ≤ 1 / 10 := by
      exact (div_le_iff₀ hTpos).2 (by nlinarith)

end
end MAPPrincipalZetaHuxley1972Equation35Identity

#print axioms MAPPrincipalZetaHuxley1972Equation35Identity.huxleyCoefficient_apply
#print axioms MAPPrincipalZetaHuxley1972Equation35Identity.huxleyEquation35_full_identity
#print axioms MAPPrincipalZetaHuxley1972Equation35Identity.huxleyEquation38_residue_le_oneTenth
#print axioms MAPPrincipalZetaHuxley1972Equation35Identity.huxleyEquation38_residue_le_oneTenth_of_equation37
#print axioms MAPPrincipalZetaHuxley1972Equation35Identity.huxleyEquation310_farTail_le_oneTenth
