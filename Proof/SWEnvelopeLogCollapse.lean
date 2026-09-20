import SiegelWalfiszToPointwise
import SupportBoundaryQuantitative
import PrimePolynomialEnergyFromPointwise

/-!
# Collapse of the explicit Siegel--Walfisz envelope

This file contains only deterministic real-asymptotic bookkeeping.  Its sole
analytic hypothesis is the public `UniformSiegelWalfiszPsi` contract.  The
explicit prefix and Abel envelopes already proved in
`SiegelWalfiszToPointwise` are collapsed to an arbitrary logarithmic saving.
-/

namespace SWEnvelopeLogCollapse

open MAPPointwiseMajorArc MAPSiegelWalfiszToPointwise MAPMajorArcWeld

noncomputable section

/-- The Abel multiplier on a paper arc is at most `10 log(X)^D` once
`log X >= 1`. -/
theorem abelMultiplier_le
    {X : ℝ} {D : ℕ} (hX : 0 < X) (hlog : 1 ≤ Real.log X) :
    2 + X * (2 * Real.pi * paperArcRadius X D) ≤
      10 * (Real.log X) ^ D := by
  have hpow : 1 ≤ (Real.log X) ^ D := one_le_pow₀ hlog
  have hpi : 2 * Real.pi ≤ (8 : ℝ) := by
    nlinarith [Real.pi_lt_four.le]
  have hpiPow : 2 * Real.pi * (Real.log X) ^ D ≤
      8 * (Real.log X) ^ D :=
    mul_le_mul_of_nonneg_right hpi (pow_nonneg (by linarith) D)
  have hident : X * (2 * Real.pi * paperArcRadius X D) =
      2 * Real.pi * (Real.log X) ^ D := by
    unfold paperArcRadius
    field_simp
  rw [hident]
  nlinarith [hpiPow]

/-- A convenient positive square-root comparison used to absorb the
prime-power correction in the prefix envelope. -/
theorem sqrt_two_mul_le_two_sqrt
    (X : ℝ) :
    Real.sqrt (2 * X) ≤ 2 * Real.sqrt X := by
  have h2 : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg X)

/-- The explicit envelope has an arbitrary logarithmic saving after choosing
the Siegel--Walfisz exponent `A = B + D + K` and waiting past two elementary
polylogarithmic thresholds. -/
theorem eventually_primePolynomialEnvelope_le
    (C : ℝ) (hC : 0 < C) (K B D : ℕ) :
    ∀ᶠ X : ℝ in Filter.atTop,
      primePolynomialEnvelope X C (B + D + K) B D ≤
        (10 * C + 90) * X / (Real.log X) ^ K := by
  have hpolyWhole := SupportBoundaryQuantitative.polylog_absorption
    ((B + D + K : ℕ) : ℝ) 1 (by norm_num)
  have hpolyHalf := SupportBoundaryQuantitative.polylog_absorption
    ((D + 1 + K : ℕ) : ℝ) (1 / 2 : ℝ) (by norm_num)
  filter_upwards [hpolyWhole, hpolyHalf,
      Filter.eventually_ge_atTop (Real.exp 1),
      Filter.eventually_ge_atTop (2 : ℝ)] with X hwhole hhalf hXexp hX2
  have hXpos : 0 < X := by linarith [Real.exp_pos 1]
  have hlog1 : 1 ≤ Real.log X :=
    (Real.le_log_iff_exp_le hXpos).2 hXexp
  have hlogpos : 0 < Real.log X := zero_lt_one.trans_le hlog1
  have hlog0 : 0 ≤ Real.log X := hlogpos.le
  have hlog2X : Real.log (2 * X) ≤ 2 * Real.log X :=
    MAPVarianceTransferWeld.log_two_mul_le_two_log hX2
  have hlog2X0 : 0 ≤ Real.log (2 * X) :=
    Real.log_nonneg (by linarith)
  have hsqrt : Real.sqrt (2 * X) ≤ 2 * Real.sqrt X :=
    sqrt_two_mul_le_two_sqrt X
  have hmult : 2 + X * (2 * Real.pi * paperArcRadius X D) ≤
      10 * (Real.log X) ^ D := abelMultiplier_le hXpos hlog1
  have hwhole' : (Real.log X) ^ (B + D + K) ≤ X := by
    calc
      (Real.log X) ^ (B + D + K) =
          Real.rpow (Real.log X) ((B + D + K : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ Real.rpow X 1 := hwhole
      _ = X := Real.rpow_one X
  have hhalf' : (Real.log X) ^ (D + 1 + K) ≤ Real.sqrt X := by
    calc
      (Real.log X) ^ (D + 1 + K) =
          Real.rpow (Real.log X) ((D + 1 + K : ℕ) : ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ ≤ Real.rpow X (1 / 2 : ℝ) := hhalf
      _ = Real.sqrt X := (Real.sqrt_eq_rpow X).symm
  have hsqrt0 : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hmain :
      10 * (Real.log X) ^ D *
          ((Real.log X) ^ B *
            (C * X / (Real.log X) ^ (B + D + K))) ≤
        10 * C * X / (Real.log X) ^ K := by
    have hlogne : Real.log X ≠ 0 := hlogpos.ne'
    field_simp [hlogne]
    rw [pow_add, pow_add]
    show (Real.log X) ^ D * (Real.log X) ^ B * (Real.log X) ^ K ≤
      (Real.log X) ^ B * (Real.log X) ^ D * (Real.log X) ^ K
    exact le_of_eq (by ring)
  have hone :
      10 * (Real.log X) ^ D * (Real.log X) ^ B ≤
        10 * X / (Real.log X) ^ K := by
    apply (le_div_iff₀ (pow_pos hlogpos K)).2
    calc
      10 * (Real.log X) ^ D * (Real.log X) ^ B * (Real.log X) ^ K =
          10 * (Real.log X) ^ (B + D + K) := by ring
      _ ≤ 10 * X := by gcongr
  have hsqrtTerm :
      10 * (Real.log X) ^ D *
          (2 * Real.sqrt (2 * X) * Real.log (2 * X)) ≤
        80 * X / (Real.log X) ^ K := by
    have hpre :
        10 * (Real.log X) ^ D *
            (2 * Real.sqrt (2 * X) * Real.log (2 * X)) ≤
          80 * Real.sqrt X * (Real.log X) ^ (D + 1) := by
      calc
        10 * (Real.log X) ^ D *
            (2 * Real.sqrt (2 * X) * Real.log (2 * X)) ≤
          10 * (Real.log X) ^ D *
            (2 * (2 * Real.sqrt X) * (2 * Real.log X)) := by
              gcongr
        _ = 80 * Real.sqrt X * (Real.log X) ^ (D + 1) := by
          rw [pow_succ]
          ring
    refine hpre.trans ?_
    apply (le_div_iff₀ (pow_pos hlogpos K)).2
    have hmul := mul_le_mul_of_nonneg_left hhalf'
      (by positivity : 0 ≤ 80 * Real.sqrt X)
    calc
      80 * Real.sqrt X * (Real.log X) ^ (D + 1) * (Real.log X) ^ K =
          80 * Real.sqrt X * (Real.log X) ^ (D + 1 + K) := by ring
      _ ≤ 80 * Real.sqrt X * Real.sqrt X := hmul
      _ = 80 * X := by nlinarith [Real.sq_sqrt hXpos.le]
  unfold primePolynomialEnvelope rationalPrefixEnvelope
  have hrational0 :
      0 ≤ (Real.log X) ^ B *
            (C * X / (Real.log X) ^ (B + D + K) + 1) +
          2 * Real.sqrt (2 * X) * Real.log (2 * X) := by
    positivity
  calc
    (2 + X * (2 * Real.pi * paperArcRadius X D)) *
        ((Real.log X) ^ B *
            (C * X / (Real.log X) ^ (B + D + K) + 1) +
          2 * Real.sqrt (2 * X) * Real.log (2 * X)) ≤
      10 * (Real.log X) ^ D *
        ((Real.log X) ^ B *
            (C * X / (Real.log X) ^ (B + D + K) + 1) +
          2 * Real.sqrt (2 * X) * Real.log (2 * X)) := by
            exact mul_le_mul_of_nonneg_right hmult hrational0
    _ =
      10 * (Real.log X) ^ D *
          ((Real.log X) ^ B *
            (C * X / (Real.log X) ^ (B + D + K))) +
      10 * (Real.log X) ^ D * (Real.log X) ^ B +
      10 * (Real.log X) ^ D *
          (2 * Real.sqrt (2 * X) * Real.log (2 * X)) := by ring
    _ ≤ 10 * C * X / (Real.log X) ^ K +
        10 * X / (Real.log X) ^ K +
        80 * X / (Real.log X) ^ K := by
      gcongr
    _ = (10 * C + 90) * X / (Real.log X) ^ K := by ring

/-- The requested deterministic bridge.  No analytic proposition beyond
`UniformSiegelWalfiszPsi` is used. -/
theorem uniformPrimePolynomialLogSaving_of_siegelWalfisz
    (hSW : MAPPointwiseMajorArc.UniformSiegelWalfiszPsi) :
    MAPPrimePolynomialEnergyFromPointwise.UniformPrimePolynomialLogSaving := by
  intro K B D
  obtain ⟨Csw, Xsw, hCsw, hXsw, hpoint⟩ :=
    MAPSiegelWalfiszToPointwise.UniformSiegelWalfiszPsi.exists_uniform_primePolynomial
      hSW (B + D + K) B D
  have henv := eventually_primePolynomialEnvelope_le Csw hCsw K B D
  rw [Filter.eventually_atTop] at henv
  obtain ⟨Xe, hXe⟩ := henv
  let C : ℝ := 10 * Csw + 90
  let X₀ : ℝ := max Xsw (max Xe 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hX₀ : 2 ≤ X₀ :=
    (le_max_right Xe 2).trans (le_max_right Xsw (max Xe 2))
  refine ⟨C, X₀, hC, hX₀, ?_⟩
  intro X hXX₀ q a β hq hqL ha hcop hβ
  have hXXsw : Xsw ≤ X :=
    (le_max_left Xsw (max Xe 2)).trans hXX₀
  have hXXe : Xe ≤ X :=
    (le_max_left Xe 2).trans
      ((le_max_right Xsw (max Xe 2)).trans hXX₀)
  exact (hpoint X hXXsw q a β hq hqL ha hcop hβ).trans (hXe X hXXe)

end

end SWEnvelopeLogCollapse

#print axioms SWEnvelopeLogCollapse.uniformPrimePolynomialLogSaving_of_siegelWalfisz
