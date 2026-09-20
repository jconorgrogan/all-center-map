import GoldfeldEulerCorrection
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Varying-level Goldfeld comparison

The common product level contributes one finite Euler correction.  The
elementary harmonic bound therefore gives a fourth fixed logarithm; the
conductor exponent remains proportional to the exceptional zero gap.
-/

namespace MAPGoldfeldSiegel

open Complex

noncomputable section

/-- The source comparison with one additional fixed logarithm from the
common-level realization. -/
def GoldfeldComparisonEstimateFourLog : Prop :=
  ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
    ∀ (exceptional a : PrimitiveRealCharacter),
      exceptional.level ≤ a.level → a ≠ exceptional →
      ∀ betaExceptional : ℝ,
        1 / 2 < betaExceptional → betaExceptional < 1 →
        exceptional.LFunction betaExceptional = 0 →
          C * Real.rpow (a.level : ℝ)
                (-A * (1 - betaExceptional)) /
              (Real.log (2 * (a.level : ℝ))) ^ 4 ≤
            ‖a.LFunction 1‖

theorem productLevel_le_sq
    (exceptional a : PrimitiveRealCharacter)
    (hlevel : exceptional.level ≤ a.level) :
    productLevel exceptional a ≤ a.level ^ 2 := by
  unfold productLevel
  simpa [pow_two] using Nat.mul_le_mul_right a.level hlevel

theorem one_add_log_productLevel_le_four_log
    (exceptional a : PrimitiveRealCharacter)
    (hlevel : exceptional.level ≤ a.level) :
    1 + Real.log (productLevel exceptional a) ≤
      4 * Real.log (2 * (a.level : ℝ)) := by
  have hePos : (0 : ℝ) < exceptional.level := by
    exact_mod_cast Nat.pos_of_ne_zero exceptional.level_ne_zero
  have haPos : (0 : ℝ) < a.level := by
    exact_mod_cast Nat.pos_of_ne_zero a.level_ne_zero
  have hprodPos : (0 : ℝ) < productLevel exceptional a := by
    exact_mod_cast Nat.mul_pos
      (Nat.pos_of_ne_zero exceptional.level_ne_zero)
      (Nat.pos_of_ne_zero a.level_ne_zero)
  have hasqPos : (0 : ℝ) < (a.level : ℝ) ^ 2 := sq_pos_of_pos haPos
  have hprodLe : (productLevel exceptional a : ℝ) ≤ (a.level : ℝ) ^ 2 := by
    exact_mod_cast productLevel_le_sq exceptional a hlevel
  have hlogProd : Real.log (productLevel exceptional a) ≤
      2 * Real.log (a.level : ℝ) := by
    calc
      Real.log (productLevel exceptional a) ≤ Real.log ((a.level : ℝ) ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hprodPos hasqPos hprodLe
      _ = 2 * Real.log (a.level : ℝ) := by
        rw [Real.log_pow]
        norm_num
  have htwoaPos : (0 : ℝ) < 2 * (a.level : ℝ) := by positivity
  have hlogLevel : Real.log (a.level : ℝ) ≤
      Real.log (2 * (a.level : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn haPos htwoaPos
    nlinarith
  have hlogTwo : Real.log 2 ≤ Real.log (2 * (a.level : ℝ)) := by
    apply Real.strictMonoOn_log.monotoneOn (by norm_num) htwoaPos
    have haOne : (1 : ℝ) ≤ a.level := by
      exact_mod_cast (NeZero.one_le : 1 ≤ a.level)
    nlinarith
  have hone : (1 : ℝ) ≤ 2 * Real.log (2 * (a.level : ℝ)) := by
    nlinarith [Real.log_two_gt_d9]
  linarith

/-- The product-level conductor power coarsens to exponent `26` at the larger
primitive level. -/
theorem level_sq_rpow_le_productLevel_rpow
    (exceptional a : PrimitiveRealCharacter)
    (hlevel : exceptional.level ≤ a.level)
    {beta : ℝ} (hbetaHigh : beta < 1) :
    Real.rpow (a.level : ℝ) (-26 * (1 - beta)) ≤
      Real.rpow (productLevel exceptional a : ℝ) (-13 * (1 - beta)) := by
  have hprodPos : (0 : ℝ) < productLevel exceptional a := by
    exact_mod_cast Nat.mul_pos
      (Nat.pos_of_ne_zero exceptional.level_ne_zero)
      (Nat.pos_of_ne_zero a.level_ne_zero)
  have hprodLe : (productLevel exceptional a : ℝ) ≤ (a.level : ℝ) ^ 2 := by
    exact_mod_cast productLevel_le_sq exceptional a hlevel
  have hexp : -13 * (1 - beta) ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hprodPos hprodLe hexp
  calc
    Real.rpow (a.level : ℝ) (-26 * (1 - beta)) =
        Real.rpow (a.level : ℝ) (2 * (-13 * (1 - beta))) := by
      congr 1
      ring
    _ = Real.rpow (Real.rpow (a.level : ℝ) 2)
        (-13 * (1 - beta)) :=
      Real.rpow_mul (Nat.cast_nonneg a.level) 2 (-13 * (1 - beta))
    _ = Real.rpow ((a.level : ℝ) ^ 2) (-13 * (1 - beta)) := by
      congr 1
      exact Real.rpow_natCast (a.level : ℝ) 2
    _ ≤ Real.rpow (productLevel exceptional a : ℝ)
        (-13 * (1 - beta)) := hpow

/-- The completed contour, Lemma 11.2, product-level adapter, and harmonic
Euler correction prove the varying-level comparison. -/
theorem goldfeldComparisonEstimateFourLog : GoldfeldComparisonEstimateFourLog := by
  let C0 : ℝ := (24000 * (2 * goldfeldBoundaryCoefficient) ^ 2)⁻¹
  let C : ℝ := C0 / (4 : ℝ) ^ 4
  have hC0 : 0 < C0 := by
    dsimp [C0]
    positivity [goldfeldBoundaryCoefficient_pos]
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨26, C, by norm_num, hC, ?_⟩
  intro exceptional a hlevel hne beta hbetaHalf hbetaHigh hzero
  let N := productLevel exceptional a
  let chi := leftLift exceptional a
  let psi := rightLift exceptional a
  have hN : 2 ≤ N := by
    dsimp [N, productLevel]
    have heTwo := exceptional.two_le_level
    have haPos := Nat.pos_of_ne_zero a.level_ne_zero
    nlinarith
  have hchi := leftLift_ne_one exceptional a
  have hpsi := rightLift_ne_one exceptional a
  have hmul := leftLift_mul_rightLift_ne_one exceptional a (Ne.symm hne)
  have hchiReal := leftLift_sq exceptional a
  have hpsiReal := rightLift_sq exceptional a
  have hzeroLift := leftLift_LFunction_eq_zero exceptional a hzero
  have hsame := sameLevel_goldfeld_Lvalue_lower_nonprimitive hN chi psi
    hchi hpsi hmul hchiReal hpsiReal hzeroLift hbetaHalf
      hbetaHigh
  have heuler := norm_rightLift_LFunction_one_le exceptional a
  have hchain := hsame.trans heuler
  change C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
      (1 + Real.log N) ^ 3 ≤
        (1 + Real.log (productLevel exceptional a)) * ‖a.LFunction 1‖ at hchain
  have hLN : 0 < 1 + Real.log (N : ℝ) := by
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ N by omega))
    linarith
  have hambient :
      C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
          (1 + Real.log N) ^ 4 ≤ ‖a.LFunction 1‖ := by
    have hdiv :
        (C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
          (1 + Real.log N) ^ 3) / (1 + Real.log N) ≤
            ‖a.LFunction 1‖ := by
      apply (div_le_iff₀ hLN).2
      simpa [N, psi, mul_comm, mul_left_comm, mul_assoc] using hchain
    convert hdiv using 1 <;> field_simp <;> ring
  have hpow := level_sq_rpow_le_productLevel_rpow exceptional a hlevel hbetaHigh
  have hlog := one_add_log_productLevel_le_four_log exceptional a hlevel
  have hlogTarget : 0 < Real.log (2 * (a.level : ℝ)) := by
    apply Real.log_pos
    have haOne : (1 : ℝ) ≤ a.level := by
      exact_mod_cast (NeZero.one_le : 1 ≤ a.level)
    nlinarith
  have hdenN : 0 < (1 + Real.log (N : ℝ)) ^ 4 := pow_pos hLN 4
  have hdenTarget : 0 < (Real.log (2 * (a.level : ℝ))) ^ 4 :=
    pow_pos hlogTarget 4
  have hlogPow : (1 + Real.log (N : ℝ)) ^ 4 ≤
      (4 : ℝ) ^ 4 * (Real.log (2 * (a.level : ℝ))) ^ 4 := by
    have hp := pow_le_pow_left₀ hLN.le (by simpa [N] using hlog) 4
    simpa [mul_pow] using hp
  have hpow0 : 0 ≤ Real.rpow (a.level : ℝ) (-26 * (1 - beta)) :=
    Real.rpow_nonneg (Nat.cast_nonneg a.level) _
  have hnum : C0 / (4 : ℝ) ^ 4 *
        Real.rpow (a.level : ℝ) (-26 * (1 - beta)) ≤
      C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
        (4 : ℝ) ^ 4 := by
    rw [show C0 / (4 : ℝ) ^ 4 *
        Real.rpow (a.level : ℝ) (-26 * (1 - beta)) =
      (C0 * Real.rpow (a.level : ℝ) (-26 * (1 - beta))) /
        (4 : ℝ) ^ 4 by ring]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < (4 : ℝ) ^ 4)).2
    exact mul_le_mul_of_nonneg_left hpow hC0.le
  have hcoarse :
      (C0 / (4 : ℝ) ^ 4 *
          Real.rpow (a.level : ℝ) (-26 * (1 - beta))) /
          (Real.log (2 * (a.level : ℝ))) ^ 4 ≤
        C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
          (1 + Real.log N) ^ 4 := by
    apply (div_le_div_iff₀ hdenTarget hdenN).2
    have hC0N : 0 ≤ C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) := by
      exact mul_nonneg hC0.le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    calc
      (C0 / (4 : ℝ) ^ 4 *
          Real.rpow (a.level : ℝ) (-26 * (1 - beta))) *
          (1 + Real.log N) ^ 4 ≤
        (C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
          (4 : ℝ) ^ 4) * (1 + Real.log N) ^ 4 :=
        mul_le_mul_of_nonneg_right hnum (pow_nonneg hLN.le 4)
      _ ≤ (C0 * Real.rpow (N : ℝ) (-13 * (1 - beta))) *
          (Real.log (2 * (a.level : ℝ))) ^ 4 := by
        calc
          _ ≤ (C0 * Real.rpow (N : ℝ) (-13 * (1 - beta)) /
              (4 : ℝ) ^ 4) *
              ((4 : ℝ) ^ 4 *
                (Real.log (2 * (a.level : ℝ))) ^ 4) :=
            mul_le_mul_of_nonneg_left hlogPow (by positivity)
          _ = _ := by field_simp
  exact hcoarse.trans hambient

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.one_add_log_productLevel_le_four_log
#print axioms MAPGoldfeldSiegel.level_sq_rpow_le_productLevel_rpow
#print axioms MAPGoldfeldSiegel.goldfeldComparisonEstimateFourLog
