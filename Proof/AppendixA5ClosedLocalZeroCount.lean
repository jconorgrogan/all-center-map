import AppendixA45GrowthConnector

/-!
# Premise-free logarithmic local zero count for Appendix (A.5)

This file spends the certified Phragmén--Lindelöf bound on the literal Jensen
circle from `LocalZeroWindowJensen`.  The resulting theorem counts the zeros in
the manuscript's closed interval `[t,t+1]`, with analytic multiplicity, and has
an explicit absolute constant.
-/

open Complex Real Set Metric
open scoped Real

namespace MAPAppendixA5ClosedLocalZeroCount

noncomputable section

variable {q : ℕ} [NeZero q]

private theorem four_le_arithmeticScale
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    (4 : ℝ) ≤ MAPLocalZeroWindow.arithmeticScale q t := by
  have hqne : q ≠ 1 := fun hq => hχ (DirichletCharacter.level_one' χ hq)
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2nat : 2 ≤ q := by omega
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq2nat
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  unfold MAPLocalZeroWindow.arithmeticScale
  nlinarith

private theorem logarithmic_numerator_le
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (t : ℝ) :
    Real.log 3 + Real.log 3200 +
          2 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) ≤
      9 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) := by
  let S : ℝ := MAPLocalZeroWindow.arithmeticScale q t
  have hS4 : 4 ≤ S := four_le_arithmeticScale χ hχ t
  have hSpos : 0 < S := by linarith
  have hpow : (9600 : ℝ) ≤ S ^ (7 : ℕ) := by
    calc
      (9600 : ℝ) ≤ 4 ^ (7 : ℕ) := by norm_num
      _ ≤ S ^ (7 : ℕ) := by
        exact pow_le_pow_left₀ (by norm_num) hS4 7
  have hlogpow : Real.log (9600 : ℝ) ≤ 7 * Real.log S := by
    calc
      Real.log (9600 : ℝ) ≤ Real.log (S ^ (7 : ℕ)) :=
        Real.log_le_log (by norm_num) hpow
      _ = 7 * Real.log S := by rw [Real.log_pow]; norm_num
  have hcombine : Real.log 3 + Real.log 3200 = Real.log 9600 := by
    rw [← Real.log_mul (by norm_num : (3 : ℝ) ≠ 0)
      (by norm_num : (3200 : ℝ) ≠ 0)]
    norm_num
  dsimp [S] at hS4 hSpos hpow hlogpow ⊢
  rw [hcombine]
  linarith

private theorem one_div_seventeen_le_jensenDenominator :
    (1 / 17 : ℝ) ≤
      Real.log (MAPLocalZeroWindow.jensenOuterRadius /
        MAPLocalZeroWindow.jensenInnerRadius) := by
  have h := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < MAPLocalZeroWindow.jensenOuterRadius /
      MAPLocalZeroWindow.jensenInnerRadius by
        norm_num [MAPLocalZeroWindow.jensenOuterRadius,
          MAPLocalZeroWindow.jensenInnerRadius])
  norm_num [MAPLocalZeroWindow.jensenOuterRadius,
    MAPLocalZeroWindow.jensenInnerRadius] at h ⊢
  exact h

/-- The closed unit-window count from Appendix (A.5), including analytic
multiplicity, is bounded by an explicit constant times the expected
level-height logarithm.  The proof needs only nonprincipality. -/
theorem certifiedAppendixA5ClosedLocalZeroCount_nonprincipal
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ t : ℝ} (hσ : 1 / 2 ≤ σ) :
    (MAPLocalZeroWindow.closedUnitWindowCount χ σ t : ℝ) ≤
      153 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) := by
  have hbase :=
    MAPAppendixA45GrowthConnector.certifiedAppendixA5LocalZeroCount
      χ hχ (t := t) hσ
  have hnum := logarithmic_numerator_le χ hχ t
  have hS4 := four_le_arithmeticScale χ hχ t
  have hlogS : 0 ≤ Real.log (MAPLocalZeroWindow.arithmeticScale q t) :=
    Real.log_nonneg (by linarith)
  have hden := one_div_seventeen_le_jensenDenominator
  have hquot :
      (Real.log 3 + Real.log 3200 +
          2 * Real.log (MAPLocalZeroWindow.arithmeticScale q t)) /
        Real.log (MAPLocalZeroWindow.jensenOuterRadius /
          MAPLocalZeroWindow.jensenInnerRadius) ≤
      153 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) := by
    apply (div_le_iff₀ MAPLocalZeroWindow.jensenDenominator_pos).2
    have hmul :
        9 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) ≤
          153 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) *
            Real.log (MAPLocalZeroWindow.jensenOuterRadius /
              MAPLocalZeroWindow.jensenInnerRadius) := by
      nlinarith
    exact hnum.trans hmul
  exact hbase.trans hquot

/-- The exact primitive/nonprincipal form consumed by the detector argument.
For a primitive character, its level `q` is its conductor, so the logarithm is
literally `log(q (|t|+2))` with `q` equal to the manuscript's `r`. -/
theorem certifiedAppendixA5ClosedLocalZeroCount
    (χ : DirichletCharacter ℂ q) (_hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    {σ t : ℝ} (hσ : 1 / 2 ≤ σ) :
    (MAPLocalZeroWindow.closedUnitWindowCount χ σ t : ℝ) ≤
      153 * Real.log (MAPLocalZeroWindow.arithmeticScale q t) :=
  certifiedAppendixA5ClosedLocalZeroCount_nonprincipal χ hχ hσ

end

end MAPAppendixA5ClosedLocalZeroCount

#print axioms MAPAppendixA5ClosedLocalZeroCount.certifiedAppendixA5ClosedLocalZeroCount_nonprincipal
#print axioms MAPAppendixA5ClosedLocalZeroCount.certifiedAppendixA5ClosedLocalZeroCount
