import McCurleyRegularLowHeightBridge
import PrimitiveSiegelContourAdapter

/-!
# McCurley's bounded-ordinate region in the primitive contour predicate

This file contains the deterministic conversion from McCurley's literal
exception-shape theorem to the low-height zero-gap predicate used by
`PrimitiveSiegelContourAdapter`.

The source region has denominator

`9.645908801 * log (max {q, q |t|, 10})`.

As elsewhere in the McCurley bridge, a closed consumer uses the rigorously
larger `9.64590881`.  For `|t| < 3`, the elementary inequality
`max {q, q |t|, 10} <= 10 q` and `log x <= x^epsilon / epsilon`
turn the logarithmic region into a uniform `q^(-epsilon)` collar.  No
analytic zero-free assertion is introduced here.
-/

namespace MAPMcCurleyPrimitiveLowPredicate

open Set
open DirichletZeros PrimitiveTruncatedExplicitFormulaBridge
open MAPMcCurleyHighImaginaryBridge MAPMcCurleyRegularLowHeightBridge

noncomputable section

/-- Explicit constant converting McCurley's logarithmic collar to a
power-saving collar at bounded ordinate. -/
def regularLowConstant (epsilon : ℝ) : ℝ :=
  epsilon / (safeClosedR * Real.rpow 10 epsilon)

theorem regularLowConstant_pos {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < regularLowConstant epsilon := by
  unfold regularLowConstant
  exact div_pos hepsilon (mul_pos (by norm_num [safeClosedR])
    (Real.rpow_pos_of_pos (by norm_num) _))

/-- At `|t| < 3`, McCurley's exact scale is at most `10 q`. -/
theorem mccurleyScale_le_ten_mul_level_of_abs_lt_three
    {q : ℕ} [NeZero q] {t : ℝ} (ht : |t| < 3) :
    mccurleyScale q t ≤ 10 * (q : ℝ) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  unfold mccurleyScale
  apply max_le
  · apply max_le
    · nlinarith
    · have habs : |t| ≤ 10 := by linarith
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left habs (Nat.cast_nonneg q))
  · nlinarith

/-- Source denominator at bounded ordinate is controlled by an arbitrary
positive conductor power. -/
theorem safeDenominator_le_level_rpow
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {q : ℕ} [NeZero q] {t : ℝ} (ht : |t| < 3) :
    safeDenominator q t ≤
      (safeClosedR * Real.rpow 10 epsilon / epsilon) *
        Real.rpow (q : ℝ) epsilon := by
  have hscale := mccurleyScale_le_ten_mul_level_of_abs_lt_three
    (q := q) (t := t) ht
  have hscalePos : 0 < mccurleyScale q t :=
    zero_lt_one.trans (one_lt_mccurleyScale q t)
  have hlog : Real.log (mccurleyScale q t) ≤
      Real.log (10 * (q : ℝ)) :=
    Real.log_le_log hscalePos hscale
  have hpow := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ 10 * (q : ℝ) by positivity) hepsilon
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hten0 : (0 : ℝ) ≤ 10 := by norm_num
  have hrpowMul : Real.rpow (10 * (q : ℝ)) epsilon =
      Real.rpow 10 epsilon * Real.rpow (q : ℝ) epsilon := by
    exact Real.mul_rpow hten0 hq0
  unfold safeDenominator
  calc
    safeClosedR * Real.log (mccurleyScale q t) ≤
        safeClosedR * Real.log (10 * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (by norm_num [safeClosedR])
    _ ≤ safeClosedR *
        (Real.rpow (10 * (q : ℝ)) epsilon / epsilon) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num [safeClosedR])
    _ = (safeClosedR * Real.rpow 10 epsilon / epsilon) *
        Real.rpow (q : ℝ) epsilon := by
      rw [hrpowMul]
      ring

/-- The power collar with `regularLowConstant` lies inside McCurley's closed
bounded-height collar. -/
theorem regularLowConstant_mul_rpow_neg_le_one_div_safeDenominator
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {q : ℕ} [NeZero q] {t : ℝ} (ht : |t| < 3) :
    regularLowConstant epsilon * Real.rpow (q : ℝ) (-epsilon) ≤
      1 / safeDenominator q t := by
  have hden := safeDenominator_le_level_rpow
    (q := q) (t := t) hepsilon ht
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (NeZero.ne q).bot_lt
  have htenpow : 0 < Real.rpow 10 epsilon :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hqpow : 0 < Real.rpow (q : ℝ) epsilon :=
    Real.rpow_pos_of_pos hqpos _
  have hR : 0 < safeClosedR := by norm_num [safeClosedR]
  have hC : 0 < safeClosedR * Real.rpow 10 epsilon / epsilon :=
    div_pos (mul_pos hR htenpow) hepsilon
  have hupperPos : 0 <
      (safeClosedR * Real.rpow 10 epsilon / epsilon) *
        Real.rpow (q : ℝ) epsilon := mul_pos hC hqpow
  have hinv := one_div_le_one_div_of_le (safeDenominator_pos q t) hden
  have hneg : Real.rpow (q : ℝ) (-epsilon) =
      (Real.rpow (q : ℝ) epsilon)⁻¹ := by
    exact Real.rpow_neg hqpos.le epsilon
  calc
    regularLowConstant epsilon * Real.rpow (q : ℝ) (-epsilon) =
        1 / ((safeClosedR * Real.rpow 10 epsilon / epsilon) *
          Real.rpow (q : ℝ) epsilon) := by
      rw [regularLowConstant, hneg]
      field_simp [hepsilon.ne', hR.ne', htenpow.ne', hqpow.ne']
    _ ≤ 1 / safeDenominator q t := hinv

/-- A supported zero of the regularized L-function is a zero of the ordinary
L-function.  In the principal case the nonzero patched value at `1` removes
the only possible spurious factor. -/
theorem LFunction_eq_zero_of_mem_zeroSupport
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {sigma T : ℝ} {rho : ℂ} (hrho : rho ∈ zeroSupport chi sigma T) :
    DirichletCharacter.LFunction chi rho = 0 := by
  have hreg : regularizedLFunction chi rho = 0 :=
    regularizedLFunction_eq_zero_of_mem_zeroSupport chi sigma T hrho
  by_cases hchi : chi = 1
  · have hrhoOne : rho ≠ 1 := by
      intro h
      subst rho
      exact MAPAPZeroDensityCert.regularizedLFunction_one_ne_zero chi hreg
    have hprod : (rho - 1) * DirichletCharacter.LFunction chi rho = 0 := by
      simpa [regularizedLFunction, hchi,
        DirichletCharacter.LFunctionTrivChar₁,
        Function.update_of_ne hrhoOne] using hreg
    exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hrhoOne)
  · simpa [regularizedLFunction, hchi] using hreg

/-- Exact low-height predicate consumed by `PrimitiveSiegelContourAdapter`,
conditional only on the literal McCurley exception-shape statement. -/
theorem regular_low_zeroSupport_gap_of_mccurley_shape
    {epsilon omega : ℝ} (hepsilon : 0 < epsilon)
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hPublishedExceptionShape :
      ∀ (psi : DirichletCharacter ℂ q) (s : ℂ),
        mccurleyBoundary publishedR q s.im < s.re →
        DirichletCharacter.LFunction psi s = 0 →
        s.im = 0 ∧ psi ≠ 1 ∧ psi ^ 2 = 1)
    {sigma T : ℝ}
    (homega : omega ≤ regularLowConstant epsilon *
      Real.rpow (q : ℝ) (-epsilon)) :
    ∀ rho ∈ zeroSupport chi sigma T,
      (chi = 1 ∨ chi ^ 2 ≠ 1 ∨ rho.im ≠ 0) → |rho.im| < 3 →
        rho.re ≤ 1 - omega := by
  intro rho hrho hregular hheight
  have hnotExceptional : ¬ (chi ≠ 1 ∧ chi ^ 2 = 1 ∧ rho.im = 0) := by
    intro hbad
    rcases hregular with hprincipal | hnquad | hnonreal
    · exact hbad.1 hprincipal
    · exact hnquad hbad.2.1
    · exact hnonreal hbad.2.2
  have hLzero : DirichletCharacter.LFunction chi
      ((rho.re : ℂ) + (rho.im : ℂ) * Complex.I) = 0 := by
    simpa [Complex.re_add_im] using
      (LFunction_eq_zero_of_mem_zeroSupport chi hrho)
  have hsource :=
    one_div_safeDenominator_le_one_sub_sigma_of_regular_zero
      chi hPublishedExceptionShape hnotExceptional hLzero
  have hpower :=
    regularLowConstant_mul_rpow_neg_le_one_div_safeDenominator
      (q := q) (t := rho.im) hepsilon hheight
  linarith

end

end MAPMcCurleyPrimitiveLowPredicate

#print axioms MAPMcCurleyPrimitiveLowPredicate.regularLowConstant_pos
#print axioms MAPMcCurleyPrimitiveLowPredicate.mccurleyScale_le_ten_mul_level_of_abs_lt_three
#print axioms MAPMcCurleyPrimitiveLowPredicate.safeDenominator_le_level_rpow
#print axioms MAPMcCurleyPrimitiveLowPredicate.regularLowConstant_mul_rpow_neg_le_one_div_safeDenominator
#print axioms MAPMcCurleyPrimitiveLowPredicate.LFunction_eq_zero_of_mem_zeroSupport
#print axioms MAPMcCurleyPrimitiveLowPredicate.regular_low_zeroSupport_gap_of_mccurley_shape
