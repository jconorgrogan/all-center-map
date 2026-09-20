import GoldfeldLemma11TwoNormalized
import GoldfeldFullContour
import GoldfeldComparisonArithmetic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Quantitative residue lower bound from the full Goldfeld contour

This is the deterministic inequality layer between the order-14 contour
identity and the arithmetic comparison.
-/

namespace MAPGoldfeldSiegel

open Set MeasureTheory Complex ComplexOrder
open scoped ArithmeticFunction LSeries.notation BigOperators

noncomputable section

/-- The explicit shifted-line majorant integrates to the boundary constant
times `pi`. -/
theorem norm_goldfeldRaw_left_integral_le
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X) :
    ‖∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      goldfeldBoundaryConstant N X * Real.pi := by
  let f : ℝ → ℂ := fun t => goldfeldRawIntegrand chi psi beta 14 X
    (((-1 / 2 : ℝ) : ℂ) + t * I)
  let g : ℝ → ℝ := fun t =>
    goldfeldBoundaryConstant N X * (1 + t ^ 2)⁻¹
  have hf : Integrable f := integrable_goldfeldRaw_left
    chi psi hchi hpsi hmul hzero hbetaLow hbetaHigh hX
  have hg : Integrable g := by
    exact integrable_inv_one_add_sq.const_mul (goldfeldBoundaryConstant N X)
  have hpoint : ∀ᵐ t : ℝ, ‖f t‖ ≤ g t :=
    Filter.Eventually.of_forall fun t =>
      norm_goldfeldRaw_left_le_inv_one_add_sq chi psi hchi hpsi hmul
        hbetaLow hbetaHigh hX t
  calc
    ‖∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I)‖ = ‖∫ t : ℝ, f t‖ := by rfl
    _ ≤ ∫ t : ℝ, g t := MeasureTheory.norm_integral_le_of_norm_le hg hpoint
    _ = goldfeldBoundaryConstant N X * Real.pi := by
      simp [g, MeasureTheory.integral_const_mul, integral_univ_inv_one_add_sq]

/-- After the contour normalization, a boundary constant at most `1/2`
costs at most `1/4`. -/
theorem norm_normalized_goldfeld_left_le_one_fourth
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 0 < X)
    (hboundary : goldfeldBoundaryConstant N X ≤ 1 / 2) :
    ‖(((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
        (((-1 / 2 : ℝ) : ℂ) + t * I))‖ ≤ 1 / 4 := by
  have hint := norm_goldfeldRaw_left_integral_le
    chi psi hchi hpsi hmul hzero hbetaLow hbetaHigh hX
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr (mul_pos (by norm_num) hpi))]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
        (1 / (2 * Real.pi)) *
          (goldfeldBoundaryConstant N X * Real.pi) := by gcongr
    _ = goldfeldBoundaryConstant N X / 2 := by field_simp
    _ ≤ 1 / 4 := by linarith

/-- The smoothed fourfold arithmetic side is summable in the Goldfeld range. -/
theorem summable_goldfeldFourfoldRieszTerm
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta)
    {X : ℝ} (hX : 0 < X) :
    Summable (goldfeldRieszTerm
      (fun n => goldfeldFourfoldCoeff chi psi n) beta 14 X) := by
  have hs : 1 < (((beta + 1 / 2 : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  let z : ArithmeticFunction ℂ := ArithmeticFunction.zeta
  let a : ArithmeticFunction ℂ := toArithmeticFunction (chi ·)
  let b : ArithmeticFunction ℂ := toArithmeticFunction (psi ·)
  let d : ArithmeticFunction ℂ := toArithmeticFunction ((chi * psi) ·)
  have hz : LSeriesSummable (fun n => z n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
    simpa [z] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have ha : LSeriesSummable (fun n => a n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
    exact (LSeriesSummable_congr _ fun hn =>
      chi.apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re chi hs)
  have hb : LSeriesSummable (fun n => b n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
    exact (LSeriesSummable_congr _ fun hn =>
      psi.apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re psi hs)
  have hd : LSeriesSummable (fun n => d n) (((beta + 1 / 2 : ℝ) : ℂ)) := by
    exact (LSeriesSummable_congr _ fun hn =>
      (chi * psi).apply_eq_toArithmeticFunction_apply hn).mp
        (DirichletCharacter.LSeriesSummable_of_one_lt_re (chi * psi) hs)
  exact summable_goldfeldRieszTerm
    (fun n => goldfeldFourfoldCoeff chi psi n) beta 14 (by norm_num) hX
      (by norm_num) (ArithmeticFunction.LSeriesSummable_mul
        (ArithmeticFunction.LSeriesSummable_mul
          (ArithmeticFunction.LSeriesSummable_mul hz ha) hb) hd)

/-- Once the explicit left line costs at most `1/4`, positivity of the
smoothed arithmetic side forces the residue to have norm at least `1/4`. -/
theorem one_fourth_le_norm_goldfeldPoleResidue
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    (hchiReal : chi ^ 2 = 1) (hpsiReal : psi ^ 2 = 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 28 ≤ X)
    (hboundary : goldfeldBoundaryConstant N X ≤ 1 / 2) :
    1 / 4 ≤ ‖goldfeldPoleResidue chi psi beta 14 X‖ := by
  have hXpos : 0 < X := by linarith
  have hsum := summable_goldfeldFourfoldRieszTerm chi psi hbetaLow hXpos
  have harith := one_half_le_goldfeldRiesz_tsum
    hchiReal hpsiReal beta (k := 14) (by norm_num) (X := X) (by
      norm_num
      exact hX) hsum
  have hright := normalized_goldfeld_fourfold_right_line
    chi psi beta 14 (by norm_num) hXpos (by norm_num : (0 : ℝ) < 1 / 2)
      (by simp; linarith)
  have hcontour := normalized_full_goldfeld_contour
    chi psi hchi hpsi hmul hzero hbetaLow hbetaHigh hXpos
  let R : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
      (((1 / 2 : ℝ) : ℂ) + t * I))
  let E : ℂ := (((1 / (2 * Real.pi) : ℝ) : ℂ) *
    ∫ t : ℝ, goldfeldRawIntegrand chi psi beta 14 X
      (((-1 / 2 : ℝ) : ℂ) + t * I))
  have hRE : R = goldfeldPoleResidue chi psi beta 14 X + E := by
    simpa [R, E] using hcontour
  have hrightEq : R = ∑' n : ℕ,
      goldfeldRieszTerm (fun m => goldfeldFourfoldCoeff chi psi m)
        beta 14 X n := by
    simpa [R, goldfeldRawIntegrand] using hright
  have hRlowerC : (((1 / 2 : ℝ) : ℂ)) ≤ R := by
    rw [hrightEq]
    exact harith
  have hRlower : (1 / 2 : ℝ) ≤ ‖R‖ := by
    have hre : (1 / 2 : ℝ) ≤ R.re := by
      exact hRlowerC.1
    exact hre.trans (le_abs_self R.re) |>.trans (Complex.abs_re_le_norm R)
  have hE : ‖E‖ ≤ 1 / 4 := by
    dsimp [E]
    exact norm_normalized_goldfeld_left_le_one_fourth
      chi psi hchi hpsi hmul hzero hbetaLow hbetaHigh hXpos hboundary
  have htriangle : ‖R‖ ≤ ‖goldfeldPoleResidue chi psi beta 14 X‖ + ‖E‖ := by
    rw [hRE]
    exact norm_add_le _ _
  linarith

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.norm_goldfeldRaw_left_integral_le
#print axioms MAPGoldfeldSiegel.norm_normalized_goldfeld_left_le_one_fourth
#print axioms MAPGoldfeldSiegel.summable_goldfeldFourfoldRieszTerm
#print axioms MAPGoldfeldSiegel.one_fourth_le_norm_goldfeldPoleResidue
