import GoldfeldSameLevelComparison
import GoldfeldImprimitiveDerivative

/-!
# Same-level Goldfeld comparison without a primitivity hypothesis

The common-level lift of the exceptional character need not be primitive.
Complete-period cancellation still gives the `j = 1` instance of Lemma 11.2
with current-level conductor cost `N^(1-sigma)`.  This is enough for the
Goldfeld pole cancellation, at the price of replacing the square-root factor
by `N^(1-beta)`.
-/

namespace MAPGoldfeldSiegel

open Complex Set
open MAPAppendixA4RieszKernel

noncomputable section

/-- The `j=1` estimate and a real zero bound the value at one for every
nonprincipal character at its current (possibly imprimitive) level. -/
theorem nonprincipal_norm_LFunction_one_le_gap
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N) (hchi : chi ≠ 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hzero : DirichletCharacter.LFunction chi beta = 0) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      (2000 * Real.rpow (N : ℝ) (1 - beta) *
        (1 + Real.log N) ^ 2) * (1 - beta) := by
  let M : ℝ := 2000 * Real.rpow (N : ℝ) (1 - beta) *
    (1 + Real.log N) ^ 2
  apply MAPZeroFreeSiegelSpine.norm_LFunction_one_le_gap_mul_of_deriv_bound
    chi hchi hbetaHigh.le hzero
  intro x hx
  have hxhalf : 1 / 2 ≤ x := hbetaLow.le.trans hx.1
  have hxone : x ≤ 1 := hx.2.le
  have hderiv := nonprincipal_deriv_LFunction_t0_le
    hN chi hchi hxhalf hxone
  have hNone : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hpow : Real.rpow (N : ℝ) (1 - x) ≤
      Real.rpow (N : ℝ) (1 - beta) :=
    Real.rpow_le_rpow_of_exponent_le hNone (by linarith [hx.1])
  exact hderiv.trans (by
    dsimp [M]
    gcongr
    exact hx.1)

/-- Same-level quantitative Goldfeld comparison for a possibly imprimitive
exceptional character. -/
theorem sameLevel_goldfeld_comparison_nonprimitive
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi psi : DirichletCharacter ℂ N)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    (hchiReal : chi ^ 2 = 1) (hpsiReal : psi ^ 2 = 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 28 ≤ X)
    (hboundary : goldfeldBoundaryConstant N X ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤
      6000 * Real.rpow X (1 - beta) *
        Real.rpow (N : ℝ) (1 - beta) *
        (1 + Real.log N) ^ 3 *
        ‖DirichletCharacter.LFunction psi 1‖ := by
  have hgap : 0 < 1 - beta := sub_pos.mpr hbetaHigh
  have hXpos : 0 < X := by linarith
  have hres := one_fourth_le_norm_goldfeldPoleResidue
    chi psi hchi hpsi hmul hchiReal hpsiReal hzero hbetaLow hbetaHigh
      hX hboundary
  have hresEq := goldfeldPoleResidue_eq chi psi hbetaHigh hzero 14 X
  have hk := norm_rieszMellinKernel_fourteen_real_le_inv hgap
  have hchiOne := nonprincipal_norm_LFunction_one_le_gap
    hN chi hchi hbetaLow hbetaHigh hzero
  have hprodOne := nonprincipal_norm_LFunction_one_le (chi * psi) hmul
  have hchiOne' : ‖DirichletCharacter.LFunction chi 1‖ ≤
      (2000 * (N : ℝ) ^ (1 - beta) *
        (1 + Real.log N) ^ 2) * (1 - beta) := by
    simpa only [Real.rpow_eq_pow] using hchiOne
  have hk' : ‖rieszMellinKernel 14 (1 - (beta : ℂ))‖ ≤ (1 - beta)⁻¹ := by
    convert hk using 1
    push_cast
    rfl
  have hupper : ‖goldfeldPoleResidue chi psi beta 14 X‖ ≤
      (1 - beta)⁻¹ * Real.rpow X (1 - beta) *
        ((2000 * Real.rpow (N : ℝ) (1 - beta) *
          (1 + Real.log N) ^ 2) * (1 - beta)) *
        ‖DirichletCharacter.LFunction psi 1‖ *
        (3 * (1 + Real.log N)) := by
    rw [hresEq]
    simp only [norm_mul]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hXpos]
    norm_num
    gcongr
  have hcomp := hres.trans hupper
  calc
    (1 / 4 : ℝ) ≤
        (1 - beta)⁻¹ * Real.rpow X (1 - beta) *
          ((2000 * Real.rpow (N : ℝ) (1 - beta) *
            (1 + Real.log N) ^ 2) * (1 - beta)) *
          ‖DirichletCharacter.LFunction psi 1‖ *
          (3 * (1 + Real.log N)) := hcomp
    _ = 6000 * Real.rpow X (1 - beta) *
        Real.rpow (N : ℝ) (1 - beta) *
        (1 + Real.log N) ^ 3 *
        ‖DirichletCharacter.LFunction psi 1‖ := by
      field_simp
      ring

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.nonprincipal_norm_LFunction_one_le_gap
#print axioms MAPGoldfeldSiegel.sameLevel_goldfeld_comparison_nonprimitive
