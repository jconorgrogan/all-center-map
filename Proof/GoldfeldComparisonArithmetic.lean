import GoldfeldFourfoldContour
import RieszCoefficientNormalization

/-!
# Arithmetic and residue bookkeeping in Goldfeld's comparison

This file records the exact positive main term and the explicit residue after
the certified contour shift.
-/

namespace MAPGoldfeldSiegel

open ComplexOrder Complex
open scoped ArithmeticFunction LSeries.notation BigOperators
open MAPAppendixA4RieszInversion MAPAppendixA4RieszKernel

noncomputable section

/-- The complex-valued Riesz weight lies on the nonnegative real axis. -/
theorem rieszWeight_nonneg_complex (k : ℕ) (x : ℝ) :
    0 ≤ rieszWeight k x := by
  change 0 ≤ ((((max (1 - x) 0) ^ k : ℝ) : ℂ))
  exact_mod_cast pow_nonneg (le_max_right (1 - x) 0) k

/-- Every term of the smoothed Goldfeld series is nonnegative. -/
theorem goldfeldRieszTerm_nonneg
    {N : ℕ} {chi psi : DirichletCharacter ℂ N}
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1)
    (beta : ℝ) (k : ℕ) (X : ℝ) (n : ℕ) :
    0 ≤ goldfeldRieszTerm
      (fun m => goldfeldFourfoldCoeff chi psi m) beta k X n := by
  unfold goldfeldRieszTerm
  exact mul_nonneg
    (LSeries.term_nonneg (goldfeldFourfoldCoeff_nonneg hchi hpsi n) beta)
    (rieszWeight_nonneg_complex k ((n : ℝ) / X))

/-- The distinguished coefficient is exactly the Riesz mass at `1/X`. -/
theorem goldfeldRieszTerm_one
    {N : ℕ} (chi psi : DirichletCharacter ℂ N)
    (beta : ℝ) (k : ℕ) (X : ℝ) :
    goldfeldRieszTerm (fun m => goldfeldFourfoldCoeff chi psi m)
      beta k X 1 = rieszWeight k (1 / X) := by
  unfold goldfeldRieszTerm
  simp [goldfeldFourfoldCoeff, toArithmeticFunction]

/-- The source lower bound survives with mass `1/2` for the compact Riesz
replacement once `X ≥ 2k`. -/
theorem one_half_le_goldfeldRiesz_tsum
    {N : ℕ} {chi psi : DirichletCharacter ℂ N}
    (hchi : chi ^ 2 = 1) (hpsi : psi ^ 2 = 1)
    (beta : ℝ) {k : ℕ} (hk : 0 < k) {X : ℝ}
    (hX : (2 : ℝ) * k ≤ X)
    (hsum : Summable (goldfeldRieszTerm
      (fun m => goldfeldFourfoldCoeff chi psi m) beta k X)) :
    ((1 / 2 : ℝ) : ℂ) ≤
      ∑' n : ℕ, goldfeldRieszTerm
        (fun m => goldfeldFourfoldCoeff chi psi m) beta k X n := by
  have hone := MAPAppendixA4RieszCoefficients.one_half_le_rieszWeight_one_div
    hk hX
  have honeC : ((1 / 2 : ℝ) : ℂ) ≤ rieszWeight k (1 / X) := by
    change ((1 / 2 : ℝ) : ℂ) ≤
      ((MAPAppendixA4RieszCoefficients.rieszWeight k (1 / X) : ℝ) : ℂ)
    exact_mod_cast hone
  calc
    ((1 / 2 : ℝ) : ℂ) ≤
        goldfeldRieszTerm (fun m => goldfeldFourfoldCoeff chi psi m)
          beta k X 1 := by rw [goldfeldRieszTerm_one]; exact honeC
    _ ≤ ∑' n : ℕ, goldfeldRieszTerm
          (fun m => goldfeldFourfoldCoeff chi psi m) beta k X n :=
      hsum.le_tsum 1 (fun n hn =>
        goldfeldRieszTerm_nonneg hchi hpsi beta k X n)

/-- The abstract residue is the literal zeta residue times the three L-values
and the Riesz kernel at `1-β`. -/
theorem goldfeldPoleResidue_eq
    {N : ℕ} [NeZero N] (chi psi : DirichletCharacter ℂ N)
    {beta : ℝ} (hbeta : beta < 1)
    (hzero : DirichletCharacter.LFunction chi beta = 0)
    (k : ℕ) (X : ℝ) :
    goldfeldPoleResidue chi psi beta k X =
      rieszMellinKernel k (1 - beta) *
        (X : ℂ) ^ ((1 - beta : ℝ) : ℂ) *
        DirichletCharacter.LFunction chi 1 *
        DirichletCharacter.LFunction psi 1 *
        DirichletCharacter.LFunction (chi * psi) 1 := by
  have hp : ((1 - beta : ℝ) : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (ne_of_gt hbeta))
  have hq := MAPAppendixA4Detector.shiftedZeroQuotient_eq_div chi hzero hp
  unfold goldfeldPoleResidue goldfeldZeroCanceledFactor
  have hpcast : (1 - (beta : ℂ)) = ((1 - beta : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hpcast]
  rw [hq]
  have harg : (beta : ℂ) + (1 - beta : ℝ) = 1 := by
    push_cast
    ring
  rw [harg]
  rw [rieszMellinKernel_eq_div_regularized]
  field_simp

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.one_half_le_goldfeldRiesz_tsum
#print axioms MAPGoldfeldSiegel.goldfeldPoleResidue_eq
