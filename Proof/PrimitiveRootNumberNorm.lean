import MRTLemma29FiniteFourier
import TrivialZeroEndpoint

/-!
# Unit norm of the primitive Dirichlet root number

Ramachandra's critical-line functional-equation multiplier may be discarded
after taking norms only because the primitive root number has norm one.  The
project previously certified merely that it is nonzero.  This file proves the
exact norm statement for every primitive complex Dirichlet character by
Parseval for the finite Fourier transform.

This does not address the shifted multiplier occurring after a Mellin contour
shift; that factor needs the separate uniform Gamma-ratio estimate.
-/

namespace FixedCharacterPrimitiveRootNumber

open scoped BigOperators ZMod
open Complex

noncomputable section

/-- The finite Fourier transform of a primitive character has exact energy
`phi(N) * |tau(chi)|^2`. -/
theorem primitive_dft_energy_eq_totient_mul_gaussNormSq
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) :
    (∑ k : ZMod N, ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2) =
      (N.totient : ℝ) * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
  classical
  have hpoint (k : ZMod N) :
      ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2 =
        ‖chi⁻¹ (-k)‖ ^ 2 * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
    rw [hprim.fourierTransform_eq_inv_mul_gaussSum]
    rw [norm_mul, mul_pow]
  calc
    (∑ k : ZMod N, ‖ZMod.dft (chi : ZMod N → ℂ) k‖ ^ 2) =
        ∑ k : ZMod N,
          ‖chi⁻¹ (-k)‖ ^ 2 * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
      exact Finset.sum_congr rfl (fun k _hk => hpoint k)
    _ = (∑ k : ZMod N, ‖chi⁻¹ (-k)‖ ^ 2) *
          ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
      rw [Finset.sum_mul]
    _ = (∑ k : ZMod N, ‖chi⁻¹ k‖ ^ 2) *
          ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
      have hneg :=
        (Equiv.sum_comp (Equiv.neg (ZMod N))
          (fun k : ZMod N => ‖chi⁻¹ (-k)‖ ^ 2)).symm
      simpa only [Equiv.neg_apply, neg_neg] using congrArg
        (fun x : ℝ => x * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2) hneg
    _ = (N.totient : ℝ) * ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 := by
      rw [MAPMRTLemma29Proof.dirichletCharacter_energy]

/-- Exact square-root conductor norm of the Gauss sum of any primitive
complex Dirichlet character. -/
theorem norm_gaussSum_stdAddChar_eq_sqrt
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) :
    ‖gaussSum chi ZMod.stdAddChar‖ = Real.sqrt N := by
  have hparseval := MAPMRTLemma29Proof.dft_energy (chi : ZMod N → ℂ)
  rw [MAPMRTLemma29Proof.dirichletCharacter_energy] at hparseval
  have hprimitive :=
    primitive_dft_energy_eq_totient_mul_gaussNormSq chi hprim
  rw [hprimitive] at hparseval
  have hphi : 0 < (N.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsq : ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 = (N : ℝ) := by
    nlinarith
  have hsqrtSq : (Real.sqrt N) ^ 2 = (N : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  nlinarith [norm_nonneg (gaussSum chi ZMod.stdAddChar), Real.sqrt_nonneg (N : ℝ)]

/-- The global root number in Mathlib's primitive functional equation has
unit norm. -/
theorem primitive_rootNumber_norm_eq_one
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) :
    ‖chi.rootNumber‖ = 1 := by
  classical
  have hNpos : 0 < N := NeZero.pos N
  have hgauss := norm_gaussSum_stdAddChar_eq_sqrt chi hprim
  have hphase : ‖(Complex.I : ℂ) ^ (if chi.Even then 0 else 1)‖ = 1 := by
    split_ifs <;> simp
  have hconductor : ‖(N : ℂ) ^ (1 / 2 : ℂ)‖ = Real.sqrt N := by
    rw [Complex.norm_natCast_cpow_of_pos hNpos]
    simpa [Real.sqrt_eq_rpow]
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by positivity
  unfold DirichletCharacter.rootNumber
  simp only [norm_div, hgauss, hphase, div_one, hconductor]
  exact div_self hsqrt

/-- The complete conductor/root-number multiplier in Mathlib's primitive
functional equation has unit norm on the critical line.  This is the precise
factor that may be discarded in the unshifted part of Ramachandra's formula.
The corresponding factor at `s+w` is intentionally not covered. -/
theorem primitive_criticalLine_multiplier_norm_eq_one
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (t : ℝ) :
    ‖(N : ℂ) ^
        ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) - 1 / 2) *
        chi.rootNumber‖ = 1 := by
  rw [norm_mul, primitive_rootNumber_norm_eq_one chi hprim, mul_one]
  rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  norm_num

/-- Exact conductor loss after a complex Mellin shift.  All remaining growth
in the ordinary (uncompleted) functional-equation multiplier is therefore in
the shifted gamma quotient. -/
theorem primitive_shifted_multiplier_norm_eq_rpow
    {N : ℕ} [NeZero N] (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (t : ℝ) (w : ℂ) :
    ‖(N : ℂ) ^
        (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) + w) - 1 / 2) *
        chi.rootNumber‖ = Real.rpow N w.re := by
  rw [norm_mul, primitive_rootNumber_norm_eq_one chi hprim, mul_one]
  rw [Complex.norm_natCast_cpow_of_pos (NeZero.pos N)]
  congr 1
  norm_num

end
end FixedCharacterPrimitiveRootNumber

#print axioms FixedCharacterPrimitiveRootNumber.primitive_dft_energy_eq_totient_mul_gaussNormSq
#print axioms FixedCharacterPrimitiveRootNumber.norm_gaussSum_stdAddChar_eq_sqrt
#print axioms FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one
#print axioms FixedCharacterPrimitiveRootNumber.primitive_criticalLine_multiplier_norm_eq_one
#print axioms FixedCharacterPrimitiveRootNumber.primitive_shifted_multiplier_norm_eq_rpow
