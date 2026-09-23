import GoldfeldResidueLower
import GoldfeldLemma11TwoLValue
import ZeroFreeSiegelSpine

/-!
# Same-level Goldfeld comparison

This module cancels the real Riesz pole against the exceptional L-value zero
gap and inserts the two forms of Lemma 11.2.
-/

namespace MAPGoldfeldSiegel

open Complex Set
open MAPAppendixA4RieszKernel

noncomputable section

/-- On the nonnegative real axis the regularized order-14 Riesz kernel is at
most one. -/
theorem norm_regularizedRieszKernel_fourteen_real_le_one
    {u : ℝ} (hu : 0 ≤ u) :
    ‖regularizedRieszKernel 14 (u : ℂ)‖ ≤ 1 := by
  unfold regularizedRieszKernel
  rw [norm_div, Complex.norm_natCast, norm_prod]
  have hfactor : ∀ j ∈ Finset.range 14,
      ((j + 1 : ℕ) : ℝ) ≤ ‖(u : ℂ) + ((j + 1 : ℕ) : ℂ)‖ := by
    intro j hj
    rw [show (u : ℂ) + ((j + 1 : ℕ) : ℂ) =
        ((u + (j + 1 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hprod : (Nat.factorial 14 : ℝ) ≤
      ∏ j ∈ Finset.range 14, ‖(u : ℂ) + ((j + 1 : ℕ) : ℂ)‖ := by
    calc
      (Nat.factorial 14 : ℝ) =
          ∏ j ∈ Finset.range 14, (((j + 1 : ℕ) : ℝ)) := by
        exact_mod_cast (Finset.prod_range_add_one_eq_factorial 14).symm
      _ ≤ _ := Finset.prod_le_prod₀ (fun j hj => by positivity) hfactor
  have hdenpos : 0 <
      ∏ j ∈ Finset.range 14, ‖(u : ℂ) + ((j + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le (by positivity : (0 : ℝ) < Nat.factorial 14) hprod
  exact (div_le_one hdenpos).2 hprod

/-- The only singular cost of the order-14 Riesz kernel at a positive real
gap is the explicit reciprocal gap. -/
theorem norm_rieszMellinKernel_fourteen_real_le_inv
    {u : ℝ} (hu : 0 < u) :
    ‖rieszMellinKernel 14 (u : ℂ)‖ ≤ u⁻¹ := by
  rw [rieszMellinKernel_eq_div_regularized, norm_div,
    norm_real, Real.norm_eq_abs, abs_of_pos hu]
  simpa [one_div] using (div_le_div_iff_of_pos_right hu).2
    (norm_regularizedRieszKernel_fourteen_real_le_one hu.le)

/-- The `j=1` estimate and the real zero give the exact upper bound for the
exceptional L-value that cancels the Riesz pole. -/
theorem primitive_quadratic_norm_LFunction_one_le_gap
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi : DirichletCharacter ℂ N)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1) (hreal : chi ^ 2 = 1)
    {beta : ℝ} (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    (hzero : DirichletCharacter.LFunction chi beta = 0) :
    ‖DirichletCharacter.LFunction chi 1‖ ≤
      (6000 * Real.rpow (Real.sqrt N) (1 - beta) *
        (1 + Real.log N) ^ 2) * (1 - beta) := by
  let M : ℝ := 6000 * Real.rpow (Real.sqrt N) (1 - beta) *
    (1 + Real.log N) ^ 2
  apply MAPZeroFreeSiegelSpine.norm_LFunction_one_le_gap_mul_of_deriv_bound
    chi hchi hbetaHigh.le hzero
  intro x hx
  have hxhalf : 1 / 2 ≤ x := hbetaLow.le.trans hx.1
  have hxone : x ≤ 1 := hx.2.le
  have hderiv := primitive_quadratic_deriv_LFunction_t0_le
    hN chi hprim hchi hreal hxhalf hxone
  have hRone : (1 : ℝ) ≤ Real.sqrt N := Real.one_le_sqrt.2 (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hpow : Real.rpow (Real.sqrt N) (1 - x) ≤
      Real.rpow (Real.sqrt N) (1 - beta) :=
    Real.rpow_le_rpow_of_exponent_le hRone (by linarith [hx.1])
  exact hderiv.trans (by
    dsimp [M]
    gcongr
    exact hx.1)

/-- Same-level quantitative Goldfeld comparison before choosing the smoothing
scale.  The left side is deliberately multiplicative so the next layer can
insert a polynomial `X` without division bookkeeping. -/
theorem sameLevel_goldfeld_comparison
    {N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (chi psi : DirichletCharacter ℂ N)
    (hchiPrim : chi.IsPrimitive)
    (hchi : chi ≠ 1) (hpsi : psi ≠ 1) (hmul : chi * psi ≠ 1)
    (hchiReal : chi ^ 2 = 1) (hpsiReal : psi ^ 2 = 1)
    {beta : ℝ} (hzero : DirichletCharacter.LFunction chi beta = 0)
    (hbetaLow : 1 / 2 < beta) (hbetaHigh : beta < 1)
    {X : ℝ} (hX : 28 ≤ X)
    (hboundary : goldfeldBoundaryConstant N X ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤
      18000 * Real.rpow X (1 - beta) *
        Real.rpow (Real.sqrt N) (1 - beta) *
        (1 + Real.log N) ^ 3 *
        ‖DirichletCharacter.LFunction psi 1‖ := by
  have hgap : 0 < 1 - beta := sub_pos.mpr hbetaHigh
  have hXpos : 0 < X := by linarith
  have hres := one_fourth_le_norm_goldfeldPoleResidue
    chi psi hchi hpsi hmul hchiReal hpsiReal hzero hbetaLow hbetaHigh
      hX hboundary
  have hresEq := goldfeldPoleResidue_eq chi psi hbetaHigh hzero 14 X
  have hk := norm_rieszMellinKernel_fourteen_real_le_inv hgap
  have hchiOne := primitive_quadratic_norm_LFunction_one_le_gap
    hN chi hchiPrim hchi hchiReal hbetaLow hbetaHigh hzero
  have hprodOne := nonprincipal_norm_LFunction_one_le (chi * psi) hmul
  have hk' : ‖rieszMellinKernel 14 (1 - (beta : ℂ))‖ ≤ (1 - beta)⁻¹ := by
    convert hk using 1
    push_cast
    rfl
  have hchiOne' : ‖DirichletCharacter.LFunction chi 1‖ ≤
      (6000 * (Real.sqrt N) ^ (1 - beta) *
        (1 + Real.log N) ^ 2) * (1 - beta) := by
    simpa only [Real.rpow_eq_pow] using hchiOne
  have hupper : ‖goldfeldPoleResidue chi psi beta 14 X‖ ≤
      (1 - beta)⁻¹ * Real.rpow X (1 - beta) *
        ((6000 * Real.rpow (Real.sqrt N) (1 - beta) *
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
          ((6000 * Real.rpow (Real.sqrt N) (1 - beta) *
            (1 + Real.log N) ^ 2) * (1 - beta)) *
          ‖DirichletCharacter.LFunction psi 1‖ *
          (3 * (1 + Real.log N)) := hcomp
    _ = 18000 * Real.rpow X (1 - beta) *
        Real.rpow (Real.sqrt N) (1 - beta) *
        (1 + Real.log N) ^ 3 *
        ‖DirichletCharacter.LFunction psi 1‖ := by
      field_simp
      ring

end
end MAPGoldfeldSiegel

#print axioms MAPGoldfeldSiegel.norm_rieszMellinKernel_fourteen_real_le_inv
#print axioms MAPGoldfeldSiegel.primitive_quadratic_norm_LFunction_one_le_gap
#print axioms MAPGoldfeldSiegel.sameLevel_goldfeld_comparison
