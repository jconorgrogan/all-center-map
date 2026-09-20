import FunctionalZeroTransport
import KoukNegativeHalfPlaneNonvanishing

/-!
# Full open-critical-strip zero transport

The existing functional-equation transport is packaged for the strict lower
half because that is what the A.5 counting argument needs.  The same proof
works throughout `0 < Re ρ < 1`; this source-facing form is needed to carry a
selected horizontal clearance to the inverse character.
-/

namespace KoukFullCriticalZeroTransport

open Complex DirichletZeros
open MAPFunctionalZeroTransport

noncomputable section

theorem analyticOrderAt_regularized_transport_openStrip
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {rho : ℂ} (hrhoPos : 0 < rho.re) (hrhoOne : rho.re < 1) :
    analyticOrderAt (regularizedLFunction chi) rho =
      analyticOrderAt (regularizedLFunction chi⁻¹) (1 - rho) := by
  have hreflect : 0 < (1 - rho).re := by
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  calc
    analyticOrderAt (regularizedLFunction chi) rho =
        analyticOrderAt (DirichletCharacter.completedLFunction chi) rho :=
      analyticOrderAt_regularized_eq_completed hchi hrhoPos
    _ = analyticOrderAt
          (DirichletCharacter.completedLFunction chi⁻¹) (1 - rho) :=
      analyticOrderAt_completed_transport hprim hchi rho
    _ = analyticOrderAt (regularizedLFunction chi⁻¹) (1 - rho) :=
      (analyticOrderAt_regularized_eq_completed (inverse_ne_one hchi)
        hreflect).symm

theorem regularizedLFunction_one_sub_eq_zero_openStrip
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {rho : ℂ} (hrhoPos : 0 < rho.re) (hrhoOne : rho.re < 1)
    (hzero : regularizedLFunction chi rho = 0) :
    regularizedLFunction chi⁻¹ (1 - rho) = 0 := by
  have hanChi := (differentiable_regularizedLFunction chi).analyticAt rho
  have hanInv :=
    (differentiable_regularizedLFunction chi⁻¹).analyticAt (1 - rho)
  have horder : analyticOrderAt (regularizedLFunction chi) rho ≠ 0 :=
    hanChi.analyticOrderAt_ne_zero.mpr hzero
  apply hanInv.analyticOrderAt_ne_zero.mp
  rw [← analyticOrderAt_regularized_transport_openStrip
    hprim hchi hrhoPos hrhoOne]
  exact horder

/-- Value-level reflection of every nonreal zero.  This includes the endpoint
sectors `Re rho = 0,1` and therefore avoids importing a zero-free-line theorem
into the common-height clearance argument. -/
theorem regularizedLFunction_one_sub_eq_zero_of_nonreal
    {q : ℕ} [NeZero q] {chi : DirichletCharacter ℂ q}
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {rho : ℂ} (him : rho.im ≠ 0)
    (hzeroInv : regularizedLFunction chi⁻¹ rho = 0) :
    regularizedLFunction chi (1 - rho) = 0 := by
  have hInvNe : chi⁻¹ ≠ 1 := inverse_ne_one hchi
  have hrho0 : rho ≠ 0 := by
    intro hrho
    rw [hrho] at him
    norm_num at him
  have hreflect0 : 1 - rho ≠ 0 := by
    intro hreflect
    have hi := congrArg Complex.im hreflect
    simp at hi
    exact him hi
  have hLInv : DirichletCharacter.LFunction chi⁻¹ rho = 0 := by
    simpa [regularizedLFunction, hInvNe] using hzeroInv
  have hgammaInv : DirichletCharacter.gammaFactor chi⁻¹ rho ≠ 0 :=
    KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
      chi⁻¹ him
  have heqInv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    chi⁻¹ rho (Or.inl hrho0)
  have hcompletedInv :
      DirichletCharacter.completedLFunction chi⁻¹ rho = 0 := by
    have hdiv : DirichletCharacter.completedLFunction chi⁻¹ rho /
        DirichletCharacter.gammaFactor chi⁻¹ rho = 0 := by
      rw [← heqInv, hLInv]
    exact (div_eq_zero_iff).mp hdiv |>.resolve_right hgammaInv
  have hFE := hprim.completedLFunction_one_sub rho
  have hcompleted :
      DirichletCharacter.completedLFunction chi (1 - rho) = 0 := by
    simpa [hcompletedInv] using hFE
  have hL : DirichletCharacter.LFunction chi (1 - rho) = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor
      chi (1 - rho) (Or.inl hreflect0), hcompleted, zero_div]
  simpa [regularizedLFunction, hchi] using hL

end

end KoukFullCriticalZeroTransport

#print axioms KoukFullCriticalZeroTransport.regularizedLFunction_one_sub_eq_zero_openStrip
#print axioms KoukFullCriticalZeroTransport.regularizedLFunction_one_sub_eq_zero_of_nonreal
