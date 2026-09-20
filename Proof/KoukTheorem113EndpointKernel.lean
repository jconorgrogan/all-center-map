import PrimitiveRemovableClosure
import EndpointRegularizedZeroPrimitive
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The endpoint-regularized Perron kernel in Koukoulopoulos Theorem 11.3

The contour proof of Theorem 11.3 uses

`(x^s - 1) / s`

instead of `x^s / s`.  The subtraction is not cosmetic: it removes the
kernel's singularity at `s = 0` and makes the residue at a zero `rho` equal
to the endpoint-correct term `(x^rho - 1) / rho`, with value `log x` when
`rho = 0`.

We realize the continuous extension as the divided slope of `s ↦ x^s`.
This gives a globally holomorphic function directly from Mathlib's
`differentiableOn_dslope`; no informal limit convention is needed.
-/

namespace KoukTheorem113EndpointKernel

open Complex Set
open APFoundation MAPEndpointRegularizedZeroPrimitive

noncomputable section

/-- The entire extension of `(x^s - 1) / s` at `s = 0`. -/
def endpointPerronKernel (x : ℝ) : ℂ → ℂ :=
  dslope (fun s : ℂ => (x : ℂ) ^ s) 0

/-- Away from the removable point, the kernel is the literal quotient used
in Koukoulopoulos (11.5). -/
theorem endpointPerronKernel_of_ne {x : ℝ} {s : ℂ} (hs : s ≠ 0) :
    endpointPerronKernel x s = ((x : ℂ) ^ s - 1) / s := by
  rw [endpointPerronKernel, dslope_of_ne _ hs]
  simp only [slope, vsub_eq_sub, sub_zero, Complex.cpow_zero]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

/-- At the removable point, the kernel has the exact endpoint value
`log x`. -/
theorem endpointPerronKernel_zero {x : ℝ} (hx : 0 < x) :
    endpointPerronKernel x 0 = (Real.log x : ℂ) := by
  rw [endpointPerronKernel, dslope_same]
  have hderiv := (Complex.hasStrictDerivAt_const_cpow
    (x := (x : ℂ)) (y := (0 : ℂ))
    (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).hasDerivAt.deriv
  rw [hderiv]
  simp only [Complex.cpow_zero, one_mul]
  exact (Complex.ofReal_log hx.le).symm

/-- The divided-slope construction agrees exactly with the endpoint
primitive already used by the MAP zero-field layer. -/
theorem endpointPerronKernel_eq_endpointRegularizedZeroTerm
    {x : ℝ} (hx : 0 < x) (s : ℂ) :
    endpointPerronKernel x s = endpointRegularizedZeroTerm x s := by
  by_cases hs : s = 0
  · subst s
    rw [endpointPerronKernel_zero hx]
    simp [endpointRegularizedZeroTerm]
  · rw [endpointPerronKernel_of_ne hs]
    simp [endpointRegularizedZeroTerm, regularizedZeroTerm, hs]

/-- The endpoint kernel is holomorphic on the whole complex plane. -/
theorem differentiable_endpointPerronKernel {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (endpointPerronKernel x) := by
  have hpow : Differentiable ℂ (fun s : ℂ => (x : ℂ) ^ s) :=
    differentiable_id.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  rw [endpointPerronKernel]
  rw [← differentiableOn_univ]
  exact (differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
    Filter.univ_mem).2 hpow.differentiableOn

/-- Analyticity form consumed by the finite-pole residue layer. -/
theorem analytic_endpointPerronKernel {x : ℝ} (hx : 0 < x) :
    AnalyticOnNhd ℂ (endpointPerronKernel x) Set.univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr
    (differentiable_endpointPerronKernel hx)

/-- The source integrand in Koukoulopoulos Theorem 11.3, before its finite
pole removable extension. -/
def endpointPerronContourIntegrand {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (x : ℝ) (s : ℂ) : ℂ :=
  (-logDeriv (DirichletCharacter.LFunction chi) s) *
    endpointPerronKernel x s

/-- At every point where `L(s,chi)` is nonzero, the modified contour
integrand is holomorphic, including `s = 0` whenever that is not a zero. -/
theorem differentiableAt_endpointPerronContourIntegrand_of_L_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hregular : s ≠ 1 ∨ chi ≠ 1)
    (hL : DirichletCharacter.LFunction chi s ≠ 0) :
    DifferentiableAt ℂ (endpointPerronContourIntegrand chi x) s := by
  have hLa : AnalyticAt ℂ (DirichletCharacter.LFunction chi) s := by
    rcases hregular with hs | hchi
    · rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [eventually_ne_nhds hs] with z hz
      exact DirichletCharacter.differentiableAt_LFunction chi z (.inl hz)
    · exact (DirichletCharacter.differentiable_LFunction hchi).analyticAt s
  have hlog : DifferentiableAt ℂ
      (logDeriv (DirichletCharacter.LFunction chi)) s := by
    simpa only [logDeriv, Pi.div_apply] using
      (hLa.deriv.div hLa hL).differentiableAt
  unfold endpointPerronContourIntegrand
  exact hlog.neg.mul (differentiable_endpointPerronKernel hx s)

end
end KoukTheorem113EndpointKernel

#print axioms KoukTheorem113EndpointKernel.endpointPerronKernel_of_ne
#print axioms KoukTheorem113EndpointKernel.endpointPerronKernel_zero
#print axioms KoukTheorem113EndpointKernel.endpointPerronKernel_eq_endpointRegularizedZeroTerm
#print axioms KoukTheorem113EndpointKernel.differentiable_endpointPerronKernel
