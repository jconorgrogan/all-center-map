import KoukCompletedLogDerivativeFunctionalEquation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Exact logarithmic derivative of the Dirichlet Gamma factor

This file reduces the archimedean term in the reflected L-logarithmic
derivative to `Complex.digamma`.  Thus the only remaining quantitative
functional-equation leaf is a digamma growth bound away from its poles.
-/

namespace KoukGammaFactorLogDerivative

open Complex

noncomputable section

private theorem piPower_ne_zero (s : ℂ) :
    (Real.pi : ℂ) ^ (-s / 2) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

private theorem logDeriv_piPower (s : ℂ) :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) := by
  have hexp : DifferentiableAt ℂ (fun z : ℂ => -z / 2) s := by fun_prop
  rw [logDeriv_apply, Complex.deriv_const_cpow hexp]
  have hderiv : deriv (fun z : ℂ => -z / 2) s = -(1 / 2 : ℂ) := by
    convert ((hasDerivAt_id s).neg.div_const (2 : ℂ)).deriv using 1 <;> ring
  rw [hderiv]
  have hpow := piPower_ne_zero s
  field_simp [hpow]

/-- Exact `Gamma_R` logarithmic derivative away from its poles. -/
theorem logDeriv_GammaR
    (s : ℂ) (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv Complex.Gammaℝ s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  let A : ℂ → ℂ := fun z => (Real.pi : ℂ) ^ (-z / 2)
  let B : ℂ → ℂ := fun z => Complex.Gamma (z / 2)
  have hAne : A s ≠ 0 := piPower_ne_zero s
  have hBne : B s ≠ 0 := Complex.Gamma_ne_zero hpole
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp only [A]
    exact (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hinner : DifferentiableAt ℂ (fun z : ℂ => z / 2) s := by fun_prop
  have hBdiff : DifferentiableAt ℂ B s := by
    exact (Complex.differentiableAt_Gamma (s / 2) hpole).comp s hinner
  have hmul := logDeriv_mul s hAne hBne hAdiff hBdiff
  have hAlog : logDeriv A s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) := by
    simpa only [A] using logDeriv_piPower s
  have hderivInner : deriv (fun z : ℂ => z / 2) s = (1 / 2 : ℂ) := by
    simpa using ((hasDerivAt_id s).div_const (2 : ℂ)).deriv
  have hBlog : logDeriv B s =
      (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    change logDeriv (Complex.Gamma ∘ fun z : ℂ => z / 2) s = _
    rw [logDeriv_comp (f := Complex.Gamma)
      (g := fun z : ℂ => z / 2)
      (Complex.differentiableAt_Gamma (s / 2) hpole)
      hinner, hderivInner, Complex.digamma_def]
    ring
  change logDeriv (fun z => A z * B z) s = _
  rw [hmul, hAlog, hBlog]

/-- Even-character specialization of the exact Gamma-factor formula. -/
theorem logDeriv_gammaFactor_of_even
    {q : ℕ} (chi : DirichletCharacter ℂ q) (hEven : chi.Even)
    (s : ℂ) (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor chi) s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  rw [show DirichletCharacter.gammaFactor chi = Complex.Gammaℝ by
    funext z
    exact hEven.gammaFactor_def z]
  exact logDeriv_GammaR s hpole

/-- Odd-character specialization; the shift by one is retained exactly. -/
theorem logDeriv_gammaFactor_of_odd
    {q : ℕ} (chi : DirichletCharacter ℂ q) (hOdd : chi.Odd)
    (s : ℂ) (hpole : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ)) :
    logDeriv (DirichletCharacter.gammaFactor chi) s =
      -(1 / 2 : ℂ) * Complex.log (Real.pi : ℂ) +
        (1 / 2 : ℂ) * Complex.digamma ((s + 1) / 2) := by
  rw [show DirichletCharacter.gammaFactor chi =
      fun z => Complex.Gammaℝ (z + 1) by
    funext z
    exact hOdd.gammaFactor_def z]
  have hinner : DifferentiableAt ℂ (fun z : ℂ => z + 1) s := by fun_prop
  have hGRdiff : DifferentiableAt ℂ Complex.Gammaℝ (s + 1) := by
    change DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) *
        Complex.Gamma (z / 2)) (s + 1)
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        ((Complex.differentiableAt_Gamma ((s + 1) / 2) hpole).comp
          (s + 1) (by fun_prop))
  have hderivInner : deriv (fun z : ℂ => z + 1) s = 1 := by
    simpa using ((hasDerivAt_id s).add_const (1 : ℂ)).deriv
  change logDeriv (Complex.Gammaℝ ∘ fun z : ℂ => z + 1) s = _
  rw [logDeriv_comp (f := Complex.Gammaℝ)
    (g := fun z : ℂ => z + 1) hGRdiff hinner, hderivInner, mul_one,
    logDeriv_GammaR (s + 1) hpole]

end
end KoukGammaFactorLogDerivative

#print axioms KoukGammaFactorLogDerivative.logDeriv_GammaR
#print axioms KoukGammaFactorLogDerivative.logDeriv_gammaFactor_of_even
#print axioms KoukGammaFactorLogDerivative.logDeriv_gammaFactor_of_odd
