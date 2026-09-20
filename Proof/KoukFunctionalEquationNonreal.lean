import KoukGammaFactorLogDerivative
import KoukEndpointContourBounds

/-!
# Nonreal specialization of the completed functional equation

The horizontal Kouk contour has nonzero ordinate.  At such points all
archimedean poles and both exceptional completed-L points are absent.  This
module discharges those legality hypotheses once and exposes the exact
uncompleted logarithmic-derivative reflection with only the two literal
L-nonvanishing assumptions.
-/

namespace KoukFunctionalEquationNonreal

open Complex
open KoukNegativeHalfPlaneNonvanishing
open KoukCompletedLogDerivativeFunctionalEquation

noncomputable section

/-- The Dirichlet Gamma factor is differentiable at every nonreal point. -/
theorem differentiableAt_gammaFactor_of_im_ne_zero
    {q : ℕ} (chi : DirichletCharacter ℂ q) {s : ℂ}
    (him : s.im ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.gammaFactor chi) s := by
  have hpoleEven : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hi := congrArg Complex.im hm
    simp at hi
    exact him hi
  have hpoleOdd : ∀ m : ℕ, (s + 1) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hi := congrArg Complex.im hm
    simp at hi
    exact him hi
  rcases chi.even_or_odd with heven | hodd
  · rw [show DirichletCharacter.gammaFactor chi = Complex.Gammaℝ by
      funext z
      exact heven.gammaFactor_def z]
    change DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s
    exact ((differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        ((Complex.differentiableAt_Gamma (s / 2) hpoleEven).comp s (by fun_prop))
  · rw [show DirichletCharacter.gammaFactor chi =
      fun z => Complex.Gammaℝ (z + 1) by
      funext z
      exact hodd.gammaFactor_def z]
    change DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + 1) / 2) *
        Complex.Gamma ((z + 1) / 2)) s
    exact (((differentiableAt_id.add_const 1).neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))).mul
        ((Complex.differentiableAt_Gamma ((s + 1) / 2) hpoleOdd).comp s
          (by fun_prop))

/-- At a nonreal point, literal L-nonvanishing implies completed-L
nonvanishing because the Gamma factor is finite and nonzero. -/
theorem completedLFunction_ne_zero_of_LFunction_ne_zero_of_im_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {s : ℂ}
    (him : s.im ≠ 0)
    (hL : DirichletCharacter.LFunction chi s ≠ 0) :
    DirichletCharacter.completedLFunction chi s ≠ 0 := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have heq := DirichletCharacter.LFunction_eq_completed_div_gammaFactor
    chi s (Or.inl hs0)
  intro hcompleted
  rw [hcompleted, zero_div] at heq
  exact hL heq

/-- Completed L is differentiable at every nonreal point. -/
theorem differentiableAt_completedLFunction_of_im_ne_zero
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) {s : ℂ}
    (him : s.im ≠ 0) :
    DifferentiableAt ℂ (DirichletCharacter.completedLFunction chi) s := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at him
    norm_num at him
  exact DirichletCharacter.differentiableAt_completedLFunction
    chi s (Or.inl hs0) (Or.inl hs1)

/-- Exact uncompleted reflection at a nonreal point.  No differentiability,
Gamma-pole, or exceptional-point premises remain. -/
theorem logDeriv_LFunction_reflection_of_nonreal
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (s : ℂ) (him : s.im ≠ 0)
    (hleftL : DirichletCharacter.LFunction chi (1 - s) ≠ 0)
    (hrightL : DirichletCharacter.LFunction chi⁻¹ s ≠ 0) :
    logDeriv (DirichletCharacter.LFunction chi) (1 - s) =
      -Complex.log (q : ℂ) -
        logDeriv (DirichletCharacter.LFunction chi⁻¹) s -
        logDeriv (DirichletCharacter.gammaFactor chi⁻¹) s -
        logDeriv (DirichletCharacter.gammaFactor chi) (1 - s) := by
  have himLeft : (1 - s).im ≠ 0 := by
    simp only [sub_im, one_im, zero_sub]
    exact neg_ne_zero.mpr him
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at him
    norm_num at him
  have hleft0 : 1 - s ≠ 0 := by
    intro hs
    have hi := congrArg Complex.im hs
    simp at hi
    exact him hi
  apply logDeriv_LFunction_reflection chi hprimitive s
    (Or.inl hleft0) (Or.inl hs0)
  · exact differentiableAt_completedLFunction_of_im_ne_zero chi himLeft
  · exact differentiableAt_completedLFunction_of_im_ne_zero chi⁻¹ him
  · exact differentiableAt_gammaFactor_of_im_ne_zero chi himLeft
  · exact differentiableAt_gammaFactor_of_im_ne_zero chi⁻¹ him
  · exact completedLFunction_ne_zero_of_LFunction_ne_zero_of_im_ne_zero
      chi himLeft hleftL
  · exact completedLFunction_ne_zero_of_LFunction_ne_zero_of_im_ne_zero
      chi⁻¹ him hrightL
  · exact gammaFactor_ne_zero_of_im_ne_zero chi himLeft
  · exact gammaFactor_ne_zero_of_im_ne_zero chi⁻¹ him

end
end KoukFunctionalEquationNonreal

#print axioms KoukFunctionalEquationNonreal.logDeriv_LFunction_reflection_of_nonreal
