import KoukTheorem113AmbientFormula

/-!
# Logarithmic derivative of the completed functional equation

This is the exact algebraic transport behind the negative-half-plane part of
Koukoulopoulos Lemma 11.4(b).  It differentiates Mathlib's primitive
functional equation without introducing a bound.  The remaining quantitative
source leaf is consequently the archimedean Gamma/digamma estimate, not the
functional-equation identity itself.
-/

namespace KoukCompletedLogDerivativeFunctionalEquation

open Complex Filter Topology

noncomputable section

private theorem natCast_ne_zero {q : ℕ} [NeZero q] : (q : ℂ) ≠ 0 := by
  exact_mod_cast (NeZero.ne q)

private theorem conductorPower_ne_zero {q : ℕ} [NeZero q] (s : ℂ) :
    (q : ℂ) ^ (s - 1 / 2) ≠ 0 :=
  Complex.cpow_ne_zero_iff.mpr (Or.inl (natCast_ne_zero (q := q)))

private theorem logDeriv_conductorPower {q : ℕ} [NeZero q] (s : ℂ) :
    logDeriv (fun z : ℂ => (q : ℂ) ^ (z - 1 / 2)) s =
      Complex.log (q : ℂ) := by
  have hexp : DifferentiableAt ℂ (fun z : ℂ => z - 1 / 2) s := by fun_prop
  rw [logDeriv_apply, Complex.deriv_const_cpow hexp]
  have hderiv : deriv (fun z : ℂ => z - 1 / 2) s = 1 := by
    simpa using (hasDerivAt_id s).sub_const (1 / 2 : ℂ) |>.deriv
  rw [hderiv, mul_one]
  exact mul_div_cancel_right₀ _ (conductorPower_ne_zero (q := q) s)

/-- Exact completed-L logarithmic-derivative functional equation.  The
nonvanishing hypotheses are precisely what is needed to take logarithmic
derivatives at the chosen point; in the contour application they follow from
edge avoidance and the Euler-product half-plane. -/
theorem logDeriv_completedLFunction_one_sub
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (s : ℂ)
    (hleftDiff : DifferentiableAt ℂ
      (DirichletCharacter.completedLFunction chi) (1 - s))
    (hrightDiff : DifferentiableAt ℂ
      (DirichletCharacter.completedLFunction chi⁻¹) s)
    (hleftNe : DirichletCharacter.completedLFunction chi (1 - s) ≠ 0)
    (hrightNe : DirichletCharacter.completedLFunction chi⁻¹ s ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction chi) (1 - s) =
      -Complex.log (q : ℂ) -
        logDeriv (DirichletCharacter.completedLFunction chi⁻¹) s := by
  classical
  let A : ℂ → ℂ := fun z => (q : ℂ) ^ (z - 1 / 2)
  let W : ℂ := DirichletCharacter.rootNumber chi
  let C : ℂ → ℂ := DirichletCharacter.completedLFunction chi⁻¹
  let g : ℂ → ℂ := fun z => 1 - z
  have hfun :
      (fun z : ℂ => DirichletCharacter.completedLFunction chi (1 - z)) =
        fun z : ℂ => A z * W * C z := by
    funext z
    simpa only [A, W, C] using hprimitive.completedLFunction_one_sub z
  have hAne : A s ≠ 0 := conductorPower_ne_zero (q := q) s
  have hWne : W ≠ 0 := by
    intro hW
    have hfe := hprimitive.completedLFunction_one_sub s
    rw [show DirichletCharacter.rootNumber chi = W from rfl, hW] at hfe
    simp only [mul_zero, zero_mul] at hfe
    exact hleftNe hfe
  have hAdiff : DifferentiableAt ℂ A s := by
    dsimp only [A]
    exact (differentiableAt_id.sub_const (1 / 2 : ℂ)).const_cpow
      (Or.inl (natCast_ne_zero (q := q)))
  have hAWne : A s * W ≠ 0 := mul_ne_zero hAne hWne
  have hAWdiff : DifferentiableAt ℂ (fun z => A z * W) s :=
    hAdiff.mul_const W
  have hrightLog :
      logDeriv (fun z => A z * W * C z) s =
        Complex.log (q : ℂ) + logDeriv C s := by
    change logDeriv ((fun z => A z * W) * C) s = _
    rw [logDeriv_mul s hAWne hrightNe hAWdiff hrightDiff]
    rw [logDeriv_mul_const s W hWne]
    rw [show logDeriv A s = Complex.log (q : ℂ) by
      simpa only [A] using logDeriv_conductorPower (q := q) s]
  have hgdiff : DifferentiableAt ℂ g s := by
    dsimp only [g]
    fun_prop
  have hgderiv : deriv g s = -1 := by
    dsimp only [g]
    simpa only [id_eq] using
      ((hasDerivAt_id s).const_sub (1 : ℂ)).deriv
  have hleftLog :
      logDeriv
          (fun z : ℂ => DirichletCharacter.completedLFunction chi (1 - z)) s =
        -logDeriv (DirichletCharacter.completedLFunction chi) (1 - s) := by
    change logDeriv
      (DirichletCharacter.completedLFunction chi ∘ g) s = _
    rw [logDeriv_comp hleftDiff hgdiff, hgderiv]
    ring
  have heq :
      logDeriv
          (fun z : ℂ => DirichletCharacter.completedLFunction chi (1 - z)) s =
        logDeriv (fun z => A z * W * C z) s := by
    rw [hfun]
  rw [hleftLog, hrightLog] at heq
  linear_combination -heq

/-- Local logarithmic derivative of `L = completedL / gammaFactor`.  The
only exceptional case in Mathlib's pointwise identity is `(q,s)=(1,0)`;
the disjunctive premise records exactly its exclusion. -/
theorem logDeriv_LFunction_eq_completed_sub_gamma
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hregular : s ≠ 0 ∨ q ≠ 1)
    (hcompletedDiff : DifferentiableAt ℂ
      (DirichletCharacter.completedLFunction chi) s)
    (hgammaDiff : DifferentiableAt ℂ
      (DirichletCharacter.gammaFactor chi) s)
    (hcompletedNe : DirichletCharacter.completedLFunction chi s ≠ 0)
    (hgammaNe : DirichletCharacter.gammaFactor chi s ≠ 0) :
    logDeriv (DirichletCharacter.LFunction chi) s =
      logDeriv (DirichletCharacter.completedLFunction chi) s -
        logDeriv (DirichletCharacter.gammaFactor chi) s := by
  have heq : DirichletCharacter.LFunction chi =ᶠ[𝓝 s]
      fun z => DirichletCharacter.completedLFunction chi z /
        DirichletCharacter.gammaFactor chi z := by
    rcases hregular with hs0 | hq1
    · filter_upwards [eventually_ne_nhds hs0] with z hz
      exact DirichletCharacter.LFunction_eq_completed_div_gammaFactor
        chi z (Or.inl hz)
    · exact Filter.Eventually.of_forall fun z =>
        DirichletCharacter.LFunction_eq_completed_div_gammaFactor
          chi z (Or.inr hq1)
  calc
    logDeriv (DirichletCharacter.LFunction chi) s =
        logDeriv (fun z => DirichletCharacter.completedLFunction chi z /
          DirichletCharacter.gammaFactor chi z) s := by
      rw [logDeriv_apply, logDeriv_apply, heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv (DirichletCharacter.completedLFunction chi) s -
        logDeriv (DirichletCharacter.gammaFactor chi) s :=
      logDeriv_div s hcompletedNe hgammaNe hcompletedDiff hgammaDiff

/-- Exact uncompleted reflection formula for logarithmic derivatives.  It
isolates the two archimedean logarithmic derivatives which require the
remaining quantitative digamma estimate. -/
theorem logDeriv_LFunction_reflection
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (s : ℂ)
    (hleftRegular : 1 - s ≠ 0 ∨ q ≠ 1)
    (hrightRegular : s ≠ 0 ∨ q ≠ 1)
    (hleftCompletedDiff : DifferentiableAt ℂ
      (DirichletCharacter.completedLFunction chi) (1 - s))
    (hrightCompletedDiff : DifferentiableAt ℂ
      (DirichletCharacter.completedLFunction chi⁻¹) s)
    (hleftGammaDiff : DifferentiableAt ℂ
      (DirichletCharacter.gammaFactor chi) (1 - s))
    (hrightGammaDiff : DifferentiableAt ℂ
      (DirichletCharacter.gammaFactor chi⁻¹) s)
    (hleftCompletedNe :
      DirichletCharacter.completedLFunction chi (1 - s) ≠ 0)
    (hrightCompletedNe :
      DirichletCharacter.completedLFunction chi⁻¹ s ≠ 0)
    (hleftGammaNe : DirichletCharacter.gammaFactor chi (1 - s) ≠ 0)
    (hrightGammaNe : DirichletCharacter.gammaFactor chi⁻¹ s ≠ 0) :
    logDeriv (DirichletCharacter.LFunction chi) (1 - s) =
      -Complex.log (q : ℂ) -
        logDeriv (DirichletCharacter.LFunction chi⁻¹) s -
        logDeriv (DirichletCharacter.gammaFactor chi⁻¹) s -
        logDeriv (DirichletCharacter.gammaFactor chi) (1 - s) := by
  have hcompleted := logDeriv_completedLFunction_one_sub
    chi hprimitive s hleftCompletedDiff hrightCompletedDiff
      hleftCompletedNe hrightCompletedNe
  have hleft := logDeriv_LFunction_eq_completed_sub_gamma
    chi (1 - s) hleftRegular hleftCompletedDiff hleftGammaDiff
      hleftCompletedNe hleftGammaNe
  have hright := logDeriv_LFunction_eq_completed_sub_gamma
    chi⁻¹ s hrightRegular hrightCompletedDiff hrightGammaDiff
      hrightCompletedNe hrightGammaNe
  linear_combination hleft + hcompleted + hright

end
end KoukCompletedLogDerivativeFunctionalEquation

#print axioms KoukCompletedLogDerivativeFunctionalEquation.logDeriv_completedLFunction_one_sub
