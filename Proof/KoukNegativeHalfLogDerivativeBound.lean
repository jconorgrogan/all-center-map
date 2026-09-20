import KoukRightHalfPlaneLogDerivativeBound
import KoukGammaFactorGrowthBound
import KoukGaussDigammaSeries

/-!
# Reflected logarithmic derivative on the canonical negative half-line

The functional equation reflects `-1/2+it` to `3/2-it`, where the twisted
Euler series is uniformly bounded.  The four Gamma arguments stay a literal
distance `1/4` from every pole, including at `t=0`.
-/

namespace KoukNegativeHalfLogDerivativeBound

open Complex
open KoukNegativeHalfPlaneNonvanishing KoukFunctionalEquationNonreal
open KoukRightHalfPlaneLogDerivativeBound KoukGammaFactorGrowthBound
open PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

private theorem negativeHalf_even_clearance (t : ℝ) (m : ℕ) :
    (1 / 4 : ℝ) ≤
      ‖((((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t) / 2) + (m : ℂ)‖ := by
  let z : ℂ := (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t) / 2 + (m : ℂ)
  have hre : z.re = (m : ℝ) - 1 / 4 := by simp [z]; ring
  by_cases hm : m = 0
  · subst m
    have habs : |z.re| = 1 / 4 := by rw [hre]; norm_num
    rw [← habs]
    exact Complex.abs_re_le_norm z
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hrePos : (1 / 4 : ℝ) ≤ z.re := by
      rw [hre]
      have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      linarith
    exact hrePos.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))

private theorem negativeHalf_odd_clearance (t : ℝ) (m : ℕ) :
    (1 / 4 : ℝ) ≤
      ‖((((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t + 1) / 2) + (m : ℂ)‖ := by
  let z : ℂ :=
    (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t + 1) / 2 + (m : ℂ)
  have hre : z.re = (m : ℝ) + 1 / 4 := by simp [z]; ring
  have hrePos : (1 / 4 : ℝ) ≤ z.re := by
    rw [hre]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  exact hrePos.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))

private theorem reflectedThreeHalves_even_clearance (t : ℝ) (m : ℕ) :
    (1 / 4 : ℝ) ≤
      ‖((((3 / 2 : ℝ) : ℂ) - Complex.I * t) / 2) + (m : ℂ)‖ := by
  let z : ℂ := ((((3 / 2 : ℝ) : ℂ) - Complex.I * t) / 2) + (m : ℂ)
  have hre : z.re = (m : ℝ) + 3 / 4 := by simp [z]; ring
  have hrePos : (1 / 4 : ℝ) ≤ z.re := by
    rw [hre]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  exact hrePos.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))

private theorem reflectedThreeHalves_odd_clearance (t : ℝ) (m : ℕ) :
    (1 / 4 : ℝ) ≤
      ‖(((((3 / 2 : ℝ) : ℂ) - Complex.I * t) + 1) / 2) + (m : ℂ)‖ := by
  let z : ℂ :=
    (((((3 / 2 : ℝ) : ℂ) - Complex.I * t) + 1) / 2) + (m : ℂ)
  have hre : z.re = (m : ℝ) + 5 / 4 := by simp [z]; ring
  have hrePos : (1 / 4 : ℝ) ≤ z.re := by
    rw [hre]
    have hm0 : (0 : ℝ) ≤ m := by positivity
    linarith
  exact hrePos.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))

/-- Pointwise reflected bound on the canonical negative half-line.  The only
analytic premise is the away-from-poles digamma estimate. -/
theorem norm_logDeriv_LFunction_negativeHalf_le_fixed
    (C : ℝ) (hC : 0 < C)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (t : ℝ) (ht : t ≠ 0) :
    ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
        ‖Complex.log (q : ℂ)‖ + 24 +
          C * (Real.log (‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ + 3) +
            Real.log
              (‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ + 3)) := by
  let z : ℂ := ((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t
  let u : ℂ := ((3 / 2 : ℝ) : ℂ) - Complex.I * t
  have hzu : 1 - u = z := by dsimp [z, u]; push_cast; ring
  have huim : u.im ≠ 0 := by
    dsimp [u]
    simp only [sub_im, ofReal_im, mul_im, I_re, ofReal_re, I_im,
      zero_mul, mul_one, zero_sub]
    simpa using neg_ne_zero.mpr ht
  have hzL : DirichletCharacter.LFunction chi z ≠ 0 := by
    apply LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
      chi hprimitive
    · simp [z]
    · simpa [z, negativeHalfIntegerEdge, mul_comm] using
        gammaFactor_ne_zero_on_negativeHalfIntegerLine chi 0 t
  have huRe : (3 / 2 : ℝ) ≤ u.re := by simp [u]
  have huL : DirichletCharacter.LFunction chi⁻¹ u ≠ 0 :=
    LFunction_ne_zero_of_one_lt_re chi⁻¹ (by norm_num [u])
  have hreflect := logDeriv_LFunction_reflection_of_nonreal
    chi hprimitive u huim (by simpa only [hzu] using hzL) huL
  have hEuler := norm_logDeriv_LFunction_le_twenty chi⁻¹ huRe
  have hGammaU :=
    norm_logDeriv_gammaFactor_le_fixed C hC hDigamma chi⁻¹ u
      (reflectedThreeHalves_even_clearance t)
      (reflectedThreeHalves_odd_clearance t)
  have hGammaZ :=
    norm_logDeriv_gammaFactor_le_fixed C hC hDigamma chi z
      (negativeHalf_even_clearance t) (negativeHalf_odd_clearance t)
  change ‖logDeriv (DirichletCharacter.LFunction chi) z‖ ≤
    ‖Complex.log (q : ℂ)‖ + 24 +
      C * (Real.log (‖u‖ + 3) + Real.log (‖z‖ + 3))
  have hLrewrite : logDeriv (DirichletCharacter.LFunction chi) z =
      logDeriv (DirichletCharacter.LFunction chi) (1 - u) := by rw [hzu]
  rw [hLrewrite, hreflect]
  have htri :
      ‖-Complex.log (q : ℂ) -
          logDeriv (DirichletCharacter.LFunction chi⁻¹) u -
          logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u -
          logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ ≤
        ‖Complex.log (q : ℂ)‖ +
          ‖logDeriv (DirichletCharacter.LFunction chi⁻¹) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ := by
    calc
      ‖-Complex.log (q : ℂ) -
          logDeriv (DirichletCharacter.LFunction chi⁻¹) u -
          logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u -
          logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ ≤
        ‖-Complex.log (q : ℂ) -
          logDeriv (DirichletCharacter.LFunction chi⁻¹) u -
          logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ :=
        norm_sub_le _ _
      _ ≤ _ := by
        have h2 := norm_sub_le
          (-Complex.log (q : ℂ) -
            logDeriv (DirichletCharacter.LFunction chi⁻¹) u)
          (logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u)
        have h3 := norm_sub_le (-Complex.log (q : ℂ))
          (logDeriv (DirichletCharacter.LFunction chi⁻¹) u)
        rw [norm_neg] at h3
        nlinarith
  calc
    ‖-Complex.log (q : ℂ) -
        logDeriv (DirichletCharacter.LFunction chi⁻¹) u -
        logDeriv (DirichletCharacter.gammaFactor chi⁻¹) u -
        logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ ≤ _ := htri
    _ ≤ ‖Complex.log (q : ℂ)‖ + 20 +
        (2 + C * Real.log (‖u‖ + 3)) +
        (2 + C * Real.log (‖z‖ + 3)) := by
      rw [hzu]
      gcongr
    _ ≤ ‖Complex.log (q : ℂ)‖ + 24 +
        C * (Real.log (‖u‖ + 3) + Real.log (‖z‖ + 3)) := by
      have hlogu : 0 ≤ Real.log (‖u‖ + 3) :=
        Real.log_nonneg (by linarith [norm_nonneg u])
      have hlogz : 0 ≤ Real.log (‖z‖ + 3) :=
        Real.log_nonneg (by linarith [norm_nonneg z])
      nlinarith
    _ = _ := by rfl

/-- Existential interface obtained from the certified away-from-poles
digamma statement.  The witness is selected once and is uniform in `t`. -/
theorem norm_logDeriv_LFunction_negativeHalf_le_of_awayFromPoles
    (hDigamma : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, t ≠ 0 →
      ‖logDeriv (DirichletCharacter.LFunction chi)
        (((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
        ‖Complex.log (q : ℂ)‖ + 24 +
          C * (Real.log (‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ + 3) +
            Real.log
              (‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ + 3)) := by
  obtain ⟨C, hC, hbound⟩ := hDigamma
  exact ⟨C, hC, fun t ht =>
    norm_logDeriv_LFunction_negativeHalf_le_fixed
      C hC hbound chi hprimitive t ht⟩

/-- Uniform left-edge contour bound obtained by composing reflection with the
integrable endpoint-kernel geometry.  The digamma witness is chosen once and
is therefore uniform in the ordinate and character. -/
theorem norm_endpointVerticalLineIntegral_negativeHalf_le_fixed
    (C : ℝ) (hC : 0 < C) (hbound : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {x T : ℝ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) :
    ‖KoukTheorem113ExactFormula.endpointVerticalLineIntegral
        chi x (-(1 / 2 : ℝ)) T‖ ≤
      (6 * (‖Complex.log (q : ℂ)‖ + 24 +
        2 * C * Real.log (T + 5)) / Real.pi) *
          Real.log (T + 1) := by
  let M : ℝ := ‖Complex.log (q : ℂ)‖ + 24 +
    2 * C * Real.log (T + 5)
  have hscalePos : 0 < T + 5 := by linarith
  have hscaleLog : 0 ≤ Real.log (T + 5) :=
    Real.log_nonneg (by linarith)
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hleft :=
    KoukEndpointLeftVerticalBound.norm_endpointVerticalLineIntegral_negativeHalf_le_of_logDeriv
      chi hx hT hM
      (fun t _ht => by
        apply LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
          chi hprimitive
        · norm_num
        · simpa [negativeHalfIntegerEdge, mul_comm] using
            gammaFactor_ne_zero_on_negativeHalfIntegerLine chi 0 t)
      (fun t htIcc ht0 => by
        have hp := norm_logDeriv_LFunction_negativeHalf_le_fixed
          C hC hbound chi hprimitive t ht0
        have habs : |t| ≤ T := (abs_le).2 ⟨htIcc.1, htIcc.2⟩
        have huNorm :
            ‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ + 3 ≤ T + 5 := by
          have htri := norm_sub_le ((3 / 2 : ℝ) : ℂ) (Complex.I * t)
          have hIt : ‖Complex.I * (t : ℂ)‖ = |t| := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs]
          rw [hIt] at htri
          norm_num [Complex.norm_real, Real.norm_eq_abs] at htri
          have htri' :
              ‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ ≤
                3 / 2 + |t| := by simpa using htri
          linarith
        have hzNorm :
            ‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ + 3 ≤ T + 5 := by
          have htri := norm_add_le ((-(1 / 2 : ℝ)) : ℂ) (Complex.I * t)
          have hIt : ‖Complex.I * (t : ℂ)‖ = |t| := by
            rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
              Real.norm_eq_abs]
          rw [hIt] at htri
          norm_num [Complex.norm_real, Real.norm_eq_abs] at htri
          have htri' :
              ‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ ≤
                1 / 2 + |t| := by simpa using htri
          linarith
        have hlogu :
            Real.log (‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ + 3) ≤
              Real.log (T + 5) :=
          Real.strictMonoOn_log.monotoneOn
            (show 0 < ‖(((3 / 2 : ℝ) : ℂ) - Complex.I * t)‖ + 3 by
              positivity)
            hscalePos huNorm
        have hlogz :
            Real.log (‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ + 3) ≤
              Real.log (T + 5) :=
          Real.strictMonoOn_log.monotoneOn
            (show 0 < ‖(((-(1 / 2 : ℝ)) : ℂ) + Complex.I * t)‖ + 3 by
              positivity)
            hscalePos hzNorm
        dsimp only [M]
        nlinarith)
  simpa only [M] using hleft

theorem norm_endpointVerticalLineIntegral_negativeHalf_le_of_awayFromPoles
    (hDigamma : ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {x T : ℝ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ‖KoukTheorem113ExactFormula.endpointVerticalLineIntegral
          chi x (-(1 / 2 : ℝ)) T‖ ≤
        (6 * (‖Complex.log (q : ℂ)‖ + 24 +
          2 * C * Real.log (T + 5)) / Real.pi) *
            Real.log (T + 1) := by
  obtain ⟨C, hC, hbound⟩ := hDigamma
  exact ⟨C, hC,
    norm_endpointVerticalLineIntegral_negativeHalf_le_fixed
      C hC hbound chi hprimitive hx hT⟩

/-- Premise-free canonical left-edge bound. -/
theorem norm_endpointVerticalLineIntegral_negativeHalf_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) {x T : ℝ}
    (hx : 1 ≤ x) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ‖KoukTheorem113ExactFormula.endpointVerticalLineIntegral
          chi x (-(1 / 2 : ℝ)) T‖ ≤
        (6 * (‖Complex.log (q : ℂ)‖ + 24 +
          2 * C * Real.log (T + 5)) / Real.pi) *
            Real.log (T + 1) :=
  norm_endpointVerticalLineIntegral_negativeHalf_le_of_awayFromPoles
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
    chi hprimitive hx hT

end

end KoukNegativeHalfLogDerivativeBound

#print axioms KoukNegativeHalfLogDerivativeBound.norm_logDeriv_LFunction_negativeHalf_le_of_awayFromPoles
#print axioms KoukNegativeHalfLogDerivativeBound.norm_logDeriv_LFunction_negativeHalf_le_fixed
#print axioms KoukNegativeHalfLogDerivativeBound.norm_endpointVerticalLineIntegral_negativeHalf_le_of_awayFromPoles
#print axioms KoukNegativeHalfLogDerivativeBound.norm_endpointVerticalLineIntegral_negativeHalf_le
