import KoukNegativeHalfLogDerivativeBound
import FunctionalZeroTransport
import KoukExercise12TwoContourAperture
import KoukGaussDigammaSeries

/-!
# Reflected logarithmic derivative on the negative horizontal half-strip

For `-1/2 ≤ r ≤ 0`, reflection sends `r+it` to
`1-r-it`, inside the positive local-Blaschke region.  This module retains the
exact inverse-character wide-zero clearance required by that local estimate.
-/

namespace KoukNegativeHorizontalLogDerivativeBound

open Complex
open MAPKoukExercise12TwoContourAperture MAPFunctionalZeroTransport
open KoukFunctionalEquationNonreal KoukGammaFactorGrowthBound
open WideDiskBlaschkeAssembly MAPLocalZeroWindow

noncomputable section

private theorem gamma_even_clearance_of_im
    (s : ℂ) (him : (1 / 2 : ℝ) ≤ |s.im|) (m : ℕ) :
    (1 / 4 : ℝ) ≤ ‖s / 2 + (m : ℂ)‖ := by
  have him' : (1 / 4 : ℝ) ≤ |(s / 2 + (m : ℂ)).im| := by
    have heq : (s / 2 + (m : ℂ)).im = s.im / 2 := by
      norm_num
    rw [heq, abs_div]
    norm_num
    linarith
  exact him'.trans (Complex.abs_im_le_norm _)

private theorem gamma_odd_clearance_of_im
    (s : ℂ) (him : (1 / 2 : ℝ) ≤ |s.im|) (m : ℕ) :
    (1 / 4 : ℝ) ≤ ‖(s + 1) / 2 + (m : ℂ)‖ := by
  have him' : (1 / 4 : ℝ) ≤ |((s + 1) / 2 + (m : ℂ)).im| := by
    have heq : ((s + 1) / 2 + (m : ℂ)).im = s.im / 2 := by
      norm_num
    rw [heq, abs_div]
    norm_num
    linarith
  exact him'.trans (Complex.abs_im_le_norm _)

/-- Fixed-constant pointwise bound for the negative half of a horizontal
contour.  The exact inverse-character wide-zero clearance is left explicit. -/
theorem norm_logDeriv_LFunction_negativeHorizontal_le_fixed_of_nonzero
    (C : ℝ) (hC : 0 < C)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (hchi : chi ≠ 1)
    {r t d : ℝ} (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0)
    (ht : (1 / 2 : ℝ) ≤ |t|) (hd : 0 < d)
    (hdistInv : ∀ rho ∈ wideZeroSupport chi⁻¹ (-t),
      d ≤ ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-t)) - rho)‖)
    (hzL : DirichletCharacter.LFunction chi
      ((r : ℂ) + Complex.I * t) ≠ 0)
    (huL : DirichletCharacter.LFunction chi⁻¹
      (((1 - r : ℝ) : ℂ) + Complex.I * (-t)) ≠ 0) :
    ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.log (q : ℂ)‖ +
        (20 * (Real.log 21600 +
            2 * Real.log (arithmeticScale q (-t))) +
          5520 * Real.log (arithmeticScale q (-t)) +
          (5520 * Real.log (arithmeticScale q (-t))) / d) + 4 +
        C * (Real.log
            (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-t))‖ + 3) +
          Real.log (‖((r : ℂ) + Complex.I * t)‖ + 3)) := by
  let z : ℂ := (r : ℂ) + Complex.I * t
  let u : ℂ := ((1 - r : ℝ) : ℂ) + Complex.I * (-t)
  have hzu : 1 - u = z := by dsimp [z, u]; push_cast; ring
  have ht0 : t ≠ 0 := by
    intro htzero
    subst t
    norm_num at ht
  have huim : u.im ≠ 0 := by
    simpa [u] using neg_ne_zero.mpr ht0
  have huRe0 : 0 < u.re := by simp [u]; linarith [hr.2]
  have huRe4 : u.re < 4 := by simp [u]; linarith [hr.1]
  have hInvPrim := isPrimitive_inv hprimitive
  have hInvNe := inverse_ne_one hchi
  have hInvLocalRaw := norm_logDeriv_LFunction_le_of_wide_clearance
    chi⁻¹ hInvPrim hInvNe (t := -t) (r := 1 - r) (d := d)
      (by linarith [hr.2]) (by linarith [hr.1]) hd
      (fun rho hrho => by
        simpa only [Complex.ofReal_neg] using hdistInv rho hrho)
  have hInvLocal :
      ‖logDeriv (DirichletCharacter.LFunction chi⁻¹) u‖ ≤
        20 * (Real.log 21600 +
            2 * Real.log (arithmeticScale q (-t))) +
          5520 * Real.log (arithmeticScale q (-t)) +
          (5520 * Real.log (arithmeticScale q (-t))) / d := by
    simpa [u] using hInvLocalRaw
  have hreflect := logDeriv_LFunction_reflection_of_nonreal
    chi hprimitive u huim (by simpa only [hzu, z] using hzL)
      (by simpa [u] using huL)
  have huAbsIm : (1 / 2 : ℝ) ≤ |u.im| := by simpa [u] using ht
  have hzAbsIm : (1 / 2 : ℝ) ≤ |z.im| := by simpa [z] using ht
  have hGammaU := norm_logDeriv_gammaFactor_le_fixed C hC hDigamma
    chi⁻¹ u (gamma_even_clearance_of_im u huAbsIm)
      (gamma_odd_clearance_of_im u huAbsIm)
  have hGammaZ := norm_logDeriv_gammaFactor_le_fixed C hC hDigamma
    chi z (gamma_even_clearance_of_im z hzAbsIm)
      (gamma_odd_clearance_of_im z hzAbsIm)
  have hLrewrite : logDeriv (DirichletCharacter.LFunction chi) z =
      logDeriv (DirichletCharacter.LFunction chi) (1 - u) := by rw [hzu]
  change ‖logDeriv (DirichletCharacter.LFunction chi) z‖ ≤ _
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
      _ ≤ ‖-Complex.log (q : ℂ) -
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
    _ ≤ _ := htri
    _ ≤ ‖Complex.log (q : ℂ)‖ +
        (20 * (Real.log 21600 + 2 * Real.log (arithmeticScale q (-t))) +
          5520 * Real.log (arithmeticScale q (-t)) +
          (5520 * Real.log (arithmeticScale q (-t))) / d) +
        (2 + C * Real.log (‖u‖ + 3)) +
        (2 + C * Real.log (‖z‖ + 3)) := by
      rw [hzu]
      gcongr
    _ = _ := by ring

/-- Negative-half specialization, discharging both literal L-nonvanishing
premises from the two zero-free half-planes. -/
theorem norm_logDeriv_LFunction_negativeHorizontal_le_fixed
    (C : ℝ) (hC : 0 < C)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (hchi : chi ≠ 1)
    {r t d : ℝ} (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0)
    (hrNeg : r < 0)
    (ht : (1 / 2 : ℝ) ≤ |t|) (hd : 0 < d)
    (hdistInv : ∀ rho ∈ wideZeroSupport chi⁻¹ (-t),
      d ≤ ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-t)) - rho)‖) :
    ‖logDeriv (DirichletCharacter.LFunction chi)
        ((r : ℂ) + Complex.I * t)‖ ≤
      ‖Complex.log (q : ℂ)‖ +
        (20 * (Real.log 21600 +
            2 * Real.log (arithmeticScale q (-t))) +
          5520 * Real.log (arithmeticScale q (-t)) +
          (5520 * Real.log (arithmeticScale q (-t))) / d) + 4 +
        C * (Real.log
            (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-t))‖ + 3) +
          Real.log (‖((r : ℂ) + Complex.I * t)‖ + 3)) := by
  have ht0 : t ≠ 0 := by
    intro htzero
    subst t
    norm_num at ht
  have hzL : DirichletCharacter.LFunction chi
      ((r : ℂ) + Complex.I * t) ≠ 0 := by
    apply KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
      chi hprimitive
    · simpa using hrNeg
    · exact KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
        chi (by simpa using ht0)
  have huL : DirichletCharacter.LFunction chi⁻¹
      (((1 - r : ℝ) : ℂ) + Complex.I * (-t)) ≠ 0 :=
    PrimitiveTruncatedExplicitFormulaBridge.LFunction_ne_zero_of_one_lt_re
      chi⁻¹ (by simp; linarith [hrNeg])
  exact norm_logDeriv_LFunction_negativeHorizontal_le_fixed_of_nonzero
    C hC hDigamma chi hprimitive hchi hr ht hd hdistInv hzL huL

/-- Premise-free pointwise negative-horizontal bound, with one absolute
constant supplied by the certified Gauss digamma series. -/
theorem norm_logDeriv_LFunction_negativeHorizontal_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprimitive : chi.IsPrimitive) (hchi : chi ≠ 1)
    {r t d : ℝ} (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0)
    (hrNeg : r < 0)
    (ht : (1 / 2 : ℝ) ≤ |t|) (hd : 0 < d)
    (hdistInv : ∀ rho ∈ wideZeroSupport chi⁻¹ (-t),
      d ≤ ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-t)) - rho)‖) :
    ∃ C : ℝ, 0 < C ∧
      ‖logDeriv (DirichletCharacter.LFunction chi)
          ((r : ℂ) + Complex.I * t)‖ ≤
        ‖Complex.log (q : ℂ)‖ +
          (20 * (Real.log 21600 +
              2 * Real.log (arithmeticScale q (-t))) +
            5520 * Real.log (arithmeticScale q (-t)) +
            (5520 * Real.log (arithmeticScale q (-t))) / d) + 4 +
          C * (Real.log
              (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-t))‖ + 3) +
            Real.log (‖((r : ℂ) + Complex.I * t)‖ + 3)) := by
  obtain ⟨C, hC, hbound⟩ :=
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
  exact ⟨C, hC,
    norm_logDeriv_LFunction_negativeHorizontal_le_fixed
      C hC hbound chi hprimitive hchi hr hrNeg ht hd hdistInv⟩

end

end KoukNegativeHorizontalLogDerivativeBound

#print axioms KoukNegativeHorizontalLogDerivativeBound.norm_logDeriv_LFunction_negativeHorizontal_le_fixed
#print axioms KoukNegativeHorizontalLogDerivativeBound.norm_logDeriv_LFunction_negativeHorizontal_le
