import KoukNegativeHorizontalLogDerivativeBound
import KoukExercise12TwoPointwisePrincipalFormula

/-!
# Principal negative-horizontal logarithmic derivative

The conductor-one primitive character is the only principal case in the
primitive-inducer family.  Reflection is still valid on a nonreal horizontal
line; on the positive reflected side we use the certified principal local
Blaschke estimate, retaining its explicit pole-at-one correction.
-/

namespace KoukPrincipalNegativeHorizontalLogDerivativeBound

set_option maxHeartbeats 800000

open Complex
open MAPKoukExercise12TwoPointwisePrincipalFormula
open KoukFunctionalEquationNonreal KoukGammaFactorGrowthBound
open WideDiskBlaschkeAssembly WideDiskLFunctionGrowth MAPLocalZeroWindow

noncomputable section

local instance : NeZero 1 := ⟨Nat.one_ne_zero⟩

private theorem gamma_even_clearance_of_im
    (s : ℂ) (him : (1 / 2 : ℝ) ≤ |s.im|) (m : ℕ) :
    (1 / 4 : ℝ) ≤ ‖s / 2 + (m : ℂ)‖ := by
  have him' : (1 / 4 : ℝ) ≤ |(s / 2 + (m : ℂ)).im| := by
    have heq : (s / 2 + (m : ℂ)).im = s.im / 2 := by norm_num
    rw [heq, abs_div]
    norm_num
    linarith
  exact him'.trans (Complex.abs_im_le_norm _)

private theorem gamma_odd_clearance_of_im
    (s : ℂ) (him : (1 / 2 : ℝ) ≤ |s.im|) (m : ℕ) :
    (1 / 4 : ℝ) ≤ ‖(s + 1) / 2 + (m : ℂ)‖ := by
  have him' : (1 / 4 : ℝ) ≤ |((s + 1) / 2 + (m : ℂ)).im| := by
    have heq : ((s + 1) / 2 + (m : ℂ)).im = s.im / 2 := by norm_num
    rw [heq, abs_div]
    norm_num
    linarith
  exact him'.trans (Complex.abs_im_le_norm _)

private theorem norm_inv_sub_one_le_two_of_half_le_abs_im
    (s : ℂ) (him : (1 / 2 : ℝ) ≤ |s.im|) :
    ‖(s - 1)⁻¹‖ ≤ 2 := by
  rw [norm_inv]
  have hden : (1 / 2 : ℝ) ≤ ‖s - 1‖ := by
    calc
      (1 / 2 : ℝ) ≤ |(s - 1).im| := by simpa using him
      _ ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
  have hdenPos : 0 < ‖s - 1‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hden
  calc
    ‖s - 1‖⁻¹ ≤ (1 / 2 : ℝ)⁻¹ :=
      (inv_le_inv₀ hdenPos (by norm_num)).2 hden
    _ = 2 := by norm_num

/-- Fixed-constant principal analogue of the negative-horizontal bound. -/
theorem norm_logDeriv_principal_negativeHorizontal_le_fixed
    (C : ℝ) (hC : 0 < C)
    (hDigamma : ∀ z : ℂ,
      (∀ m : ℕ, (1 / 4 : ℝ) ≤ ‖z + (m : ℂ)‖) →
      ‖Complex.digamma z‖ ≤ C * Real.log (‖z‖ + 2))
    {r t d : ℝ} (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0)
    (hrNeg : r < 0) (ht : (1 / 2 : ℝ) ≤ |t|) (hd : 0 < d)
    (hdistInv : ∀ rho ∈
        wideZeroSupport (1 : DirichletCharacter ℂ 1) (-t),
      d ≤ ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-t)) - rho)‖) :
    ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
        ((r : ℂ) + Complex.I * t)‖ ≤
      (2 + 20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 (-t))) +
        30300 * Real.log (arithmeticScale 1 (-t)) +
        (30300 * Real.log (arithmeticScale 1 (-t))) / d) + 4 +
      C * (Real.log
          (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-t))‖ + 3) +
        Real.log (‖((r : ℂ) + Complex.I * t)‖ + 3)) := by
  let chi : DirichletCharacter ℂ 1 := 1
  have hprimOne : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def,
      DirichletCharacter.conductor_one]
  let z : ℂ := (r : ℂ) + Complex.I * t
  let u : ℂ := ((1 - r : ℝ) : ℂ) + Complex.I * (-t)
  have hzu : 1 - u = z := by dsimp [z, u]; push_cast; ring
  have ht0 : t ≠ 0 := by
    intro htzero
    subst t
    norm_num at ht
  have huim : u.im ≠ 0 := by simpa [u] using neg_ne_zero.mpr ht0
  have huRe0 : 0 < u.re := by simp [u]; linarith [hr.2]
  have huRe4 : u.re < 4 := by simp [u]; linarith [hr.1]
  have huAbsIm : (1 / 2 : ℝ) ≤ |u.im| := by simpa [u] using ht
  have hzAbsIm : (1 / 2 : ℝ) ≤ |z.im| := by simpa [z] using ht
  have huNeOne : u ≠ 1 := by
    intro hu
    have hi := congrArg Complex.im hu
    simp [u] at hi
    exact ht0 hi
  have hInvLocalRaw := norm_logDeriv_principal_le_of_wide_clearance
    (t := -t) (r := 1 - r) (d := d)
      (by linarith [hr.2]) (by linarith [hr.1]) hd
      (by simpa [u] using huNeOne)
      (by simpa [u] using
        norm_inv_sub_one_le_two_of_half_le_abs_im u huAbsIm)
      (by simpa [u] using hdistInv)
  have hInvLocal :
      ‖logDeriv (DirichletCharacter.LFunction chi) u‖ ≤
        2 + 20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 (-t))) +
        30300 * Real.log (arithmeticScale 1 (-t)) +
        (30300 * Real.log (arithmeticScale 1 (-t))) / d := by
    simpa [chi, u] using hInvLocalRaw
  have hzL : DirichletCharacter.LFunction chi z ≠ 0 := by
    apply KoukNegativeHalfPlaneNonvanishing.LFunction_ne_zero_of_primitive_of_re_neg_of_gamma_ne_zero
      chi (by simpa [chi] using hprimOne)
    · simpa [z] using hrNeg
    · exact KoukNegativeHalfPlaneNonvanishing.gammaFactor_ne_zero_of_im_ne_zero
        chi (by simpa [z] using ht0)
  have huL : DirichletCharacter.LFunction chi u ≠ 0 :=
    PrimitiveTruncatedExplicitFormulaBridge.LFunction_ne_zero_of_one_lt_re
      chi (by simp [u]; linarith [hr.2])
  have hreflect := logDeriv_LFunction_reflection_of_nonreal
    chi (by simpa [chi] using hprimOne) u huim
      (by simpa [hzu] using hzL) (by simpa [chi] using huL)
  have hchiInv : chi⁻¹ = chi := by simp [chi]
  rw [hchiInv] at hreflect
  have hGammaU := norm_logDeriv_gammaFactor_le_fixed C hC hDigamma
    chi u (gamma_even_clearance_of_im u huAbsIm)
      (gamma_odd_clearance_of_im u huAbsIm)
  have hGammaZ := norm_logDeriv_gammaFactor_le_fixed C hC hDigamma
    chi z (gamma_even_clearance_of_im z hzAbsIm)
      (gamma_odd_clearance_of_im z hzAbsIm)
  have hLrewrite : logDeriv (DirichletCharacter.LFunction chi) z =
      logDeriv (DirichletCharacter.LFunction chi) (1 - u) := by rw [hzu]
  change ‖logDeriv (DirichletCharacter.LFunction chi) z‖ ≤ _
  rw [hLrewrite, hreflect]
  have htri :
      ‖-Complex.log (((1 : ℕ) : ℂ)) -
          logDeriv (DirichletCharacter.LFunction chi) u -
          logDeriv (DirichletCharacter.gammaFactor chi) u -
          logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ ≤
        ‖logDeriv (DirichletCharacter.LFunction chi) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ := by
    norm_num only [Nat.cast_one, Complex.log_one, neg_zero, zero_sub]
    calc
      ‖-logDeriv (DirichletCharacter.LFunction chi) u -
          logDeriv (DirichletCharacter.gammaFactor chi) u -
          logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ ≤
        ‖-logDeriv (DirichletCharacter.LFunction chi) u -
          logDeriv (DirichletCharacter.gammaFactor chi) u‖ +
          ‖logDeriv (DirichletCharacter.gammaFactor chi) (1 - u)‖ :=
        norm_sub_le _ _
      _ ≤ _ := by
        have h := norm_sub_le
          (-logDeriv (DirichletCharacter.LFunction chi) u)
          (logDeriv (DirichletCharacter.gammaFactor chi) u)
        rw [norm_neg] at h
        linarith
  calc
    _ ≤ _ := htri
    _ ≤ (2 + 20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 (-t))) +
        30300 * Real.log (arithmeticScale 1 (-t)) +
        (30300 * Real.log (arithmeticScale 1 (-t))) / d) +
        (2 + C * Real.log (‖u‖ + 3)) +
        (2 + C * Real.log (‖z‖ + 3)) := by
      rw [hzu]
      gcongr
    _ = _ := by ring

/-- Premise-free principal negative-horizontal bound. -/
theorem norm_logDeriv_principal_negativeHorizontal_le
    {r t d : ℝ} (hr : r ∈ Set.Icc (-(1 / 2 : ℝ)) 0)
    (hrNeg : r < 0) (ht : (1 / 2 : ℝ) ≤ |t|) (hd : 0 < d)
    (hdistInv : ∀ rho ∈
        wideZeroSupport (1 : DirichletCharacter ℂ 1) (-t),
      d ≤ ‖((((1 - r : ℝ) : ℂ) + Complex.I * (-t)) - rho)‖) :
    ∃ C : ℝ, 0 < C ∧
    ‖logDeriv (DirichletCharacter.LFunction
        (1 : DirichletCharacter ℂ 1))
        ((r : ℂ) + Complex.I * t)‖ ≤
      (2 + 20 * (Real.log 223948800 +
          6 * Real.log (arithmeticScale 1 (-t))) +
        30300 * Real.log (arithmeticScale 1 (-t)) +
        (30300 * Real.log (arithmeticScale 1 (-t))) / d) + 4 +
      C * (Real.log
          (‖(((1 - r : ℝ) : ℂ) + Complex.I * (-t))‖ + 3) +
        Real.log (‖((r : ℂ) + Complex.I * t)‖ + 3)) := by
  obtain ⟨C, hC, hbound⟩ :=
    KoukGaussDigammaSeries.awayFromPolesDigammaLogBound
  exact ⟨C, hC,
    norm_logDeriv_principal_negativeHorizontal_le_fixed
      C hC hbound hr hrNeg ht hd hdistInv⟩

end

end KoukPrincipalNegativeHorizontalLogDerivativeBound

#print axioms KoukPrincipalNegativeHorizontalLogDerivativeBound.norm_logDeriv_principal_negativeHorizontal_le
