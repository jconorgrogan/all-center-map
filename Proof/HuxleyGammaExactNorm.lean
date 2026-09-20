import HuxleyPrimitiveFunctionalEquation
import PrimitiveRootNumberNorm

/-!
# Exact Huxley multiplier norm on the reflected line

On Huxley's source line `u = 3/2 + it`, the two parity-dependent
archimedean quotients have the same exact norm.  The proof uses the
`Gammaℝ(s+2)` recurrence and conjugation, so no Stirling estimate is needed.
-/

namespace MAPHuxleyGammaExactNorm

open Complex DirichletCharacter

noncomputable section

variable {q : ℕ} [NeZero q]

/-- Huxley's reflected integration line. -/
def sourceLine (t : ℝ) : ℂ := (3 / 2 : ℂ) + (t : ℂ) * I

/-- `Gammaℝ` commutes with conjugation at the level of norms. -/
theorem norm_GammaR_conj (s : ℂ) :
    ‖Complex.Gammaℝ (starRingEnd ℂ s)‖ = ‖Complex.Gammaℝ s‖ := by
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
  have harg : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by
    rw [map_div₀]
    simp only [map_ofNat]
  rw [harg, Complex.Gamma_conj, RCLike.norm_conj]
  congr 1
  simp

private theorem norm_neg_half_add_mul_I (t : ℝ) :
    ‖(-1 / 2 : ℂ) + (t : ℂ) * I‖ =
      Real.sqrt (t ^ 2 + 1 / 4) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num
  congr 1
  ring

private theorem norm_half_add_mul_I (t : ℝ) :
    ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ =
      Real.sqrt (t ^ 2 + 1 / 4) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  norm_num
  congr 1
  ring

private theorem conj_one_sub_sourceLine (t : ℝ) :
    starRingEnd ℂ (1 - sourceLine t) =
      (-1 / 2 : ℂ) + (t : ℂ) * I := by
  simp only [sourceLine, map_sub, map_one, map_add, map_div₀, map_ofNat,
    map_mul, conj_ofReal, conj_I]
  ring

private theorem conj_two_sub_sourceLine (t : ℝ) :
    starRingEnd ℂ (2 - sourceLine t) =
      (1 / 2 : ℂ) + (t : ℂ) * I := by
  simp only [sourceLine, map_sub, map_ofNat, map_add, map_div₀,
    map_mul, conj_ofReal, conj_I]
  ring

private theorem norm_conj_one_sub_sourceLine (t : ℝ) :
    ‖starRingEnd ℂ (1 - sourceLine t)‖ =
      Real.sqrt (t ^ 2 + 1 / 4) := by
  rw [conj_one_sub_sourceLine, norm_neg_half_add_mul_I]

private theorem norm_conj_two_sub_sourceLine (t : ℝ) :
    ‖starRingEnd ℂ (2 - sourceLine t)‖ =
      Real.sqrt (t ^ 2 + 1 / 4) := by
  rw [conj_two_sub_sourceLine, norm_half_add_mul_I]

private theorem GammaR_one_sub_sourceLine_ne_zero (t : ℝ) :
    Complex.Gammaℝ (1 - sourceLine t) ≠ 0 := by
  have hd : 1 - sourceLine t ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [sourceLine] at hre
  have hpos : Complex.Gammaℝ ((1 - sourceLine t) + 2) ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    norm_num [sourceLine]
  intro hzero
  apply hpos
  rw [Complex.Gammaℝ_add_two hd, hzero]
  norm_num

private theorem GammaR_two_sub_sourceLine_ne_zero (t : ℝ) :
    Complex.Gammaℝ (2 - sourceLine t) ≠ 0 := by
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  norm_num [sourceLine]

/-- Exact even-parity archimedean quotient on `Re u = 3/2`. -/
theorem even_gammaR_quotient_norm (t : ℝ) :
    ‖Complex.Gammaℝ (sourceLine t) /
        Complex.Gammaℝ (1 - sourceLine t)‖ =
      Real.sqrt (t ^ 2 + 1 / 4) / (2 * Real.pi) := by
  let z := starRingEnd ℂ (1 - sourceLine t)
  have hzval : z = (-1 / 2 : ℂ) + (t : ℂ) * I := by
    exact conj_one_sub_sourceLine t
  have hz : z ≠ 0 := by
    rw [hzval]
    intro hz0
    have hre := congrArg Complex.re hz0
    norm_num at hre
  have hu : sourceLine t = z + 2 := by
    rw [hzval]
    unfold sourceLine
    ring
  have hden := GammaR_one_sub_sourceLine_ne_zero t
  have hdenNorm : ‖Complex.Gammaℝ (1 - sourceLine t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hden
  rw [show Complex.Gammaℝ (sourceLine t) = Complex.Gammaℝ (z + 2) by rw [hu]]
  rw [Complex.Gammaℝ_add_two hz]
  simp only [norm_div, norm_mul]
  rw [norm_GammaR_conj, norm_conj_one_sub_sourceLine]
  norm_num only [Complex.norm_ofNat, Complex.norm_real, Real.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le]
  field_simp [hdenNorm, Real.pi_ne_zero]

/-- Exact odd-parity archimedean quotient on `Re u = 3/2`. -/
theorem odd_gammaR_quotient_norm (t : ℝ) :
    ‖Complex.Gammaℝ (sourceLine t + 1) /
        Complex.Gammaℝ (2 - sourceLine t)‖ =
      Real.sqrt (t ^ 2 + 1 / 4) / (2 * Real.pi) := by
  let z := starRingEnd ℂ (2 - sourceLine t)
  have hzval : z = (1 / 2 : ℂ) + (t : ℂ) * I := by
    exact conj_two_sub_sourceLine t
  have hz : z ≠ 0 := by
    rw [hzval]
    intro hz0
    have hre := congrArg Complex.re hz0
    norm_num at hre
  have hu : sourceLine t + 1 = z + 2 := by
    rw [hzval]
    unfold sourceLine
    ring
  have hden := GammaR_two_sub_sourceLine_ne_zero t
  have hdenNorm : ‖Complex.Gammaℝ (2 - sourceLine t)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hden
  rw [show Complex.Gammaℝ (sourceLine t + 1) = Complex.Gammaℝ (z + 2) by rw [hu]]
  rw [Complex.Gammaℝ_add_two hz]
  simp only [norm_div, norm_mul]
  rw [norm_GammaR_conj, norm_conj_two_sub_sourceLine]
  norm_num only [Complex.norm_ofNat, Complex.norm_real, Real.norm_ofNat,
    Complex.norm_of_nonneg Real.pi_pos.le]
  field_simp [hdenNorm, Real.pi_ne_zero]


/-- Inversion preserves even parity for complex Dirichlet characters. -/
private theorem inv_even {χ : DirichletCharacter ℂ q} (hχ : χ.Even) : χ⁻¹.Even := by
  simpa only [DirichletCharacter.Even, MulChar.inv_apply_eq_inv', inv_one] using
    congrArg (fun z : ℂ => z⁻¹) hχ

/-- Inversion preserves odd parity for complex Dirichlet characters. -/
private theorem inv_odd {χ : DirichletCharacter ℂ q} (hχ : χ.Odd) : χ⁻¹.Odd := by
  simpa only [DirichletCharacter.Odd, MulChar.inv_apply_eq_inv', inv_neg,
    inv_one] using congrArg (fun z : ℂ => z⁻¹) hχ

/-- The parity-dependent Dirichlet gamma quotient has the same exact norm in
both parity cases on Huxley's reflected line. -/
theorem gammaFactor_quotient_norm_sourceLine
    (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖χ⁻¹.gammaFactor (sourceLine t) /
        χ.gammaFactor (1 - sourceLine t)‖ =
      Real.sqrt (t ^ 2 + 1 / 4) / (2 * Real.pi) := by
  rcases χ.even_or_odd with hχ | hχ
  · have hinv := inv_even hχ
    rw [hinv.gammaFactor_def, hχ.gammaFactor_def]
    exact even_gammaR_quotient_norm t
  · have hinv := inv_odd hχ
    rw [hinv.gammaFactor_def, hχ.gammaFactor_def]
    rw [show 1 - sourceLine t + 1 = 2 - sourceLine t by ring]
    exact odd_gammaR_quotient_norm t

/-- Exact norm of the entire conductor/root-number/gamma multiplier in the
ordinary primitive functional equation on `u = 3/2 + it`.  This is the exact
specialization behind Huxley (1973), equation (3.14). -/
theorem huxleyFactor_norm_sourceLine
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ) :
    ‖(q : ℂ) ^ (sourceLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (sourceLine t) /
        χ.gammaFactor (1 - sourceLine t)‖ =
      (q : ℝ) * Real.sqrt (t ^ 2 + 1 / 4) / (2 * Real.pi) := by
  rw [show (q : ℂ) ^ (sourceLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (sourceLine t) /
          χ.gammaFactor (1 - sourceLine t) =
        ((q : ℂ) ^ (sourceLine t - 1 / 2) * χ.rootNumber) *
          (χ⁻¹.gammaFactor (sourceLine t) /
            χ.gammaFactor (1 - sourceLine t)) by ring]
  rw [norm_mul]
  have hconductor :
      ‖(q : ℂ) ^ (sourceLine t - 1 / 2) * χ.rootNumber‖ = (q : ℝ) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (NeZero.pos q),
      FixedCharacterPrimitiveRootNumber.primitive_rootNumber_norm_eq_one χ hprim]
    have hre : (sourceLine t - 1 / 2).re = 1 := by
      norm_num [sourceLine]
    rw [hre, Real.rpow_one, mul_one]
  rw [hconductor, gammaFactor_quotient_norm_sourceLine]
  ring

/-- The linear form of the source-line estimate used by the reflection
argument.  It is an immediate deterministic corollary of the exact norm. -/
theorem huxleyFactor_norm_sourceLine_le
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (t : ℝ) :
    ‖(q : ℂ) ^ (sourceLine t - 1 / 2) * χ.rootNumber *
          χ⁻¹.gammaFactor (sourceLine t) /
        χ.gammaFactor (1 - sourceLine t)‖ ≤
      (q : ℝ) * (|t| + 1 / 2) / (2 * Real.pi) := by
  rw [huxleyFactor_norm_sourceLine χ hprim t]
  have hsqrt : Real.sqrt (t ^ 2 + 1 / 4) ≤ |t| + 1 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · nlinarith [sq_abs t, abs_nonneg t]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsqrt (by positivity)) (by positivity)

end

end MAPHuxleyGammaExactNorm

#print axioms MAPHuxleyGammaExactNorm.norm_GammaR_conj
#print axioms MAPHuxleyGammaExactNorm.even_gammaR_quotient_norm
#print axioms MAPHuxleyGammaExactNorm.odd_gammaR_quotient_norm
#print axioms MAPHuxleyGammaExactNorm.gammaFactor_quotient_norm_sourceLine
#print axioms MAPHuxleyGammaExactNorm.huxleyFactor_norm_sourceLine
#print axioms MAPHuxleyGammaExactNorm.huxleyFactor_norm_sourceLine_le
