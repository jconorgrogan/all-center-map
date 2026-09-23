import JutilaLemma6GammaKernel
import JutilaP48ConvexityAdapter

/-!
# The Gamma--L part of Jutila's Lemma-6 Mellin error

The fourth-order Gamma envelope absorbs the explicit p.48 convexity growth.
This file proves a complete integral bound on the literal shifted ordinate
`t+u`.  What remains in the Mellin unit-error estimate is the finite
pseudocharacter mollifier factor and the source parameter inequality.
-/

namespace MAPJutilaLemma6MellinIntegral

open Complex Real MeasureTheory
open MAPJutilaCollarA5Budget MAPJutilaP48ConvexityAdapter
open MAPJutilaLemma6GammaKernel

noncomputable section

def p48HeightExponent : ℝ := 1 / 2 + detectorLogBudget

theorem p48HeightExponent_nonneg : 0 ≤ p48HeightExponent := by
  norm_num [p48HeightExponent, detectorLogBudget]

theorem p48HeightExponent_le_one : p48HeightExponent ≤ 1 := by
  norm_num [p48HeightExponent, detectorLogBudget]

def lemmaSixGammaLNorm {q : ℕ} [NeZero q]
    (chi : DirichletCharacter ℂ q) (beta t u : ℝ) : ℝ :=
  ‖Complex.Gamma ((-beta : ℝ) + (u : ℂ) * I)‖ *
    ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖

private theorem shifted_height_le_product (t u : ℝ) :
    1 + |t + u| ≤ (1 + |t|) * (1 + |u|) := by
  have htri : |t + u| ≤ |t| + |u| := abs_add_le t u
  nlinarith [abs_nonneg t, abs_nonneg u]

private theorem one_add_abs_mul_inv_sq_le (u : ℝ) :
    (1 + |u|) * (1 + u ^ 2)⁻¹ ^ 2 ≤
      2 * (1 + u ^ 2)⁻¹ := by
  let D : ℝ := 1 + u ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have habsSq : |u| ^ 2 = u ^ 2 := sq_abs u
  have hu : |u| ≤ 1 + u ^ 2 := by
    nlinarith [sq_nonneg (|u| - 1 / 2)]
  have hnum : 1 + |u| ≤ 2 * D := by
    dsimp [D]
    nlinarith [hu, sq_nonneg u]
  calc
    (1 + |u|) * D⁻¹ ^ 2 ≤ (2 * D) * D⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 * D⁻¹ := by field_simp [hD.ne']

private theorem conductor_height_rpow_le
    {q : ℕ} [NeZero q] (t u : ℝ) :
    Real.rpow ((q : ℝ) * (1 + |t + u|)) p48HeightExponent ≤
      Real.rpow (q : ℝ) p48HeightExponent *
        ((1 + |t|) * (1 + |u|)) := by
  have hq : (1 : ℝ) ≤ q := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne q))
  have hleftOne : 1 ≤ 1 + |t + u| := by linarith [abs_nonneg (t + u)]
  have hrightOne : 1 ≤ (1 + |t|) * (1 + |u|) := by
    nlinarith [abs_nonneg t, abs_nonneg u,
      mul_nonneg (abs_nonneg t) (abs_nonneg u)]
  have hheight := shifted_height_le_product t u
  have hrpowHeight :
      Real.rpow (1 + |t + u|) p48HeightExponent ≤
        Real.rpow ((1 + |t|) * (1 + |u|)) p48HeightExponent :=
    Real.rpow_le_rpow (zero_le_one.trans hleftOne) hheight
      p48HeightExponent_nonneg
  have hrpowOne :
      Real.rpow ((1 + |t|) * (1 + |u|)) p48HeightExponent ≤
        (1 + |t|) * (1 + |u|) := by
    simpa only [Real.rpow_one] using!
      Real.rpow_le_rpow_of_exponent_le hrightOne
        p48HeightExponent_le_one
  calc
    Real.rpow ((q : ℝ) * (1 + |t + u|)) p48HeightExponent =
        Real.rpow (q : ℝ) p48HeightExponent *
          Real.rpow (1 + |t + u|) p48HeightExponent :=
      Real.mul_rpow (Nat.cast_nonneg q) (by positivity)
    _ ≤ Real.rpow (q : ℝ) p48HeightExponent *
          Real.rpow ((1 + |t|) * (1 + |u|)) p48HeightExponent :=
      mul_le_mul_of_nonneg_left hrpowHeight
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)
    _ ≤ Real.rpow (q : ℝ) p48HeightExponent *
          ((1 + |t|) * (1 + |u|)) :=
      mul_le_mul_of_nonneg_left hrpowOne
        (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Pointwise domination by the Cauchy kernel whose total mass is `pi`. -/
theorem lemmaSixGammaLNorm_le_cauchy
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t u : ℝ) :
    lemmaSixGammaLNorm chi beta t u ≤
      (2 * lemmaSixGammaSqConstant omega * p48ConvexityConstant *
        Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)) *
          (1 + u ^ 2)⁻¹ := by
  have hGamma := norm_Gamma_neg_beta_vertical_le_inv_sq
    homega hbetaLow hbetaHigh (t := u)
  have hLraw := primitive_norm_LFunction_le_p48 chi hprim hchi
    (sigma := 0) (u := t + u) (by norm_num) (by norm_num)
  have hL :
      ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ ≤
        p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
          ((1 + |t|) * (1 + |u|)) := by
    have hheight := conductor_height_rpow_le (q := q) t u
    calc
      ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ ≤
          p48ConvexityConstant *
            Real.rpow ((q : ℝ) * (1 + |t + u|))
              p48HeightExponent := by
        simpa [p48HeightExponent] using hLraw
      _ ≤ p48ConvexityConstant *
          (Real.rpow (q : ℝ) p48HeightExponent *
            ((1 + |t|) * (1 + |u|))) :=
        mul_le_mul_of_nonneg_left hheight p48ConvexityConstant_pos.le
      _ = p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
          ((1 + |t|) * (1 + |u|)) := by ring
  have hGamma0 : 0 ≤
      lemmaSixGammaSqConstant omega * (1 + u ^ 2)⁻¹ ^ 2 :=
    mul_nonneg (lemmaSixGammaSqConstant_pos homega).le (sq_nonneg _)
  have hL0 : 0 ≤
      p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
        ((1 + |t|) * (1 + |u|)) := by
    exact mul_nonneg
      (mul_nonneg p48ConvexityConstant_pos.le
        (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (mul_nonneg (by positivity) (by positivity))
  have hproduct : lemmaSixGammaLNorm chi beta t u ≤
      (lemmaSixGammaSqConstant omega * (1 + u ^ 2)⁻¹ ^ 2) *
        (p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
          ((1 + |t|) * (1 + |u|))) := by
    unfold lemmaSixGammaLNorm
    exact mul_le_mul hGamma hL (norm_nonneg _) hGamma0
  have hkernel := one_add_abs_mul_inv_sq_le u
  calc
    lemmaSixGammaLNorm chi beta t u ≤
        (lemmaSixGammaSqConstant omega * (1 + u ^ 2)⁻¹ ^ 2) *
          (p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
            ((1 + |t|) * (1 + |u|))) := hproduct
    _ = (lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)) *
        ((1 + |u|) * (1 + u ^ 2)⁻¹ ^ 2) := by ring
    _ ≤ (lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)) *
        (2 * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hkernel (by
        exact mul_nonneg
          (mul_nonneg
            (mul_nonneg (lemmaSixGammaSqConstant_pos homega).le
              p48ConvexityConstant_pos.le)
            (Real.rpow_nonneg (Nat.cast_nonneg q) _))
          (by positivity))
    _ = (2 * lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)) *
        (1 + u ^ 2)⁻¹ := by ring

/-- Complete integral bound for the Gamma--L part of (2.11). -/
theorem integral_lemmaSixGammaLNorm_le
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t : ℝ) :
    (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
      2 * Real.pi * lemmaSixGammaSqConstant omega *
        p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
          (1 + |t|) := by
  let K : ℝ := 2 * lemmaSixGammaSqConstant omega *
    p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent * (1 + |t|)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity)
            (lemmaSixGammaSqConstant_pos homega).le)
          p48ConvexityConstant_pos.le)
        (Real.rpow_nonneg (Nat.cast_nonneg q) _))
      (by positivity)
  have hmajor : Integrable (fun u : ℝ => K * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmono :
      (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
        ∫ u : ℝ, K * (1 + u ^ 2)⁻¹ := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun u =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hmajor
    (Filter.Eventually.of_forall fun u => by
      simpa only [K] using lemmaSixGammaLNorm_le_cauchy
        chi hprim hchi homega hbetaLow hbetaHigh t u)
  calc
    (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
        ∫ u : ℝ, K * (1 + u ^ 2)⁻¹ := hmono
    _ = K * ∫ u : ℝ, (1 + u ^ 2)⁻¹ := by
      rw [integral_const_mul]
    _ = K * Real.pi := by rw [integral_univ_inv_one_add_sq]
    _ = 2 * Real.pi * lemmaSixGammaSqConstant omega *
        p48ConvexityConstant * Real.rpow (q : ℝ) p48HeightExponent *
          (1 + |t|) := by
      dsimp [K]
      ring

end

end MAPJutilaLemma6MellinIntegral

#print axioms MAPJutilaLemma6MellinIntegral.integral_lemmaSixGammaLNorm_le
