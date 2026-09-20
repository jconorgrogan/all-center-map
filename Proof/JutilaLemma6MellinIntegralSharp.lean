import JutilaLemma6MellinIntegral

/-!
# Sharp conductor-height form of the Lemma-6 Gamma--L integral

The coarse staging bound replaced the height exponent by `1`.  Jutila's
parameter inequality (2.8) needs the actual exponent `1/2+1/560`.  This file
retains that exponent on `q(1+|t|)` while allowing one harmless factor
`1+|u|` inside the integrable Gamma envelope.
-/

namespace MAPJutilaLemma6MellinIntegralSharp

open Complex Real MeasureTheory
open MAPJutilaLemma6MellinIntegral
open MAPJutilaLemma6GammaKernel
open MAPJutilaP48ConvexityAdapter

noncomputable section

private theorem shifted_height_le_product (t u : ℝ) :
    1 + |t + u| ≤ (1 + |t|) * (1 + |u|) := by
  have htri : |t + u| ≤ |t| + |u| := abs_add_le t u
  nlinarith [abs_nonneg t, abs_nonneg u]

private theorem one_add_abs_mul_inv_sq_le (u : ℝ) :
    (1 + |u|) * (1 + u ^ 2)⁻¹ ^ 2 ≤
      2 * (1 + u ^ 2)⁻¹ := by
  let D : ℝ := 1 + u ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hu : |u| ≤ 1 + u ^ 2 := by
    nlinarith [sq_nonneg (|u| - 1 / 2), sq_abs u]
  have hnum : 1 + |u| ≤ 2 * D := by
    dsimp [D]
    nlinarith [hu, sq_nonneg u]
  calc
    (1 + |u|) * D⁻¹ ^ 2 ≤ (2 * D) * D⁻¹ ^ 2 :=
      mul_le_mul_of_nonneg_right hnum (sq_nonneg _)
    _ = 2 * D⁻¹ := by field_simp [hD.ne']

theorem conductor_height_rpow_le_sharp
    {q : ℕ} [NeZero q] (t u : ℝ) :
    Real.rpow ((q : ℝ) * (1 + |t + u|)) p48HeightExponent ≤
      Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
        (1 + |u|) := by
  have hq0 : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hq1 : (1 : ℝ) ≤ q := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht0 : 0 ≤ 1 + |t| := by positivity
  have hu1 : 1 ≤ 1 + |u| := by linarith [abs_nonneg u]
  have hheight := shifted_height_le_product t u
  have hbase :
      (q : ℝ) * (1 + |t + u|) ≤
        ((q : ℝ) * (1 + |t|)) * (1 + |u|) := by
    calc
      (q : ℝ) * (1 + |t + u|) ≤
          (q : ℝ) * ((1 + |t|) * (1 + |u|)) :=
        mul_le_mul_of_nonneg_left hheight hq0
      _ = ((q : ℝ) * (1 + |t|)) * (1 + |u|) := by ring
  have hrpowBase := Real.rpow_le_rpow
    (mul_nonneg hq0 (by positivity)) hbase p48HeightExponent_nonneg
  have huPow : Real.rpow (1 + |u|) p48HeightExponent ≤ 1 + |u| := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hu1 p48HeightExponent_le_one
  calc
    Real.rpow ((q : ℝ) * (1 + |t + u|)) p48HeightExponent ≤
        Real.rpow (((q : ℝ) * (1 + |t|)) * (1 + |u|))
          p48HeightExponent := hrpowBase
    _ = Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
        Real.rpow (1 + |u|) p48HeightExponent :=
      Real.mul_rpow (mul_nonneg hq0 ht0) (by positivity)
    _ ≤ Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
        (1 + |u|) :=
      mul_le_mul_of_nonneg_left huPow
        (Real.rpow_nonneg (mul_nonneg hq0 ht0) _)

theorem lemmaSixGammaLNorm_le_cauchy_sharp
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t u : ℝ) :
    lemmaSixGammaLNorm chi beta t u ≤
      (2 * lemmaSixGammaSqConstant omega * p48ConvexityConstant *
        Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) *
          (1 + u ^ 2)⁻¹ := by
  have hGamma := norm_Gamma_neg_beta_vertical_le_inv_sq
    homega hbetaLow hbetaHigh (t := u)
  have hLraw := primitive_norm_LFunction_le_p48 chi hprim hchi
    (sigma := 0) (u := t + u) (by norm_num) (by norm_num)
  have hheight := conductor_height_rpow_le_sharp (q := q) t u
  have hL :
      ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ ≤
        p48ConvexityConstant *
          (Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
            (1 + |u|)) := by
    calc
      ‖DirichletCharacter.LFunction chi (((t + u : ℝ) : ℂ) * I)‖ ≤
          p48ConvexityConstant *
            Real.rpow ((q : ℝ) * (1 + |t + u|)) p48HeightExponent := by
        simpa [p48HeightExponent] using hLraw
      _ ≤ p48ConvexityConstant *
          (Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
            (1 + |u|)) :=
        mul_le_mul_of_nonneg_left hheight p48ConvexityConstant_pos.le
  have hproduct : lemmaSixGammaLNorm chi beta t u ≤
      (lemmaSixGammaSqConstant omega * (1 + u ^ 2)⁻¹ ^ 2) *
        (p48ConvexityConstant *
          (Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
            (1 + |u|))) := by
    unfold lemmaSixGammaLNorm
    exact mul_le_mul hGamma hL (norm_nonneg _)
      (mul_nonneg (lemmaSixGammaSqConstant_pos homega).le (sq_nonneg _))
  have hkernel := one_add_abs_mul_inv_sq_le u
  calc
    lemmaSixGammaLNorm chi beta t u ≤
        (lemmaSixGammaSqConstant omega * (1 + u ^ 2)⁻¹ ^ 2) *
          (p48ConvexityConstant *
            (Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent *
              (1 + |u|))) := hproduct
    _ = (lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) *
        ((1 + |u|) * (1 + u ^ 2)⁻¹ ^ 2) := by ring
    _ ≤ (lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) *
        (2 * (1 + u ^ 2)⁻¹) :=
      mul_le_mul_of_nonneg_left hkernel (by
        exact mul_nonneg
          (mul_nonneg (lemmaSixGammaSqConstant_pos homega).le
            p48ConvexityConstant_pos.le)
          (Real.rpow_nonneg (by positivity) _))
    _ = (2 * lemmaSixGammaSqConstant omega * p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent) *
        (1 + u ^ 2)⁻¹ := by ring

theorem integral_lemmaSixGammaLNorm_le_sharp
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {beta omega : ℝ} (homega : 0 < omega)
    (hbetaLow : 4 / 5 ≤ beta) (hbetaHigh : beta ≤ 1 - omega)
    (t : ℝ) :
    (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
      2 * Real.pi * lemmaSixGammaSqConstant omega *
        p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent := by
  let K : ℝ := 2 * lemmaSixGammaSqConstant omega *
    p48ConvexityConstant *
      Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent
  have hmajor : Integrable (fun u : ℝ => K * (1 + u ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hmono :
      (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
        ∫ u : ℝ, K * (1 + u ^ 2)⁻¹ :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => by
        unfold lemmaSixGammaLNorm
        positivity)
      hmajor
      (Filter.Eventually.of_forall fun u => by
        simpa only [K] using lemmaSixGammaLNorm_le_cauchy_sharp
          chi hprim hchi homega hbetaLow hbetaHigh t u)
  calc
    (∫ u : ℝ, lemmaSixGammaLNorm chi beta t u) ≤
        ∫ u : ℝ, K * (1 + u ^ 2)⁻¹ := hmono
    _ = K * ∫ u : ℝ, (1 + u ^ 2)⁻¹ := by rw [integral_const_mul]
    _ = K * Real.pi := by rw [integral_univ_inv_one_add_sq]
    _ = 2 * Real.pi * lemmaSixGammaSqConstant omega *
        p48ConvexityConstant *
          Real.rpow ((q : ℝ) * (1 + |t|)) p48HeightExponent := by
      dsimp [K]
      ring

end

end MAPJutilaLemma6MellinIntegralSharp

#print axioms MAPJutilaLemma6MellinIntegralSharp.conductor_height_rpow_le_sharp
#print axioms MAPJutilaLemma6MellinIntegralSharp.integral_lemmaSixGammaLNorm_le_sharp
