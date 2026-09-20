import GuthMaynardLemma295ThetaBounds
import GuthMaynardLemma295MellinAllLines

/-!
# The critical-line majorant in Lemma 29.5

After the finite reflected Dirichlet polynomial is moved to `Re s = 1/2`,
the zeta multiplier has norm one, the scale has norm `sqrt N`, and the
cutoff Mellin transform supplies the source kernel `1/(1+t^2)`.  This file
assembles those three facts pointwise with the literal reflected polynomial.
-/

namespace GuthMaynardLemma295CriticalMajorant

open Complex
open Set MeasureTheory
open GuthMaynardJutilaReflection2941
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295ThetaBounds
open GuthMaynardLemma295MellinAllLines

noncomputable section

/-- The critical-line expression after the harmless change `t -> -t`.
The polynomial orientation is chosen to be exactly the one in
`lemma295CentralMajorant`; changing all phases to their conjugates leaves
its norm unchanged. -/
def lemma295CriticalIntegrand (N M g t : ℝ) : ℂ :=
  sourceZetaTheta (((1 / 2 : ℝ) : ℂ) - (g + t) * I) *
    (N : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - t * I - g * I) *
    lemma295ReflectedPolynomial M (g + t) *
    mellin sourceHZero (((1 / 2 : ℝ) : ℂ) - t * I)

theorem norm_cpow_criticalScale_eq_sqrt
    {N : ℝ} (hN : 0 < N) (g t : ℝ) :
    ‖(N : ℂ) ^ (((1 / 2 : ℝ) : ℂ) - t * I - g * I)‖ =
      Real.sqrt N := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN]
  simp only [sub_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero]
  norm_num
  exact (Real.sqrt_eq_rpow N).symm

/-- Literal pointwise source majorant on the critical line. -/
theorem norm_lemma295CriticalIntegrand_le
    {N : ℝ} (hN : 0 < N) (M g t : ℝ) :
    ‖lemma295CriticalIntegrand N M g t‖ ≤
      sourceMellinDecayConstant (1 / 2) *
        (Real.sqrt N *
          (‖lemma295ReflectedPolynomial M (g + t)‖ / (1 + t ^ 2))) := by
  have htheta := norm_sourceZetaTheta_criticalLine_eq_one (-(g + t))
  have htheta' :
      ‖sourceZetaTheta (((1 / 2 : ℝ) : ℂ) - (g + t) * I)‖ = 1 := by
    have harg :
        (((1 / 2 : ℝ) : ℂ) - (g + t) * I) =
          ((1 / 2 : ℝ) : ℂ) + ((-(g + t) : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [harg]
    exact htheta
  have hscale := norm_cpow_criticalScale_eq_sqrt hN g t
  have hmellin := norm_mellin_sourceHZero_vertical_le_inv_one_add_sq
    (1 / 2) (-t)
  have hmellin' :
      ‖mellin sourceHZero (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        sourceMellinDecayConstant (1 / 2) / (1 + t ^ 2) := by
    simpa [sub_eq_add_neg] using hmellin
  have hpoly : 0 ≤ ‖lemma295ReflectedPolynomial M (g + t)‖ := norm_nonneg _
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hconst : 0 ≤ sourceMellinDecayConstant (1 / 2) :=
    sourceMellinDecayConstant_nonneg _
  unfold lemma295CriticalIntegrand
  repeat' rw [norm_mul]
  rw [htheta', one_mul, hscale]
  calc
    Real.sqrt N * ‖lemma295ReflectedPolynomial M (g + t)‖ *
          ‖mellin sourceHZero (((1 / 2 : ℝ) : ℂ) - t * I)‖ ≤
        Real.sqrt N * ‖lemma295ReflectedPolynomial M (g + t)‖ *
          (sourceMellinDecayConstant (1 / 2) / (1 + t ^ 2)) := by
      gcongr
    _ = sourceMellinDecayConstant (1 / 2) *
        (Real.sqrt N *
          (‖lemma295ReflectedPolynomial M (g + t)‖ / (1 + t ^ 2))) := by
      field_simp

/-- The whole truncated critical integral is bounded by the literal central
majorant from the statement of Lemma 29.5. -/
theorem norm_integral_lemma295CriticalIntegrand_le
    {N : ℝ} (hN : 0 < N) (M g R : ℝ) :
    ‖∫ t : ℝ in Set.Icc (-R) R, lemma295CriticalIntegrand N M g t‖ ≤
      sourceMellinDecayConstant (1 / 2) *
        lemma295CentralMajorant N M g R := by
  let C := sourceMellinDecayConstant (1 / 2)
  let major : ℝ → ℝ := fun t =>
    C * (Real.sqrt N *
      (‖lemma295ReflectedPolynomial M (g + t)‖ / (1 + t ^ 2)))
  have hpoly : Continuous (fun t : ℝ =>
      lemma295ReflectedPolynomial M (g + t)) := by
    unfold lemma295ReflectedPolynomial GuthMaynardHeathBrownMajorant.dirichletPhase
    fun_prop
  have hmajorContinuous : Continuous major := by
    dsimp [major, C]
    apply Continuous.const_mul
    apply Continuous.const_mul
    exact hpoly.norm.div
      (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)
  have hmajorInt : Integrable major (volume.restrict (Set.Icc (-R) R)) :=
    hmajorContinuous.continuousOn.integrableOn_compact isCompact_Icc
  calc
    ‖∫ t : ℝ in Set.Icc (-R) R, lemma295CriticalIntegrand N M g t‖ ≤
        ∫ t : ℝ in Set.Icc (-R) R, major t :=
      norm_integral_le_of_norm_le hmajorInt
        (Filter.Eventually.of_forall fun t => by
          exact norm_lemma295CriticalIntegrand_le hN M g t)
    _ = C * (Real.sqrt N *
        ∫ t : ℝ in Set.Icc (-R) R,
          ‖lemma295ReflectedPolynomial M (g + t)‖ / (1 + t ^ 2)) := by
      simp only [major]
      rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul]
    _ = sourceMellinDecayConstant (1 / 2) *
        lemma295CentralMajorant N M g R := by
      rfl

end
end GuthMaynardLemma295CriticalMajorant

#print axioms GuthMaynardLemma295CriticalMajorant.norm_cpow_criticalScale_eq_sqrt
#print axioms GuthMaynardLemma295CriticalMajorant.norm_lemma295CriticalIntegrand_le
#print axioms GuthMaynardLemma295CriticalMajorant.norm_integral_lemma295CriticalIntegrand_le
