import GuthMaynardLemma295MellinAllLines

/-!
# Arbitrary polynomial Mellin decay for Lemma 29.5

The deep-left functional-equation multiplier has degree growing with the
chosen contour depth.  Thus the fixed quadratic Mellin envelope is not enough
for its infinite vertical tail.  This module packages the already-certified
Schwartz seminorm estimate at an arbitrary natural order.
-/

namespace GuthMaynardLemma295MellinPolynomialDecay

open Complex
open scoped FourierTransform SchwartzMap
open GuthMaynardLemma295CutoffAnalytic
open GuthMaynardLemma295MellinAllLines

noncomputable section

def sourceMellinDecayConstantAt (sigma : ℝ) (k : ℕ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0
      (𝓕 (sigmaLogLiftSchwartz sigma sourceHZero
        (sigmaLogLift_hasCompactSupport sigma
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
        (sigmaLogLift_contDiff sigma sourceHZero_contDiff)) : 𝓢(ℝ, ℂ)) +
    (2 * Real.pi) ^ k *
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (sigmaLogLiftSchwartz sigma sourceHZero
          (sigmaLogLift_hasCompactSupport sigma
            (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
          (sigmaLogLift_contDiff sigma sourceHZero_contDiff)) : 𝓢(ℝ, ℂ))

theorem sourceMellinDecayConstantAt_nonneg (sigma : ℝ) (k : ℕ) :
    0 ≤ sourceMellinDecayConstantAt sigma k := by
  unfold sourceMellinDecayConstantAt
  positivity

/-- Uniform all-height decay of any prescribed natural order. -/
theorem norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
    (sigma : ℝ) (k : ℕ) (t : ℝ) :
    ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
      sourceMellinDecayConstantAt sigma k / (1 + |t| ^ k) := by
  let psi : 𝓢(ℝ, ℂ) := sigmaLogLiftSchwartz sigma sourceHZero
    (sigmaLogLift_hasCompactSupport sigma
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (sigmaLogLift_contDiff sigma sourceHZero_contDiff)
  let S0 := SchwartzMap.seminorm ℂ 0 0 (𝓕 psi : 𝓢(ℝ, ℂ))
  let Sk := SchwartzMap.seminorm ℂ k 0 (𝓕 psi : 𝓢(ℝ, ℂ))
  have h0 := scaledPower_mul_norm_mellin_vertical_le_seminorm
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support
    sourceHZero_contDiff sigma 0 t
  have hk := scaledPower_mul_norm_mellin_vertical_le_seminorm
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support
    sourceHZero_contDiff sigma k t
  have h0' : ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤ S0 := by
    simpa only [pow_zero, one_mul, psi, S0] using h0
  change |t / (2 * Real.pi)| ^ k *
      ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤ Sk at hk
  have hscale :
      |t| ^ k * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
        (2 * Real.pi) ^ k * Sk := by
    calc
      |t| ^ k * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ =
          (2 * Real.pi) ^ k *
            (|t / (2 * Real.pi)| ^ k *
              ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), div_pow]
        field_simp [Real.pi_ne_zero]
      _ ≤ (2 * Real.pi) ^ k * Sk := by
        exact mul_le_mul_of_nonneg_left hk (pow_nonneg (by positivity) _)
  have hsum :
      (1 + |t| ^ k) *
          ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
        S0 + (2 * Real.pi) ^ k * Sk := by
    nlinarith [h0']
  have hden : 0 < 1 + |t| ^ k := by positivity
  apply (le_div_iff₀ hden).2
  simpa [sourceMellinDecayConstantAt, psi, S0, Sk, mul_comm] using hsum

end

end GuthMaynardLemma295MellinPolynomialDecay

#print axioms GuthMaynardLemma295MellinPolynomialDecay.norm_mellin_sourceHZero_vertical_le_inv_one_add_abs_pow
