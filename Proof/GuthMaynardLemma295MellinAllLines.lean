import GuthMaynardLemma295CutoffAnalytic

/-!
# Arbitrary-order Mellin decay on every fixed vertical line

The existing rapid-decay module treats `Re s = 1`.  Lemma 29.5 also uses a
deep-left line.  The same logarithmic change of variables works there after
including the real weight `exp (-sigma*u)`.  Compact support is unchanged.
-/

namespace GuthMaynardLemma295MellinAllLines

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

open GuthMaynardLemma295CutoffAnalytic

def sigmaLogLift (sigma : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-sigma * u) : ℂ) * f (Real.exp (-u))

theorem sigmaLogLift_contDiff
    (sigma : ℝ) {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (sigmaLogLift sigma f) := by
  have hlinear : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -sigma * u) :=
    contDiff_const.mul contDiff_id
  have hweightR : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => Real.exp (-sigma * u)) :=
    Real.contDiff_exp.comp hlinear
  have hweightC : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (Real.exp (-sigma * u) : ℂ)) := by
    simpa only [Function.comp_apply] using Complex.ofRealCLM.contDiff.comp hweightR
  have hexp : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_neg
  exact hweightC.mul (hf.comp hexp)

theorem sigmaLogLift_hasCompactSupport
    (sigma : ℝ) {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    HasCompactSupport (sigmaLogLift sigma f) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log b) (-Real.log a)))
  intro u hu
  unfold sigmaLogLift
  have hexpNot : Real.exp (-u) ∉ Set.Icc a b := by
    intro hx
    apply hu
    constructor
    · have h := Real.exp_le_exp.mp
        (show Real.exp (-u) ≤ Real.exp (Real.log b) by
          simpa [Real.exp_log hb] using hx.2)
      linarith
    · have h := Real.exp_le_exp.mp
        (show Real.exp (Real.log a) ≤ Real.exp (-u) by
          simpa [Real.exp_log ha] using hx.1)
      linarith
  rw [hsupport _ hexpNot, mul_zero]

def sigmaLogLiftSchwartz
    (sigma : ℝ) (f : ℝ → ℂ)
    (hcompact : HasCompactSupport (sigmaLogLift sigma f))
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (sigmaLogLift sigma f)) : 𝓢(ℝ, ℂ) :=
  hcompact.toSchwartzMap hsmooth

theorem mellin_vertical_eq_fourier_sigmaLogLift
    (sigma r : ℝ) (f : ℝ → ℂ) :
    mellin f ((sigma : ℂ) + r * Complex.I) =
      𝓕 (sigmaLogLift sigma f) (r / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun :
      (fun u : ℝ =>
        Real.exp (-((sigma : ℂ) + r * Complex.I).re * u) •
          f (Real.exp (-u))) = sigmaLogLift sigma f := by
    funext u
    unfold sigmaLogLift
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, neg_mul, Complex.real_smul]
  rw [hfun]
  simp

/-- A literal arbitrary-power estimate on the fixed line `Re s=sigma`. -/
theorem scaledPower_mul_norm_mellin_vertical_le_seminorm
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (sigma : ℝ) (k : ℕ) (r : ℝ) :
    |r / (2 * Real.pi)| ^ k *
        ‖mellin f ((sigma : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (sigmaLogLiftSchwartz sigma f
          (sigmaLogLift_hasCompactSupport sigma ha hb hsupport)
          (sigmaLogLift_contDiff sigma hf)) : 𝓢(ℝ, ℂ)) := by
  rw [mellin_vertical_eq_fourier_sigmaLogLift]
  let psi : 𝓢(ℝ, ℂ) := sigmaLogLiftSchwartz sigma f
    (sigmaLogLift_hasCompactSupport sigma ha hb hsupport)
    (sigmaLogLift_contDiff sigma hf)
  have hFourier :
      𝓕 (sigmaLogLift sigma f) (r / (2 * Real.pi)) =
        ((𝓕 psi : 𝓢(ℝ, ℂ)) (r / (2 * Real.pi))) := by
    exact congrFun (SchwartzMap.fourier_coe psi).symm _
  rw [hFourier]
  have h := SchwartzMap.le_seminorm ℂ k 0
    (𝓕 psi) (r / (2 * Real.pi))
  simpa only [psi, sigmaLogLiftSchwartz, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs] using h

/-- Division form, used directly on the deep-left contour away from its
single exceptional ordinate. -/
theorem norm_mellin_vertical_le_seminorm_div_scaledPower
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (sigma : ℝ) (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ‖mellin f ((sigma : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (sigmaLogLiftSchwartz sigma f
          (sigmaLogLift_hasCompactSupport sigma ha hb hsupport)
          (sigmaLogLift_contDiff sigma hf)) : 𝓢(ℝ, ℂ)) /
        |r / (2 * Real.pi)| ^ k := by
  apply (le_div_iff₀ (by positivity : 0 < |r / (2 * Real.pi)| ^ k)).2
  simpa [mul_comm] using
    (scaledPower_mul_norm_mellin_vertical_le_seminorm
      ha hb hsupport hf sigma k r)

def sourceMellinDecayConstant (sigma : ℝ) : ℝ :=
  SchwartzMap.seminorm ℂ 0 0
      (𝓕 (sigmaLogLiftSchwartz sigma sourceHZero
        (sigmaLogLift_hasCompactSupport sigma
          (by norm_num : (0 : ℝ) < 1 / 2)
          (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
        (sigmaLogLift_contDiff sigma sourceHZero_contDiff)) : 𝓢(ℝ, ℂ)) +
    (2 * Real.pi) ^ 2 *
      SchwartzMap.seminorm ℂ 2 0
        (𝓕 (sigmaLogLiftSchwartz sigma sourceHZero
          (sigmaLogLift_hasCompactSupport sigma
            (by norm_num : (0 : ℝ) < 1 / 2)
            (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
          (sigmaLogLift_contDiff sigma sourceHZero_contDiff)) : 𝓢(ℝ, ℂ))

theorem sourceMellinDecayConstant_nonneg (sigma : ℝ) :
    0 ≤ sourceMellinDecayConstant sigma := by
  unfold sourceMellinDecayConstant
  positivity

/-- The exact integrable `1/(1+t²)` envelope needed after the reflected
finite Dirichlet polynomial is moved to the critical line. -/
theorem norm_mellin_sourceHZero_vertical_le_inv_one_add_sq
    (sigma t : ℝ) :
    ‖mellin sourceHZero ((sigma : ℂ) + t * Complex.I)‖ ≤
      sourceMellinDecayConstant sigma / (1 + t ^ 2) := by
  let psi : 𝓢(ℝ, ℂ) := sigmaLogLiftSchwartz sigma sourceHZero
    (sigmaLogLift_hasCompactSupport sigma
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support)
    (sigmaLogLift_contDiff sigma sourceHZero_contDiff)
  let S0 := SchwartzMap.seminorm ℂ 0 0 (𝓕 psi : 𝓢(ℝ, ℂ))
  let S2 := SchwartzMap.seminorm ℂ 2 0 (𝓕 psi : 𝓢(ℝ, ℂ))
  have h0 := scaledPower_mul_norm_mellin_vertical_le_seminorm
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support
    sourceHZero_contDiff sigma 0 t
  have h2 := scaledPower_mul_norm_mellin_vertical_le_seminorm
    (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 5 / 2) sourceHZero_support
    sourceHZero_contDiff sigma 2 t
  have h0' : ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤ S0 := by
    simpa only [pow_zero, one_mul, psi, S0] using h0
  change |t / (2 * Real.pi)| ^ 2 *
      ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤ S2 at h2
  have hscale :
      t ^ 2 * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
        (2 * Real.pi) ^ 2 * S2 := by
    calc
      t ^ 2 * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ =
          (2 * Real.pi) ^ 2 *
            (|t / (2 * Real.pi)| ^ 2 *
              ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖) := by
        rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi),
          div_pow, sq_abs]
        field_simp [Real.pi_ne_zero]
      _ ≤ (2 * Real.pi) ^ 2 * S2 := by
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hsum :
      (1 + t ^ 2) * ‖mellin sourceHZero ((sigma : ℂ) + t * I)‖ ≤
        S0 + (2 * Real.pi) ^ 2 * S2 := by
    nlinarith [h0']
  have hden : 0 < 1 + t ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  simpa [sourceMellinDecayConstant, psi, S0, S2, mul_comm] using hsum

end
end GuthMaynardLemma295MellinAllLines

#print axioms GuthMaynardLemma295MellinAllLines.mellin_vertical_eq_fourier_sigmaLogLift
#print axioms GuthMaynardLemma295MellinAllLines.scaledPower_mul_norm_mellin_vertical_le_seminorm
#print axioms GuthMaynardLemma295MellinAllLines.norm_mellin_vertical_le_seminorm_div_scaledPower
#print axioms GuthMaynardLemma295MellinAllLines.norm_mellin_sourceHZero_vertical_le_inv_one_add_sq
