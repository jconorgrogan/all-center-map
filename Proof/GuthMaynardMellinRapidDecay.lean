import GuthMaynardMellinTail
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Arbitrary-order decay of the Guth--Maynard cutoff Mellin transform

Mathlib's exact Mellin--Fourier identity turns the line `Re(s)=1` into the
Fourier transform of a logarithmically reparameterized cutoff.  A smooth
cutoff supported in a positive compact interval gives a Schwartz function,
so every Fourier seminorm yields one of the arbitrary-power estimates used
in Guth--Maynard Lemma 6.2.  This formalizes the source's repeated-IBP claim
without introducing it as an analytic assumption.
-/

namespace GuthMaynardMellinRapidDecay

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

def mellinLogLift (f : ℝ → ℂ) (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * f (Real.exp (-u))

theorem mellinLogLift_contDiff
    {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (mellinLogLift f) := by
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => -u) := contDiff_neg
  have hexpR : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp hneg
  have hexpC : ContDiff ℝ (⊤ : ℕ∞)
      (fun u : ℝ => (Real.exp (-u) : ℂ)) := by
    simpa only [Function.comp_apply] using
      Complex.ofRealCLM.contDiff.comp hexpR
  unfold mellinLogLift
  exact hexpC.mul (hf.comp hexpR)

theorem mellinLogLift_hasCompactSupport
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0) :
    HasCompactSupport (mellinLogLift f) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log b) (-Real.log a)))
  intro u hu
  unfold mellinLogLift
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

def mellinLogLiftSchwartz
    (f : ℝ → ℂ)
    (hcompact : HasCompactSupport (mellinLogLift f))
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) (mellinLogLift f)) :
    𝓢(ℝ, ℂ) :=
  hcompact.toSchwartzMap hsmooth

/-- Exact Mellin--Fourier conversion on `Re(s)=1`, including the `2π`
normalization. -/
theorem mellin_line_one_eq_fourier_logLift (f : ℝ → ℂ) (r : ℝ) :
    mellin f ((1 : ℂ) + r * Complex.I) =
      𝓕 (mellinLogLift f) (r / (2 * Real.pi)) := by
  rw [mellin_eq_fourier]
  have hfun :
      (fun u : ℝ =>
        Real.exp (-((1 : ℂ) + r * Complex.I).re * u) •
          f (Real.exp (-u))) = mellinLogLift f := by
    funext u
    unfold mellinLogLift
    simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero,
      ofReal_im, I_im, zero_mul, sub_zero, neg_mul]
    rw [Complex.ofReal_exp]
    simp
  rw [hfun]
  simp

/-- Literal arbitrary-order Mellin decay.  For every natural `k`, the
scaled `k`th power times the Mellin transform is bounded by one explicit
Schwartz seminorm of the fixed cutoff. -/
theorem scaledPower_mul_norm_mellin_line_one_le_seminorm
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) (r : ℝ) :
    |r / (2 * Real.pi)| ^ k *
        ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (mellinLogLiftSchwartz f
          (mellinLogLift_hasCompactSupport ha hb hsupport)
          (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ)) := by
  rw [mellin_line_one_eq_fourier_logLift]
  let psi : 𝓢(ℝ, ℂ) := mellinLogLiftSchwartz f
    (mellinLogLift_hasCompactSupport ha hb hsupport)
    (mellinLogLift_contDiff hf)
  have hFourier :
      𝓕 (mellinLogLift f) (r / (2 * Real.pi)) =
        ((𝓕 psi : 𝓢(ℝ, ℂ)) (r / (2 * Real.pi))) := by
    exact congrFun (SchwartzMap.fourier_coe psi).symm _
  rw [hFourier]
  have h := SchwartzMap.le_seminorm ℂ k 0
    (𝓕 psi) (r / (2 * Real.pi))
  simpa only [psi, mellinLogLiftSchwartz, norm_iteratedFDeriv_zero,
    Real.norm_eq_abs] using h

/-- Division form of arbitrary-order decay, valid away from `r=0`. -/
theorem norm_mellin_line_one_le_seminorm_div_scaledPower
    {a b : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) {r : ℝ} (hr : r ≠ 0) :
    ‖mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (𝓕 (mellinLogLiftSchwartz f
          (mellinLogLift_hasCompactSupport ha hb hsupport)
          (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ)) /
        |r / (2 * Real.pi)| ^ k := by
  apply (le_div_iff₀ (by positivity : 0 < |r / (2 * Real.pi)| ^ k)).2
  simpa [mul_comm] using
    (scaledPower_mul_norm_mellin_line_one_le_seminorm
      ha hb hsupport hf k r)

/-- Exact positive Mellin-tail estimate of arbitrary order.  Choosing `k`
large makes a subpower truncation radius produce any prescribed fixed power
saving, which is the quantitative content of the `O(T⁻¹⁰⁰)` truncation in
Guth--Maynard Lemma 6.2. -/
theorem norm_integral_Ioi_mellin_line_one_le
    {a b R : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    let S := SchwartzMap.seminorm ℂ k 0
      (𝓕 (mellinLogLiftSchwartz f
        (mellinLogLift_hasCompactSupport ha hb hsupport)
        (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ))
    ‖∫ r : ℝ in Set.Ioi R,
        mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      ((2 * Real.pi) ^ k * S) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  dsimp
  apply GuthMaynardMellinTail.norm_positiveNatPowerTail_le hk hR
  intro r hr
  have hr0 : r ≠ 0 := ne_of_gt (hR.trans hr)
  have hraw := norm_mellin_line_one_le_seminorm_div_scaledPower
    ha hb hsupport hf k hr0
  apply hraw.trans_eq
  rw [abs_of_pos (div_pos (hR.trans hr) (by positivity))]
  rw [div_pow]
  rw [Real.rpow_neg (hR.trans hr).le, Real.rpow_natCast]
  field_simp [hr0, Real.pi_ne_zero, pow_ne_zero]

/-- Matching negative Mellin tail, obtained by reflection. -/
theorem norm_integral_Iic_mellin_line_one_le
    {a b R : ℝ} {f : ℝ → ℂ}
    (ha : 0 < a) (hb : 0 < b)
    (hsupport : ∀ x, x ∉ Set.Icc a b → f x = 0)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    {k : ℕ} (hk : 2 ≤ k) (hR : 0 < R) :
    let S := SchwartzMap.seminorm ℂ k 0
      (𝓕 (mellinLogLiftSchwartz f
        (mellinLogLift_hasCompactSupport ha hb hsupport)
        (mellinLogLift_contDiff hf)) : 𝓢(ℝ, ℂ))
    ‖∫ r : ℝ in Set.Iic (-R),
        mellin f ((1 : ℂ) + r * Complex.I)‖ ≤
      ((2 * Real.pi) ^ k * S) *
        (R ^ (1 - (k : ℝ)) / ((k : ℝ) - 1)) := by
  dsimp
  rw [← integral_comp_neg_Ioi]
  apply GuthMaynardMellinTail.norm_positiveNatPowerTail_le hk hR
  intro r hr
  have hr0 : -r ≠ 0 := neg_ne_zero.mpr (ne_of_gt (hR.trans hr))
  have hraw := norm_mellin_line_one_le_seminorm_div_scaledPower
    ha hb hsupport hf k hr0
  apply hraw.trans_eq
  rw [abs_div, abs_neg, abs_of_pos (hR.trans hr),
    abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [div_pow]
  rw [Real.rpow_neg (hR.trans hr).le, Real.rpow_natCast]
  field_simp [ne_of_gt (hR.trans hr), Real.pi_ne_zero, pow_ne_zero]

end

end GuthMaynardMellinRapidDecay

#print axioms GuthMaynardMellinRapidDecay.mellinLogLift_contDiff
#print axioms GuthMaynardMellinRapidDecay.mellinLogLift_hasCompactSupport
#print axioms GuthMaynardMellinRapidDecay.mellin_line_one_eq_fourier_logLift
#print axioms GuthMaynardMellinRapidDecay.scaledPower_mul_norm_mellin_line_one_le_seminorm
#print axioms GuthMaynardMellinRapidDecay.norm_mellin_line_one_le_seminorm_div_scaledPower
#print axioms GuthMaynardMellinRapidDecay.norm_integral_Ioi_mellin_line_one_le
#print axioms GuthMaynardMellinRapidDecay.norm_integral_Iic_mellin_line_one_le
