import GuthMaynardMellinRapidDecay
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier integration by parts in Guth--Maynard Lemma 4.3

This file certifies the arbitrary-order Fourier integration-by-parts step in
Lemma 4.3 for an arbitrary Schwartz function.  Consequently, for the literal
`h_t(u)=w(u)^2 u^{it}`, the only remaining work in part (1) of Lemma 4.3 is
the finite calculus estimate on the `L¹` norm of its `j`th derivative.
-/

namespace GuthMaynardLemma43FourierIBP

open Real Complex Set MeasureTheory
open scoped FourierTransform SchwartzMap

noncomputable section

def schwartzIteratedDerivative (n : ℕ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (SchwartzMap.derivCLM ℂ ℂ)^[n] f

theorem schwartzIteratedDerivative_apply
    (n : ℕ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    schwartzIteratedDerivative n f x =
      iteratedDeriv n (fun y : ℝ => f y) x := by
  induction n generalizing x with
  | zero => simp [schwartzIteratedDerivative]
  | succ n ih =>
      rw [schwartzIteratedDerivative, Function.iterate_succ_apply']
      rw [SchwartzMap.derivCLM_apply]
      rw [iteratedDeriv_succ]
      congr 1
      funext y
      exact ih y

/-- Exact arbitrary-order Fourier IBP estimate, with mathlib's `2π`
normalization retained internally.  Since `2π ≥ 1`, the displayed source
bound has no extra loss. -/
theorem absPow_mul_norm_fourier_le_integral_iteratedDerivative
    (f : 𝓢(ℝ, ℂ)) (q : ℕ) (xi : ℝ) :
    |xi| ^ q * ‖(𝓕 f : 𝓢(ℝ, ℂ)) xi‖ ≤
      ∫ x : ℝ, ‖iteratedDeriv q (fun y : ℝ => f y) x‖ := by
  have hInt : ∀ m : ℕ, (m : ℕ∞) ≤ ⊤ →
      Integrable (iteratedDeriv m (fun x : ℝ => f x)) := by
    intro m hm
    have h := (schwartzIteratedDerivative m f).integrable
      (μ := (volume : Measure ℝ))
    apply h.congr
    filter_upwards with x
    exact schwartzIteratedDerivative_apply m f x
  have hfourier := Real.fourier_iteratedDeriv
    (f.smooth ⊤) hInt (show (q : ℕ∞) ≤ ⊤ from le_top)
  have hraw := VectorFourier.norm_fourierIntegral_le_integral_norm
    𝐞 volume (innerₗ ℝ)
      (iteratedDeriv q (fun x : ℝ => f x)) xi
  change ‖𝓕 (iteratedDeriv q (fun x : ℝ => f x)) xi‖ ≤ _ at hraw
  rw [congrFun hfourier xi] at hraw
  have hfFourier :
      𝓕 (fun x : ℝ => f x) xi = ((𝓕 f : 𝓢(ℝ, ℂ)) xi) :=
    congrFun (SchwartzMap.fourier_coe f).symm xi
  rw [hfFourier] at hraw
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by
    nlinarith [Real.pi_gt_three]
  have hscale : (1 : ℝ) ≤ (2 * Real.pi) ^ q := one_le_pow₀ htwoPi
  have hnormScale :
      ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) •
          ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ =
        (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by
    change ‖((2 * (Real.pi : ℂ) * Complex.I * (xi : ℂ)) ^ q) *
      ((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ = _
    rw [norm_mul, norm_pow]
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_eq_abs]
    rw [abs_of_pos Real.pi_pos]
    have hnormTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
    rw [hnormTwo]
    ring
  rw [hnormScale] at hraw
  calc
    |xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ ≤
        (2 * Real.pi) ^ q *
          (|xi| ^ q * ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖) :=
      le_mul_of_one_le_left (by positivity) hscale
    _ = (2 * Real.pi) ^ q * |xi| ^ q *
          ‖((𝓕 f : 𝓢(ℝ, ℂ)) xi)‖ := by ring
    _ ≤ _ := hraw

theorem norm_fourier_le_derivativeBudget_div_absPow
    (f : 𝓢(ℝ, ℂ)) (q : ℕ) {xi A : ℝ} (hxi : xi ≠ 0)
    (hbudget :
      (∫ x : ℝ, ‖iteratedDeriv q (fun y : ℝ => f y) x‖) ≤ A) :
    ‖(𝓕 f : 𝓢(ℝ, ℂ)) xi‖ ≤ A / |xi| ^ q := by
  apply (le_div_iff₀ (by positivity : 0 < |xi| ^ q)).2
  simpa [mul_comm] using
    (absPow_mul_norm_fourier_le_integral_iteratedDerivative f q xi).trans
      hbudget

end

end GuthMaynardLemma43FourierIBP

#print axioms GuthMaynardLemma43FourierIBP.schwartzIteratedDerivative_apply
#print axioms GuthMaynardLemma43FourierIBP.absPow_mul_norm_fourier_le_integral_iteratedDerivative
#print axioms GuthMaynardLemma43FourierIBP.norm_fourier_le_derivativeBudget_div_absPow
